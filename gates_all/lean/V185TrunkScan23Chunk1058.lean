import V185TrunkScan23Chunk1057

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_6263631 : List Nat := [1, 1, 2, 1, 1, 2, 1, 1, 3, 6, 4]
def baseStart_6263631 : Nat := 118140960795 + 6263631 * 2 ^ 59
def prefixEnd_6263631 : Nat := 4983230072969 + 3 ^ 40 * 6263631 * 2
def baseEnd_6263631 : Nat := 3216253345402088248606591

theorem tailTrace_6263631 : CollatzResearch.WordTrace tailWord_6263631 prefixEnd_6263631 3216253345402088248606591 := by
  unfold tailWord_6263631
  simp only [CollatzResearch.WordTrace]
  refine ⟨228453390770942104853318747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152302260513961403235545831 228453390770942104853318747)
  ·
    refine ⟨342680086156413157279978121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 228453390770942104853318747 342680086156413157279978121)
    ·
      refine ⟨257010064617309867959983591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 342680086156413157279978121 257010064617309867959983591)
      ·
        refine ⟨385515096925964801939975387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 257010064617309867959983591 385515096925964801939975387)
        ·
          refine ⟨578272645388947202909963081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 385515096925964801939975387 578272645388947202909963081)
          ·
            refine ⟨433704484041710402182472311, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 578272645388947202909963081 433704484041710402182472311)
            ·
              refine ⟨650556726062565603273708467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 433704484041710402182472311 650556726062565603273708467)
              ·
                refine ⟨975835089093848404910562701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 650556726062565603273708467 975835089093848404910562701)
                ·
                  refine ⟨365938158410193151841461013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 975835089093848404910562701 365938158410193151841461013)
                  ·
                    refine ⟨17153351175477803992568485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 365938158410193151841461013 17153351175477803992568485)
                    ·
                      refine ⟨3216253345402088248606591, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17153351175477803992568485 3216253345402088248606591)
                      ·
                        rfl

theorem cell23_6263631_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 1, 3, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 1, 3, 6, 4].length) (baseStart_6263631 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6263631 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6263631 prefixEnd_6263631 := by exact prefixLift 6263631
  have htrace : WordTrace (prefixWord ++ tailWord_6263631) baseStart_6263631 baseEnd_6263631 := by
    simpa [prefixWord, tailWord_6263631, baseEnd_6263631] using wordTrace_append hprefix tailTrace_6263631
  have hstable : (prefixWord ++ tailWord_6263631).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6263631).length < 2 ^ (prefixWord ++ tailWord_6263631).sum := by decide
  have hdescent : baseEnd_6263631 < baseStart_6263631 := by decide
  rcases family_descends (prefixWord ++ tailWord_6263631) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6263671 : List Nat := [1, 1, 3, 1, 1, 2, 1, 2, 2, 9]
def baseStart_6263671 : Nat := 118140960795 + 6263671 * 2 ^ 59
def prefixEnd_6263671 : Nat := 4983230072969 + 3 ^ 40 * 6263671 * 2
def baseEnd_6263671 : Nat := 1072091294876089364035469

theorem tailTrace_6263671 : CollatzResearch.WordTrace tailWord_6263671 prefixEnd_6263671 1072091294876089364035469 := by
  unfold tailWord_6263671
  simp only [CollatzResearch.WordTrace]
  refine ⟨228454849690797191684774867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152303233127198127789849911 228454849690797191684774867)
  ·
    refine ⟨342682274536195787527162301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 228454849690797191684774867 342682274536195787527162301)
    ·
      refine ⟨128505852951073420322685863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 342682274536195787527162301 128505852951073420322685863)
      ·
        refine ⟨192758779426610130484028795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 128505852951073420322685863 192758779426610130484028795)
        ·
          refine ⟨289138169139915195726043193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 192758779426610130484028795 289138169139915195726043193)
          ·
            refine ⟨216853626854936396794532395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 289138169139915195726043193 216853626854936396794532395)
            ·
              refine ⟨325280440282404595191798593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 216853626854936396794532395 325280440282404595191798593)
              ·
                refine ⟨243960330211803446393848945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 325280440282404595191798593 243960330211803446393848945)
                ·
                  refine ⟨182970247658852584795386709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 243960330211803446393848945 182970247658852584795386709)
                  ·
                    refine ⟨1072091294876089364035469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 182970247658852584795386709 1072091294876089364035469)
                    ·
                      rfl

theorem cell23_6263671_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 1, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 1, 2, 2, 9].length) (baseStart_6263671 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6263671 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6263671 prefixEnd_6263671 := by exact prefixLift 6263671
  have htrace : WordTrace (prefixWord ++ tailWord_6263671) baseStart_6263671 baseEnd_6263671 := by
    simpa [prefixWord, tailWord_6263671, baseEnd_6263671] using wordTrace_append hprefix tailTrace_6263671
  have hstable : (prefixWord ++ tailWord_6263671).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6263671).length < 2 ^ (prefixWord ++ tailWord_6263671).sum := by decide
  have hdescent : baseEnd_6263671 < baseStart_6263671 := by decide
  rcases family_descends (prefixWord ++ tailWord_6263671) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6263729 : List Nat := [1, 2, 2, 4, 3, 1, 2, 1, 2, 3, 2]
def baseStart_6263729 : Nat := 118140960795 + 6263729 * 2 ^ 59
def prefixEnd_6263729 : Nat := 4983230072969 + 3 ^ 40 * 6263729 * 2
def baseEnd_6263729 : Nat := 3216303666506228865181141

theorem tailTrace_6263729 : CollatzResearch.WordTrace tailWord_6263729 prefixEnd_6263729 3216303666506228865181141 := by
  unfold tailWord_6263729
  simp only [CollatzResearch.WordTrace]
  refine ⟨228456965124587067590386241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152304643416391378393590827 228456965124587067590386241)
  ·
    refine ⟨171342723843440300692789681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 228456965124587067590386241 171342723843440300692789681)
    ·
      refine ⟨128507042882580225519592261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 171342723843440300692789681 128507042882580225519592261)
      ·
        refine ⟨24095070540483792284923549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 128507042882580225519592261 24095070540483792284923549)
        ·
          refine ⟨9035651452681422106846331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24095070540483792284923549 9035651452681422106846331)
          ·
            refine ⟨13553477179022133160269497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9035651452681422106846331 13553477179022133160269497)
            ·
              refine ⟨10165107884266599870202123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13553477179022133160269497 10165107884266599870202123)
              ·
                refine ⟨15247661826399899805303185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10165107884266599870202123 15247661826399899805303185)
                ·
                  refine ⟨11435746369799924853977389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15247661826399899805303185 11435746369799924853977389)
                  ·
                    refine ⟨4288404888674971820241521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11435746369799924853977389 4288404888674971820241521)
                    ·
                      refine ⟨3216303666506228865181141, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4288404888674971820241521 3216303666506228865181141)
                      ·
                        rfl

theorem cell23_6263729_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 3, 1, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 3, 1, 2, 1, 2, 3, 2].length) (baseStart_6263729 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6263729 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6263729 prefixEnd_6263729 := by exact prefixLift 6263729
  have htrace : WordTrace (prefixWord ++ tailWord_6263729) baseStart_6263729 baseEnd_6263729 := by
    simpa [prefixWord, tailWord_6263729, baseEnd_6263729] using wordTrace_append hprefix tailTrace_6263729
  have hstable : (prefixWord ++ tailWord_6263729).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6263729).length < 2 ^ (prefixWord ++ tailWord_6263729).sum := by decide
  have hdescent : baseEnd_6263729 < baseStart_6263729 := by decide
  rcases family_descends (prefixWord ++ tailWord_6263729) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6263762 : List Nat := [3, 2, 2, 3, 1, 1, 1, 2, 3, 2, 3]
def baseStart_6263762 : Nat := 118140960795 + 6263762 * 2 ^ 59
def prefixEnd_6263762 : Nat := 4983230072969 + 3 ^ 40 * 6263762 * 2
def baseEnd_6263762 : Nat := 3216320611367827236068489

theorem tailTrace_6263762 : CollatzResearch.WordTrace tailWord_6263762 prefixEnd_6263762 3216320611367827236068489 := by
  unfold tailWord_6263762
  simp only [CollatzResearch.WordTrace]
  refine ⟨57114542183366878556584385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 152305445822311676150891693 57114542183366878556584385)
  ·
    refine ⟨42835906637525158917438289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57114542183366878556584385 42835906637525158917438289)
    ·
      refine ⟨32126929978143869188078717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42835906637525158917438289 32126929978143869188078717)
      ·
        refine ⟨12047598741803950945529519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 32126929978143869188078717 12047598741803950945529519)
        ·
          refine ⟨18071398112705926418294279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12047598741803950945529519 18071398112705926418294279)
          ·
            refine ⟨27107097169058889627441419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18071398112705926418294279 27107097169058889627441419)
            ·
              refine ⟨40660645753588334441162129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27107097169058889627441419 40660645753588334441162129)
              ·
                refine ⟨30495484315191250830871597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 40660645753588334441162129 30495484315191250830871597)
                ·
                  refine ⟨11435806618196719061576849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 30495484315191250830871597 11435806618196719061576849)
                  ·
                    refine ⟨8576854963647539296182637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11435806618196719061576849 8576854963647539296182637)
                    ·
                      refine ⟨3216320611367827236068489, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8576854963647539296182637 3216320611367827236068489)
                      ·
                        rfl

theorem cell23_6263762_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 1, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 1, 1, 2, 3, 2, 3].length) (baseStart_6263762 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6263762 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6263762 prefixEnd_6263762 := by exact prefixLift 6263762
  have htrace : WordTrace (prefixWord ++ tailWord_6263762) baseStart_6263762 baseEnd_6263762 := by
    simpa [prefixWord, tailWord_6263762, baseEnd_6263762] using wordTrace_append hprefix tailTrace_6263762
  have hstable : (prefixWord ++ tailWord_6263762).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6263762).length < 2 ^ (prefixWord ++ tailWord_6263762).sum := by decide
  have hdescent : baseEnd_6263762 < baseStart_6263762 := by decide
  rcases family_descends (prefixWord ++ tailWord_6263762) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6263809 : List Nat := [1, 2, 4, 1, 2, 2, 3, 2, 2, 1, 3]
def baseStart_6263809 : Nat := 118140960795 + 6263809 * 2 ^ 59
def prefixEnd_6263809 : Nat := 4983230072969 + 3 ^ 40 * 6263809 * 2
def baseEnd_6263809 : Nat := 3216344744958588552180773

theorem tailTrace_6263809 : CollatzResearch.WordTrace tailWord_6263809 prefixEnd_6263809 3216344744958588552180773 := by
  unfold tailWord_6263809
  simp only [CollatzResearch.WordTrace]
  refine ⟨228459882964297241253298481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152306588642864827502198987 228459882964297241253298481)
  ·
    refine ⟨171344912223222930939973861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 228459882964297241253298481 171344912223222930939973861)
    ·
      refine ⟨32127171041854299551245099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 171344912223222930939973861 32127171041854299551245099)
      ·
        refine ⟨48190756562781449326867649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32127171041854299551245099 48190756562781449326867649)
        ·
          refine ⟨36143067422086086995150737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48190756562781449326867649 36143067422086086995150737)
          ·
            refine ⟨27107300566564565246363053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36143067422086086995150737 27107300566564565246363053)
            ·
              refine ⟨10165237712461711967386145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27107300566564565246363053 10165237712461711967386145)
              ·
                refine ⟨7623928284346283975539609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10165237712461711967386145 7623928284346283975539609)
                ·
                  refine ⟨5717946213259712981654707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7623928284346283975539609 5717946213259712981654707)
                  ·
                    refine ⟨8576919319889569472482061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5717946213259712981654707 8576919319889569472482061)
                    ·
                      refine ⟨3216344744958588552180773, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8576919319889569472482061 3216344744958588552180773)
                      ·
                        rfl

theorem cell23_6263809_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 2, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 2, 3, 2, 2, 1, 3].length) (baseStart_6263809 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6263809 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6263809 prefixEnd_6263809 := by exact prefixLift 6263809
  have htrace : WordTrace (prefixWord ++ tailWord_6263809) baseStart_6263809 baseEnd_6263809 := by
    simpa [prefixWord, tailWord_6263809, baseEnd_6263809] using wordTrace_append hprefix tailTrace_6263809
  have hstable : (prefixWord ++ tailWord_6263809).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6263809).length < 2 ^ (prefixWord ++ tailWord_6263809).sum := by decide
  have hdescent : baseEnd_6263809 < baseStart_6263809 := by decide
  rcases family_descends (prefixWord ++ tailWord_6263809) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6263836 : List Nat := [2, 2, 3, 1, 4, 1, 2, 2, 1, 3, 2]
def baseStart_6263836 : Nat := 118140960795 + 6263836 * 2 ^ 59
def prefixEnd_6263836 : Nat := 4983230072969 + 3 ^ 40 * 6263836 * 2
def baseEnd_6263836 : Nat := 3216358608936259946543149

theorem tailTrace_6263836 : CollatzResearch.WordTrace tailWord_6263836 prefixEnd_6263836 3216358608936259946543149 := by
  unfold tailWord_6263836
  simp only [CollatzResearch.WordTrace]
  refine ⟨114230433867599712432265681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 152307245156799616576354241 114230433867599712432265681)
  ·
    refine ⟨85672825400699784324199261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 114230433867599712432265681 85672825400699784324199261)
    ·
      refine ⟨32127309525262419121574723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 85672825400699784324199261 32127309525262419121574723)
      ·
        refine ⟨48190964287893628682362085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32127309525262419121574723 48190964287893628682362085)
        ·
          refine ⟨9035805803980055377942891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 48190964287893628682362085 9035805803980055377942891)
          ·
            refine ⟨13553708705970083066914337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9035805803980055377942891 13553708705970083066914337)
            ·
              refine ⟨10165281529477562300185753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13553708705970083066914337 10165281529477562300185753)
              ·
                refine ⟨7623961147108171725139315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10165281529477562300185753 7623961147108171725139315)
                ·
                  refine ⟨11435941720662257587708973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7623961147108171725139315 11435941720662257587708973)
                  ·
                    refine ⟨4288478145248346595390865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11435941720662257587708973 4288478145248346595390865)
                    ·
                      refine ⟨3216358608936259946543149, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4288478145248346595390865 3216358608936259946543149)
                      ·
                        rfl

theorem cell23_6263836_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 4, 1, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 4, 1, 2, 2, 1, 3, 2].length) (baseStart_6263836 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6263836 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6263836 prefixEnd_6263836 := by exact prefixLift 6263836
  have htrace : WordTrace (prefixWord ++ tailWord_6263836) baseStart_6263836 baseEnd_6263836 := by
    simpa [prefixWord, tailWord_6263836, baseEnd_6263836] using wordTrace_append hprefix tailTrace_6263836
  have hstable : (prefixWord ++ tailWord_6263836).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6263836).length < 2 ^ (prefixWord ++ tailWord_6263836).sum := by decide
  have hdescent : baseEnd_6263836 < baseStart_6263836 := by decide
  rcases family_descends (prefixWord ++ tailWord_6263836) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6263905 : List Nat := [1, 2, 3, 1, 1, 2, 2, 3, 1, 3, 4]
def baseStart_6263905 : Nat := 118140960795 + 6263905 * 2 ^ 59
def prefixEnd_6263905 : Nat := 4983230072969 + 3 ^ 40 * 6263905 * 2
def baseEnd_6263905 : Nat := 3216394039101420176580331

theorem tailTrace_6263905 : CollatzResearch.WordTrace tailWord_6263905 prefixEnd_6263905 3216394039101420176580331 := by
  unfold tailWord_6263905
  simp only [CollatzResearch.WordTrace]
  refine ⟨228463384371949449648793169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152308922914632966432528779 228463384371949449648793169)
  ·
    refine ⟨171347538278962087236594877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 228463384371949449648793169 171347538278962087236594877)
    ·
      refine ⟨64255326854610782713723079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 171347538278962087236594877 64255326854610782713723079)
      ·
        refine ⟨96382990281916174070584619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64255326854610782713723079 96382990281916174070584619)
        ·
          refine ⟨144574485422874261105876929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 96382990281916174070584619 144574485422874261105876929)
          ·
            refine ⟨108430864067155695829407697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 144574485422874261105876929 108430864067155695829407697)
            ·
              refine ⟨81323148050366771872055773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 108430864067155695829407697 81323148050366771872055773)
              ·
                refine ⟨30496180518887539452020915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 81323148050366771872055773 30496180518887539452020915)
                ·
                  refine ⟨45744270778331309178031373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30496180518887539452020915 45744270778331309178031373)
                  ·
                    refine ⟨17154101541874240941761765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 45744270778331309178031373 17154101541874240941761765)
                    ·
                      refine ⟨3216394039101420176580331, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17154101541874240941761765 3216394039101420176580331)
                      ·
                        rfl

theorem cell23_6263905_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 2, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 2, 3, 1, 3, 4].length) (baseStart_6263905 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6263905 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6263905 prefixEnd_6263905 := by exact prefixLift 6263905
  have htrace : WordTrace (prefixWord ++ tailWord_6263905) baseStart_6263905 baseEnd_6263905 := by
    simpa [prefixWord, tailWord_6263905, baseEnd_6263905] using wordTrace_append hprefix tailTrace_6263905
  have hstable : (prefixWord ++ tailWord_6263905).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6263905).length < 2 ^ (prefixWord ++ tailWord_6263905).sum := by decide
  have hdescent : baseEnd_6263905 < baseStart_6263905 := by decide
  rcases family_descends (prefixWord ++ tailWord_6263905) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6263922 : List Nat := [3, 2, 1, 2, 2, 1, 1, 4, 2, 1, 4]
def baseStart_6263922 : Nat := 118140960795 + 6263922 * 2 ^ 59
def prefixEnd_6263922 : Nat := 4983230072969 + 3 ^ 40 * 6263922 * 2
def baseEnd_6263922 : Nat := 3216402768272546610067753

theorem tailTrace_6263922 : CollatzResearch.WordTrace tailWord_6263922 prefixEnd_6263922 3216402768272546610067753 := by
  unfold tailWord_6263922
  simp only [CollatzResearch.WordTrace]
  refine ⟨57116001103221965388040505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 152309336275258574368108013 57116001103221965388040505)
  ·
    refine ⟨42837000827416474041030379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57116001103221965388040505 42837000827416474041030379)
    ·
      refine ⟨64255501241124711061545569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42837000827416474041030379 64255501241124711061545569)
      ·
        refine ⟨48191625930843533296159177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 64255501241124711061545569 48191625930843533296159177)
        ·
          refine ⟨36143719448132649972119383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48191625930843533296159177 36143719448132649972119383)
          ·
            refine ⟨54215579172198974958179075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36143719448132649972119383 54215579172198974958179075)
            ·
              refine ⟨81323368758298462437268613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 54215579172198974958179075 81323368758298462437268613)
              ·
                refine ⟨15248131642180961706987865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 81323368758298462437268613 15248131642180961706987865)
                ·
                  refine ⟨11436098731635721280240899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15248131642180961706987865 11436098731635721280240899)
                  ·
                    refine ⟨17154148097453581920361349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11436098731635721280240899 17154148097453581920361349)
                    ·
                      refine ⟨3216402768272546610067753, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17154148097453581920361349 3216402768272546610067753)
                      ·
                        rfl

theorem cell23_6263922_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 1, 4, 2, 1, 4].length) (baseStart_6263922 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6263922 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6263922 prefixEnd_6263922 := by exact prefixLift 6263922
  have htrace : WordTrace (prefixWord ++ tailWord_6263922) baseStart_6263922 baseEnd_6263922 := by
    simpa [prefixWord, tailWord_6263922, baseEnd_6263922] using wordTrace_append hprefix tailTrace_6263922
  have hstable : (prefixWord ++ tailWord_6263922).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6263922).length < 2 ^ (prefixWord ++ tailWord_6263922).sum := by decide
  have hdescent : baseEnd_6263922 < baseStart_6263922 := by decide
  rcases family_descends (prefixWord ++ tailWord_6263922) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6263932 : List Nat := [2, 2, 2, 1, 1, 3, 2, 3, 3, 4]
def baseStart_6263932 : Nat := 118140960795 + 6263932 * 2 ^ 59
def prefixEnd_6263932 : Nat := 4983230072969 + 3 ^ 40 * 6263932 * 2
def baseEnd_6263932 : Nat := 1072135967693030523647569

theorem tailTrace_6263932 : CollatzResearch.WordTrace tailWord_6263932 prefixEnd_6263932 1072135967693030523647569 := by
  unfold tailWord_6263932
  simp only [CollatzResearch.WordTrace]
  refine ⟨114232184571425816630013025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 152309579428567755506684033 114232184571425816630013025)
  ·
    refine ⟨85674138428569362472509769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 114232184571425816630013025 85674138428569362472509769)
    ·
      refine ⟨64255603821427021854382327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 85674138428569362472509769 64255603821427021854382327)
      ·
        refine ⟨96383405732140532781573491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64255603821427021854382327 96383405732140532781573491)
        ·
          refine ⟨144575108598210799172360237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 96383405732140532781573491 144575108598210799172360237)
          ·
            refine ⟨54215665724329049689635089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 144575108598210799172360237 54215665724329049689635089)
            ·
              refine ⟨40661749293246787267226317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 54215665724329049689635089 40661749293246787267226317)
              ·
                refine ⟨15248155984967545225209869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 40661749293246787267226317 15248155984967545225209869)
                ·
                  refine ⟨5718058494362829459453701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15248155984967545225209869 5718058494362829459453701)
                  ·
                    refine ⟨1072135967693030523647569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5718058494362829459453701 1072135967693030523647569)
                    ·
                      rfl

theorem cell23_6263932_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 2, 3, 3, 4].length) (baseStart_6263932 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6263932 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6263932 prefixEnd_6263932 := by exact prefixLift 6263932
  have htrace : WordTrace (prefixWord ++ tailWord_6263932) baseStart_6263932 baseEnd_6263932 := by
    simpa [prefixWord, tailWord_6263932, baseEnd_6263932] using wordTrace_append hprefix tailTrace_6263932
  have hstable : (prefixWord ++ tailWord_6263932).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6263932).length < 2 ^ (prefixWord ++ tailWord_6263932).sum := by decide
  have hdescent : baseEnd_6263932 < baseStart_6263932 := by decide
  rcases family_descends (prefixWord ++ tailWord_6263932) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6263959 : List Nat := [1, 1, 3, 3, 3, 1, 3, 1, 2, 2, 3]
def baseStart_6263959 : Nat := 118140960795 + 6263959 * 2 ^ 59
def prefixEnd_6263959 : Nat := 4983230072969 + 3 ^ 40 * 6263959 * 2
def baseEnd_6263959 : Nat := 3216421767056762965305083

theorem tailTrace_6263959 : CollatzResearch.WordTrace tailWord_6263959 prefixEnd_6263959 3216421767056762965305083 := by
  unfold tailWord_6263959
  simp only [CollatzResearch.WordTrace]
  refine ⟨228465353913753816871258931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152310235942502544580839287 228465353913753816871258931)
  ·
    refine ⟨342698030870630725306888397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 228465353913753816871258931 342698030870630725306888397)
    ·
      refine ⟨128511761576486521990083149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 342698030870630725306888397 128511761576486521990083149)
      ·
        refine ⟨48191910591182445746281181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 128511761576486521990083149 48191910591182445746281181)
        ·
          refine ⟨18071966471693417154855443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 48191910591182445746281181 18071966471693417154855443)
          ·
            refine ⟨27107949707540125732283165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18071966471693417154855443 27107949707540125732283165)
            ·
              refine ⟨10165481140327547149606187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27107949707540125732283165 10165481140327547149606187)
              ·
                refine ⟨15248221710491320724409281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10165481140327547149606187 15248221710491320724409281)
                ·
                  refine ⟨11436166282868490543306961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15248221710491320724409281 11436166282868490543306961)
                  ·
                    refine ⟨8577124712151367907480221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11436166282868490543306961 8577124712151367907480221)
                    ·
                      refine ⟨3216421767056762965305083, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8577124712151367907480221 3216421767056762965305083)
                      ·
                        rfl

theorem cell23_6263959_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 1, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 1, 3, 1, 2, 2, 3].length) (baseStart_6263959 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6263959 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6263959 prefixEnd_6263959 := by exact prefixLift 6263959
  have htrace : WordTrace (prefixWord ++ tailWord_6263959) baseStart_6263959 baseEnd_6263959 := by
    simpa [prefixWord, tailWord_6263959, baseEnd_6263959] using wordTrace_append hprefix tailTrace_6263959
  have hstable : (prefixWord ++ tailWord_6263959).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6263959).length < 2 ^ (prefixWord ++ tailWord_6263959).sum := by decide
  have hdescent : baseEnd_6263959 < baseStart_6263959 := by decide
  rcases family_descends (prefixWord ++ tailWord_6263959) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6263995 : List Nat := [1, 1, 1, 1, 1, 2, 4, 1, 2, 5, 4]
def baseStart_6263995 : Nat := 118140960795 + 6263995 * 2 ^ 59
def prefixEnd_6263995 : Nat := 4983230072969 + 3 ^ 40 * 6263995 * 2
def baseEnd_6263995 : Nat := 3216440252360324824454917

theorem tailTrace_6263995 : CollatzResearch.WordTrace tailWord_6263995 prefixEnd_6263995 3216440252360324824454917 := by
  unfold tailWord_6263995
  simp only [CollatzResearch.WordTrace]
  refine ⟨228466666941623395019569439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152311111294415596679712959 228466666941623395019569439)
  ·
    refine ⟨342700000412435092529354159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 228466666941623395019569439 342700000412435092529354159)
    ·
      refine ⟨514050000618652638794031239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 342700000412435092529354159 514050000618652638794031239)
      ·
        refine ⟨771075000927978958191046859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 514050000618652638794031239 771075000927978958191046859)
        ·
          refine ⟨1156612501391968437286570289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 771075000927978958191046859 1156612501391968437286570289)
          ·
            refine ⟨867459376043976327964927717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1156612501391968437286570289 867459376043976327964927717)
            ·
              refine ⟨162648633008245561493423947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 867459376043976327964927717 162648633008245561493423947)
              ·
                refine ⟨243972949512368342240135921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 162648633008245561493423947 243972949512368342240135921)
                ·
                  refine ⟨182979712134276256680101941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 243972949512368342240135921 182979712134276256680101941)
                  ·
                    refine ⟨17154348012588399063759557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 182979712134276256680101941 17154348012588399063759557)
                    ·
                      refine ⟨3216440252360324824454917, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17154348012588399063759557 3216440252360324824454917)
                      ·
                        rfl

theorem cell23_6263995_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 4, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 4, 1, 2, 5, 4].length) (baseStart_6263995 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6263995 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6263995 prefixEnd_6263995 := by exact prefixLift 6263995
  have htrace : WordTrace (prefixWord ++ tailWord_6263995) baseStart_6263995 baseEnd_6263995 := by
    simpa [prefixWord, tailWord_6263995, baseEnd_6263995] using wordTrace_append hprefix tailTrace_6263995
  have hstable : (prefixWord ++ tailWord_6263995).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6263995).length < 2 ^ (prefixWord ++ tailWord_6263995).sum := by decide
  have hdescent : baseEnd_6263995 < baseStart_6263995 := by decide
  rcases family_descends (prefixWord ++ tailWord_6263995) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6264032 : List Nat := [2, 1, 1, 3, 1, 4, 1, 3, 1, 1, 5]
def baseStart_6264032 : Nat := 118140960795 + 6264032 * 2 ^ 59
def prefixEnd_6264032 : Nat := 4983230072969 + 3 ^ 40 * 6264032 * 2
def baseEnd_6264032 : Nat := 3216459251144541179692247

theorem tailTrace_6264032 : CollatzResearch.WordTrace tailWord_6264032 prefixEnd_6264032 3216459251144541179692247 := by
  unfold tailWord_6264032
  simp only [CollatzResearch.WordTrace]
  refine ⟨114234008221244675169333175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 152312010961659566892444233 114234008221244675169333175)
  ·
    refine ⟨171351012331867012753999763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114234008221244675169333175 171351012331867012753999763)
    ·
      refine ⟨257026518497800519130999645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 171351012331867012753999763 257026518497800519130999645)
      ·
        refine ⟨96384944436675194674124867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 257026518497800519130999645 96384944436675194674124867)
        ·
          refine ⟨144577416655012792011187301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 96384944436675194674124867 144577416655012792011187301)
          ·
            refine ⟨27108265622814898502097619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 144577416655012792011187301 27108265622814898502097619)
            ·
              refine ⟨40662398434222347753146429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27108265622814898502097619 40662398434222347753146429)
              ·
                refine ⟨15248399412833380407429911, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 40662398434222347753146429 15248399412833380407429911)
                ·
                  refine ⟨22872599119250070611144867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15248399412833380407429911 22872599119250070611144867)
                  ·
                    refine ⟨34308898678875105916717301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 22872599119250070611144867 34308898678875105916717301)
                    ·
                      refine ⟨3216459251144541179692247, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 34308898678875105916717301 3216459251144541179692247)
                      ·
                        rfl

theorem cell23_6264032_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 4, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 4, 1, 3, 1, 1, 5].length) (baseStart_6264032 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6264032 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6264032 prefixEnd_6264032 := by exact prefixLift 6264032
  have htrace : WordTrace (prefixWord ++ tailWord_6264032) baseStart_6264032 baseEnd_6264032 := by
    simpa [prefixWord, tailWord_6264032, baseEnd_6264032] using wordTrace_append hprefix tailTrace_6264032
  have hstable : (prefixWord ++ tailWord_6264032).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6264032).length < 2 ^ (prefixWord ++ tailWord_6264032).sum := by decide
  have hdescent : baseEnd_6264032 < baseStart_6264032 := by decide
  rcases family_descends (prefixWord ++ tailWord_6264032) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6264042 : List Nat := [3, 1, 3, 1, 1, 3, 1, 2, 1, 1, 6]
def baseStart_6264042 : Nat := 118140960795 + 6264042 * 2 ^ 59
def prefixEnd_6264042 : Nat := 4983230072969 + 3 ^ 40 * 6264042 * 2
def baseEnd_6264042 : Nat := 3216464385951086140567201

theorem tailTrace_6264042 : CollatzResearch.WordTrace tailWord_6264042 prefixEnd_6264042 3216464385951086140567201 := by
  unfold tailWord_6264042
  simp only [CollatzResearch.WordTrace]
  refine ⟨57117095293113280511632595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 152312254114968748031020253 57117095293113280511632595)
  ·
    refine ⟨85675642939669920767448893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57117095293113280511632595 85675642939669920767448893)
    ·
      refine ⟨32128366102376220287793335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 85675642939669920767448893 32128366102376220287793335)
      ·
        refine ⟨48192549153564330431690003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32128366102376220287793335 48192549153564330431690003)
        ·
          refine ⟨72288823730346495647535005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48192549153564330431690003 72288823730346495647535005)
          ·
            refine ⟨27108308898879935867825627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 72288823730346495647535005 27108308898879935867825627)
            ·
              refine ⟨40662463348319903801738441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27108308898879935867825627 40662463348319903801738441)
              ·
                refine ⟨30496847511239927851303831, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 40662463348319903801738441 30496847511239927851303831)
                ·
                  refine ⟨45745271266859891776955747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30496847511239927851303831 45745271266859891776955747)
                  ·
                    refine ⟨68617906900289837665433621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 45745271266859891776955747 68617906900289837665433621)
                    ·
                      refine ⟨3216464385951086140567201, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 68617906900289837665433621 3216464385951086140567201)
                      ·
                        rfl

theorem cell23_6264042_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 3, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 3, 1, 2, 1, 1, 6].length) (baseStart_6264042 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6264042 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6264042 prefixEnd_6264042 := by exact prefixLift 6264042
  have htrace : WordTrace (prefixWord ++ tailWord_6264042) baseStart_6264042 baseEnd_6264042 := by
    simpa [prefixWord, tailWord_6264042, baseEnd_6264042] using wordTrace_append hprefix tailTrace_6264042
  have hstable : (prefixWord ++ tailWord_6264042).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6264042).length < 2 ^ (prefixWord ++ tailWord_6264042).sum := by decide
  have hdescent : baseEnd_6264042 < baseStart_6264042 := by decide
  rcases family_descends (prefixWord ++ tailWord_6264042) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6264092 : List Nat := [2, 2, 3, 1, 1, 1, 2, 2, 2, 2, 5]
def baseStart_6264092 : Nat := 118140960795 + 6264092 * 2 ^ 59
def prefixEnd_6264092 : Nat := 4983230072969 + 3 ^ 40 * 6264092 * 2
def baseEnd_6264092 : Nat := 3216490059983810944941971

theorem tailTrace_6264092 : CollatzResearch.WordTrace tailWord_6264092 prefixEnd_6264092 3216490059983810944941971 := by
  unfold tailWord_6264092
  simp only [CollatzResearch.WordTrace]
  refine ⟨114235102411135990292925265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 152313469881514653723900353 114235102411135990292925265)
  ·
    refine ⟨85676326808351992719693949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 114235102411135990292925265 85676326808351992719693949)
    ·
      refine ⟨32128622553131997269885231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 85676326808351992719693949 32128622553131997269885231)
      ·
        refine ⟨48192933829697995904827847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32128622553131997269885231 48192933829697995904827847)
        ·
          refine ⟨72289400744546993857241771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48192933829697995904827847 72289400744546993857241771)
          ·
            refine ⟨108434101116820490785862657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 72289400744546993857241771 108434101116820490785862657)
            ·
              refine ⟨81325575837615368089396993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 108434101116820490785862657 81325575837615368089396993)
              ·
                refine ⟨60994181878211526067047745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 81325575837615368089396993 60994181878211526067047745)
                ·
                  refine ⟨45745636408658644550285809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 60994181878211526067047745 45745636408658644550285809)
                  ·
                    refine ⟨34309227306493983412714357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 45745636408658644550285809 34309227306493983412714357)
                    ·
                      refine ⟨3216490059983810944941971, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 34309227306493983412714357 3216490059983810944941971)
                      ·
                        rfl

theorem cell23_6264092_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 2, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 2, 2, 2, 2, 5].length) (baseStart_6264092 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6264092 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6264092 prefixEnd_6264092 := by exact prefixLift 6264092
  have htrace : WordTrace (prefixWord ++ tailWord_6264092) baseStart_6264092 baseEnd_6264092 := by
    simpa [prefixWord, tailWord_6264092, baseEnd_6264092] using wordTrace_append hprefix tailTrace_6264092
  have hstable : (prefixWord ++ tailWord_6264092).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6264092).length < 2 ^ (prefixWord ++ tailWord_6264092).sum := by decide
  have hdescent : baseEnd_6264092 < baseStart_6264092 := by decide
  rcases family_descends (prefixWord ++ tailWord_6264092) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6264112 : List Nat := [2, 1, 1, 1, 2, 2, 5, 1, 2, 6]
def baseStart_6264112 : Nat := 118140960795 + 6264112 * 2 ^ 59
def prefixEnd_6264112 : Nat := 4983230072969 + 3 ^ 40 * 6264112 * 2
def baseEnd_6264112 : Nat := 1072166776532300288897293

theorem tailTrace_6264112 : CollatzResearch.WordTrace tailWord_6264112 prefixEnd_6264112 1072166776532300288897293 := by
  unfold tailWord_6264112
  simp only [CollatzResearch.WordTrace]
  refine ⟨114235467141099762000789295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 152313956188133016001052393 114235467141099762000789295)
  ·
    refine ⟨171353200711649643001183943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114235467141099762000789295 171353200711649643001183943)
    ·
      refine ⟨257029801067474464501775915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 171353200711649643001183943 257029801067474464501775915)
      ·
        refine ⟨385544701601211696752663873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 257029801067474464501775915 385544701601211696752663873)
        ·
          refine ⟨289158526200908772564497905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 385544701601211696752663873 289158526200908772564497905)
          ·
            refine ⟨216868894650681579423373429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 289158526200908772564497905 216868894650681579423373429)
            ·
              refine ⟨20331458873501398070941259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 216868894650681579423373429 20331458873501398070941259)
              ·
                refine ⟨30497188310252097106411889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20331458873501398070941259 30497188310252097106411889)
                ·
                  refine ⟨22872891232689072829808917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 30497188310252097106411889 22872891232689072829808917)
                  ·
                    refine ⟨1072166776532300288897293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 22872891232689072829808917 1072166776532300288897293)
                    ·
                      rfl

theorem cell23_6264112_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 5, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 5, 1, 2, 6].length) (baseStart_6264112 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6264112 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6264112 prefixEnd_6264112 := by exact prefixLift 6264112
  have htrace : WordTrace (prefixWord ++ tailWord_6264112) baseStart_6264112 baseEnd_6264112 := by
    simpa [prefixWord, tailWord_6264112, baseEnd_6264112] using wordTrace_append hprefix tailTrace_6264112
  have hstable : (prefixWord ++ tailWord_6264112).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6264112).length < 2 ^ (prefixWord ++ tailWord_6264112).sum := by decide
  have hdescent : baseEnd_6264112 < baseStart_6264112 := by decide
  rcases family_descends (prefixWord ++ tailWord_6264112) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6264134 : List Nat := [6, 1, 1, 3, 1, 2, 2, 1, 1, 2, 3]
def baseStart_6264134 : Nat := 118140960795 + 6264134 * 2 ^ 59
def prefixEnd_6264134 : Nat := 4983230072969 + 3 ^ 40 * 6264134 * 2
def baseEnd_6264134 : Nat := 3216511626171299780616779

theorem tailTrace_6264134 : CollatzResearch.WordTrace tailWord_6264134 prefixEnd_6264134 3216511626171299780616779 := by
  unfold tailWord_6264134
  simp only [CollatzResearch.WordTrace]
  refine ⟨7139741771503744429964983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 152314491125413214505919637 7139741771503744429964983)
  ·
    refine ⟨10709612657255616644947475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7139741771503744429964983 10709612657255616644947475)
    ·
      refine ⟨16064418985883424967421213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10709612657255616644947475 16064418985883424967421213)
      ·
        refine ⟨6024157119706284362782955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16064418985883424967421213 6024157119706284362782955)
        ·
          refine ⟨9036235679559426544174433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6024157119706284362782955 9036235679559426544174433)
          ·
            refine ⟨6777176759669569908130825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9036235679559426544174433 6777176759669569908130825)
            ·
              refine ⟨5082882569752177431098119, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6777176759669569908130825 5082882569752177431098119)
              ·
                refine ⟨7624323854628266146647179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5082882569752177431098119 7624323854628266146647179)
                ·
                  refine ⟨11436485781942399219970769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7624323854628266146647179 11436485781942399219970769)
                  ·
                    refine ⟨8577364336456799414978077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11436485781942399219970769 8577364336456799414978077)
                    ·
                      refine ⟨3216511626171299780616779, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8577364336456799414978077 3216511626171299780616779)
                      ·
                        rfl

theorem cell23_6264134_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 3, 1, 2, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 3, 1, 2, 2, 1, 1, 2, 3].length) (baseStart_6264134 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6264134 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6264134 prefixEnd_6264134 := by exact prefixLift 6264134
  have htrace : WordTrace (prefixWord ++ tailWord_6264134) baseStart_6264134 baseEnd_6264134 := by
    simpa [prefixWord, tailWord_6264134, baseEnd_6264134] using wordTrace_append hprefix tailTrace_6264134
  have hstable : (prefixWord ++ tailWord_6264134).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6264134).length < 2 ^ (prefixWord ++ tailWord_6264134).sum := by decide
  have hdescent : baseEnd_6264134 < baseStart_6264134 := by decide
  rcases family_descends (prefixWord ++ tailWord_6264134) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6264136 : List Nat := [2, 1, 3, 1, 1, 2, 1, 4, 4, 2, 2]
def baseStart_6264136 : Nat := 118140960795 + 6264136 * 2 ^ 59
def prefixEnd_6264136 : Nat := 4983230072969 + 3 ^ 40 * 6264136 * 2
def baseEnd_6264136 : Nat := 3216512653132608772791769

theorem tailTrace_6264136 : CollatzResearch.WordTrace tailWord_6264136 prefixEnd_6264136 3216512653132608772791769 := by
  unfold tailWord_6264136
  simp only [CollatzResearch.WordTrace]
  refine ⟨114235904817056288050226131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 152314539756075050733634841 114235904817056288050226131)
  ·
    refine ⟨171353857225584432075339197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114235904817056288050226131 171353857225584432075339197)
    ·
      refine ⟨64257696459594162028252199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 171353857225584432075339197 64257696459594162028252199)
      ·
        refine ⟨96386544689391243042378299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64257696459594162028252199 96386544689391243042378299)
        ·
          refine ⟨144579817034086864563567449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 96386544689391243042378299 144579817034086864563567449)
          ·
            refine ⟨108434862775565148422675587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 144579817034086864563567449 108434862775565148422675587)
            ·
              refine ⟨162652294163347722634013381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 108434862775565148422675587 162652294163347722634013381)
              ·
                refine ⟨30497305155627697993877509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 162652294163347722634013381 30497305155627697993877509)
                ·
                  refine ⟨5718244716680193373852033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 30497305155627697993877509 5718244716680193373852033)
                  ·
                    refine ⟨4288683537510145030389025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5718244716680193373852033 4288683537510145030389025)
                    ·
                      refine ⟨3216512653132608772791769, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4288683537510145030389025 3216512653132608772791769)
                      ·
                        rfl

theorem cell23_6264136_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 1, 4, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 1, 4, 4, 2, 2].length) (baseStart_6264136 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6264136 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6264136 prefixEnd_6264136 := by exact prefixLift 6264136
  have htrace : WordTrace (prefixWord ++ tailWord_6264136) baseStart_6264136 baseEnd_6264136 := by
    simpa [prefixWord, tailWord_6264136, baseEnd_6264136] using wordTrace_append hprefix tailTrace_6264136
  have hstable : (prefixWord ++ tailWord_6264136).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6264136).length < 2 ^ (prefixWord ++ tailWord_6264136).sum := by decide
  have hdescent : baseEnd_6264136 < baseStart_6264136 := by decide
  rcases family_descends (prefixWord ++ tailWord_6264136) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6264140 : List Nat := [2, 2, 1, 3, 2, 4, 2, 1, 1, 3, 2]
def baseStart_6264140 : Nat := 118140960795 + 6264140 * 2 ^ 59
def prefixEnd_6264140 : Nat := 4983230072969 + 3 ^ 40 * 6264140 * 2
def baseEnd_6264140 : Nat := 3216514707055226757141751

theorem tailTrace_6264140 : CollatzResearch.WordTrace tailWord_6264140 prefixEnd_6264140 3216514707055226757141751 := by
  unfold tailWord_6264140
  simp only [CollatzResearch.WordTrace]
  refine ⟨114235977763049042391798937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 152314637017398723189065249 114235977763049042391798937)
  ·
    refine ⟨85676983322286781793849203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 114235977763049042391798937 85676983322286781793849203)
    ·
      refine ⟨128515474983430172690773805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85676983322286781793849203 128515474983430172690773805)
      ·
        refine ⟨48193303118786314759040177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 128515474983430172690773805 48193303118786314759040177)
        ·
          refine ⟨36144977339089736069280133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48193303118786314759040177 36144977339089736069280133)
          ·
            refine ⟨6777183251079325512990025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 36144977339089736069280133 6777183251079325512990025)
            ·
              refine ⟨5082887438309494134742519, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6777183251079325512990025 5082887438309494134742519)
              ·
                refine ⟨7624331157464241202113779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5082887438309494134742519 7624331157464241202113779)
                ·
                  refine ⟨11436496736196361803170669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7624331157464241202113779 11436496736196361803170669)
                  ·
                    refine ⟨4288686276073635676189001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11436496736196361803170669 4288686276073635676189001)
                    ·
                      refine ⟨3216514707055226757141751, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4288686276073635676189001 3216514707055226757141751)
                      ·
                        rfl

theorem cell23_6264140_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 4, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 4, 2, 1, 1, 3, 2].length) (baseStart_6264140 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6264140 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6264140 prefixEnd_6264140 := by exact prefixLift 6264140
  have htrace : WordTrace (prefixWord ++ tailWord_6264140) baseStart_6264140 baseEnd_6264140 := by
    simpa [prefixWord, tailWord_6264140, baseEnd_6264140] using wordTrace_append hprefix tailTrace_6264140
  have hstable : (prefixWord ++ tailWord_6264140).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6264140).length < 2 ^ (prefixWord ++ tailWord_6264140).sum := by decide
  have hdescent : baseEnd_6264140 < baseStart_6264140 := by decide
  rcases family_descends (prefixWord ++ tailWord_6264140) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6264142 : List Nat := [4, 1, 1, 1, 1, 1, 3, 2, 9]
def baseStart_6264142 : Nat := 118140960795 + 6264142 * 2 ^ 59
def prefixEnd_6264142 : Nat := 4983230072969 + 3 ^ 40 * 6264142 * 2
def baseEnd_6264142 : Nat := 357390637112948416590749

theorem tailTrace_6264142 : CollatzResearch.WordTrace tailWord_6264142 prefixEnd_6264142 357390637112948416590749 := by
  unfold tailWord_6264142
  simp only [CollatzResearch.WordTrace]
  refine ⟨28559003559011354890646335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 152314685648060559416780453 28559003559011354890646335)
  ·
    refine ⟨42838505338517032335969503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28559003559011354890646335 42838505338517032335969503)
    ·
      refine ⟨64257758007775548503954255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42838505338517032335969503 64257758007775548503954255)
      ·
        refine ⟨96386637011663322755931383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64257758007775548503954255 96386637011663322755931383)
        ·
          refine ⟨144579955517494984133897075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 96386637011663322755931383 144579955517494984133897075)
          ·
            refine ⟨216869933276242476200845613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 144579955517494984133897075 216869933276242476200845613)
            ·
              refine ⟨81326224978590928575317105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 216869933276242476200845613 81326224978590928575317105)
              ·
                refine ⟨60994668733943196431487829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 81326224978590928575317105 60994668733943196431487829)
                ·
                  refine ⟨357390637112948416590749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 60994668733943196431487829 357390637112948416590749)
                  ·
                    rfl

theorem cell23_6264142_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 3, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 3, 2, 9].length) (baseStart_6264142 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6264142 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6264142 prefixEnd_6264142 := by exact prefixLift 6264142
  have htrace : WordTrace (prefixWord ++ tailWord_6264142) baseStart_6264142 baseEnd_6264142 := by
    simpa [prefixWord, tailWord_6264142, baseEnd_6264142] using wordTrace_append hprefix tailTrace_6264142
  have hstable : (prefixWord ++ tailWord_6264142).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6264142).length < 2 ^ (prefixWord ++ tailWord_6264142).sum := by decide
  have hdescent : baseEnd_6264142 < baseStart_6264142 := by decide
  rcases family_descends (prefixWord ++ tailWord_6264142) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6264149 : List Nat := [1, 3, 2, 2, 3, 1, 1, 2, 2, 2, 4]
def baseStart_6264149 : Nat := 118140960795 + 6264149 * 2 ^ 59
def prefixEnd_6264149 : Nat := 4983230072969 + 3 ^ 40 * 6264149 * 2
def baseEnd_6264149 : Nat := 3216519328381117221929209

theorem tailTrace_6264149 : CollatzResearch.WordTrace tailWord_6264149 prefixEnd_6264149 3216519328381117221929209 := by
  unfold tailWord_6264149
  simp only [CollatzResearch.WordTrace]
  refine ⟨228472283783065479320675501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152314855855376986213783667 228472283783065479320675501)
  ·
    refine ⟨85677106418649554745253313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 228472283783065479320675501 85677106418649554745253313)
    ·
      refine ⟨64257829813987166058939985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 85677106418649554745253313 64257829813987166058939985)
      ·
        refine ⟨48193372360490374544204989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 64257829813987166058939985 48193372360490374544204989)
        ·
          refine ⟨18072514635183890454076871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 48193372360490374544204989 18072514635183890454076871)
          ·
            refine ⟨27108771952775835681115307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18072514635183890454076871 27108771952775835681115307)
            ·
              refine ⟨40663157929163753521672961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27108771952775835681115307 40663157929163753521672961)
              ·
                refine ⟨30497368446872815141254721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 40663157929163753521672961 30497368446872815141254721)
                ·
                  refine ⟨22873026335154611355941041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 30497368446872815141254721 22873026335154611355941041)
                  ·
                    refine ⟨17154769751365958516955781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 22873026335154611355941041 17154769751365958516955781)
                    ·
                      refine ⟨3216519328381117221929209, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17154769751365958516955781 3216519328381117221929209)
                      ·
                        rfl

theorem cell23_6264149_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 1, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 1, 1, 2, 2, 2, 4].length) (baseStart_6264149 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6264149 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6264149 prefixEnd_6264149 := by exact prefixLift 6264149
  have htrace : WordTrace (prefixWord ++ tailWord_6264149) baseStart_6264149 baseEnd_6264149 := by
    simpa [prefixWord, tailWord_6264149, baseEnd_6264149] using wordTrace_append hprefix tailTrace_6264149
  have hstable : (prefixWord ++ tailWord_6264149).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6264149).length < 2 ^ (prefixWord ++ tailWord_6264149).sum := by decide
  have hdescent : baseEnd_6264149 < baseStart_6264149 := by decide
  rcases family_descends (prefixWord ++ tailWord_6264149) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6264153 : List Nat := [1, 2, 1, 2, 2, 2, 5, 2, 2, 2, 2]
def baseStart_6264153 : Nat := 118140960795 + 6264153 * 2 ^ 59
def prefixEnd_6264153 : Nat := 4983230072969 + 3 ^ 40 * 6264153 * 2
def baseEnd_6264153 : Nat := 3216521382303735206279191

theorem tailTrace_6264153 : CollatzResearch.WordTrace tailWord_6264153 prefixEnd_6264153 3216521382303735206279191 := by
  unfold tailWord_6264153
  simp only [CollatzResearch.WordTrace]
  refine ⟨228472429675050988003821113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152314953116700658669214075 228472429675050988003821113)
  ·
    refine ⟨171354322256288241002865835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 228472429675050988003821113 171354322256288241002865835)
    ·
      refine ⟨257031483384432361504298753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 171354322256288241002865835 257031483384432361504298753)
      ·
        refine ⟨192773612538324271128224065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 257031483384432361504298753 192773612538324271128224065)
        ·
          refine ⟨144580209403743203346168049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 192773612538324271128224065 144580209403743203346168049)
          ·
            refine ⟨108435157052807402509626037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 144580209403743203346168049 108435157052807402509626037)
            ·
              refine ⟨10165795973700693985277441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 108435157052807402509626037 10165795973700693985277441)
              ·
                refine ⟨7624346980275520488958081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10165795973700693985277441 7624346980275520488958081)
                ·
                  refine ⟨5718260235206640366718561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7624346980275520488958081 5718260235206640366718561)
                  ·
                    refine ⟨4288695176404980275038921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5718260235206640366718561 4288695176404980275038921)
                    ·
                      refine ⟨3216521382303735206279191, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4288695176404980275038921 3216521382303735206279191)
                      ·
                        rfl

theorem cell23_6264153_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 5, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 5, 2, 2, 2, 2].length) (baseStart_6264153 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6264153 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6264153 prefixEnd_6264153 := by exact prefixLift 6264153
  have htrace : WordTrace (prefixWord ++ tailWord_6264153) baseStart_6264153 baseEnd_6264153 := by
    simpa [prefixWord, tailWord_6264153, baseEnd_6264153] using wordTrace_append hprefix tailTrace_6264153
  have hstable : (prefixWord ++ tailWord_6264153).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6264153).length < 2 ^ (prefixWord ++ tailWord_6264153).sum := by decide
  have hdescent : baseEnd_6264153 < baseStart_6264153 := by decide
  rcases family_descends (prefixWord ++ tailWord_6264153) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6264170 : List Nat := [3, 1, 3, 3, 2, 2, 1, 1, 1, 4, 2]
def baseStart_6264170 : Nat := 118140960795 + 6264170 * 2 ^ 59
def prefixEnd_6264170 : Nat := 4983230072969 + 3 ^ 40 * 6264170 * 2
def baseEnd_6264170 : Nat := 3216530111474861639766613

theorem tailTrace_6264170 : CollatzResearch.WordTrace tailWord_6264170 prefixEnd_6264170 3216530111474861639766613 := by
  unfold tailWord_6264170
  simp only [CollatzResearch.WordTrace]
  refine ⟨57118262428997349976797491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 152315366477326266604793309 57118262428997349976797491)
  ·
    refine ⟨85677393643496024965196237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57118262428997349976797491 85677393643496024965196237)
    ·
      refine ⟨32129022616311009361948589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 85677393643496024965196237 32129022616311009361948589)
      ·
        refine ⟨12048383481116628510730721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 32129022616311009361948589 12048383481116628510730721)
        ·
          refine ⟨9036287610837471383048041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12048383481116628510730721 9036287610837471383048041)
          ·
            refine ⟨6777215708128103537286031, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9036287610837471383048041 6777215708128103537286031)
            ·
              refine ⟨10165823562192155305929047, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6777215708128103537286031 10165823562192155305929047)
              ·
                refine ⟨15248735343288232958893571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10165823562192155305929047 15248735343288232958893571)
                ·
                  refine ⟨22873103014932349438340357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15248735343288232958893571 22873103014932349438340357)
                  ·
                    refine ⟨4288706815299815519688817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 22873103014932349438340357 4288706815299815519688817)
                    ·
                      refine ⟨3216530111474861639766613, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4288706815299815519688817 3216530111474861639766613)
                      ·
                        rfl

theorem cell23_6264170_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 2, 2, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 2, 2, 1, 1, 1, 4, 2].length) (baseStart_6264170 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6264170 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6264170 prefixEnd_6264170 := by exact prefixLift 6264170
  have htrace : WordTrace (prefixWord ++ tailWord_6264170) baseStart_6264170 baseEnd_6264170 := by
    simpa [prefixWord, tailWord_6264170, baseEnd_6264170] using wordTrace_append hprefix tailTrace_6264170
  have hstable : (prefixWord ++ tailWord_6264170).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6264170).length < 2 ^ (prefixWord ++ tailWord_6264170).sum := by decide
  have hdescent : baseEnd_6264170 < baseStart_6264170 := by decide
  rcases family_descends (prefixWord ++ tailWord_6264170) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6264189 : List Nat := [1, 4, 1, 1, 2, 2, 2, 3, 2, 5]
def baseStart_6264189 : Nat := 118140960795 + 6264189 * 2 ^ 59
def prefixEnd_6264189 : Nat := 4983230072969 + 3 ^ 40 * 6264189 * 2
def baseEnd_6264189 : Nat := 1072179955869099021809675

theorem tailTrace_6264189 : CollatzResearch.WordTrace tailWord_6264189 prefixEnd_6264189 1072179955869099021809675 := by
  unfold tailWord_6264189
  simp only [CollatzResearch.WordTrace]
  refine ⟨228473742702920566152131621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152315828468613710768087747 228473742702920566152131621)
  ·
    refine ⟨42838826756797606153524679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 228473742702920566152131621 42838826756797606153524679)
    ·
      refine ⟨64258240135196409230287019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42838826756797606153524679 64258240135196409230287019)
      ·
        refine ⟨96387360202794613845430529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64258240135196409230287019 96387360202794613845430529)
        ·
          refine ⟨72290520152095960384072897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 96387360202794613845430529 72290520152095960384072897)
          ·
            refine ⟨54217890114071970288054673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 72290520152095960384072897 54217890114071970288054673)
            ·
              refine ⟨40663417585553977716041005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 54217890114071970288054673 40663417585553977716041005)
              ·
                refine ⟨15248781594582741643515377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 40663417585553977716041005 15248781594582741643515377)
                ·
                  refine ⟨11436586195937056232636533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15248781594582741643515377 11436586195937056232636533)
                  ·
                    refine ⟨1072179955869099021809675, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11436586195937056232636533 1072179955869099021809675)
                    ·
                      rfl

theorem cell23_6264189_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 2, 3, 2, 5].length) (baseStart_6264189 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6264189 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6264189 prefixEnd_6264189 := by exact prefixLift 6264189
  have htrace : WordTrace (prefixWord ++ tailWord_6264189) baseStart_6264189 baseEnd_6264189 := by
    simpa [prefixWord, tailWord_6264189, baseEnd_6264189] using wordTrace_append hprefix tailTrace_6264189
  have hstable : (prefixWord ++ tailWord_6264189).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6264189).length < 2 ^ (prefixWord ++ tailWord_6264189).sum := by decide
  have hdescent : baseEnd_6264189 < baseStart_6264189 := by decide
  rcases family_descends (prefixWord ++ tailWord_6264189) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6264209 : List Nat := [1, 2, 2, 1, 1, 1, 2, 6, 2, 1, 4]
def baseStart_6264209 : Nat := 118140960795 + 6264209 * 2 ^ 59
def prefixEnd_6264209 : Nat := 4983230072969 + 3 ^ 40 * 6264209 * 2
def baseEnd_6264209 : Nat := 3216550137220386987178933

theorem tailTrace_6264209 : CollatzResearch.WordTrace tailWord_6264209 prefixEnd_6264209 3216550137220386987178933 := by
  unfold tailWord_6264209
  simp only [CollatzResearch.WordTrace]
  refine ⟨228474472162848109567859681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152316314775232073045239787 228474472162848109567859681)
  ·
    refine ⟨171355854122136082175894761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 228474472162848109567859681 171355854122136082175894761)
    ·
      refine ⟨128516890591602061631921071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 171355854122136082175894761 128516890591602061631921071)
      ·
        refine ⟨192775335887403092447881607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 128516890591602061631921071 192775335887403092447881607)
        ·
          refine ⟨289163003831104638671822411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 192775335887403092447881607 289163003831104638671822411)
          ·
            refine ⟨433744505746656958007733617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 289163003831104638671822411 433744505746656958007733617)
            ·
              refine ⟨325308379309992718505800213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 433744505746656958007733617 325308379309992718505800213)
              ·
                refine ⟨15248830280155908679959385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 325308379309992718505800213 15248830280155908679959385)
                ·
                  refine ⟨11436622710116931509969539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15248830280155908679959385 11436622710116931509969539)
                  ·
                    refine ⟨17154934065175397264954309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11436622710116931509969539 17154934065175397264954309)
                    ·
                      refine ⟨3216550137220386987178933, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17154934065175397264954309 3216550137220386987178933)
                      ·
                        rfl

theorem cell23_6264209_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 2, 6, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 2, 6, 2, 1, 4].length) (baseStart_6264209 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6264209 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6264209 prefixEnd_6264209 := by exact prefixLift 6264209
  have htrace : WordTrace (prefixWord ++ tailWord_6264209) baseStart_6264209 baseEnd_6264209 := by
    simpa [prefixWord, tailWord_6264209, baseEnd_6264209] using wordTrace_append hprefix tailTrace_6264209
  have hstable : (prefixWord ++ tailWord_6264209).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6264209).length < 2 ^ (prefixWord ++ tailWord_6264209).sum := by decide
  have hdescent : baseEnd_6264209 < baseStart_6264209 := by decide
  rcases family_descends (prefixWord ++ tailWord_6264209) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6264210 : List Nat := [3, 2, 3, 3, 2, 1, 1, 1, 7]
def baseStart_6264210 : Nat := 118140960795 + 6264210 * 2 ^ 59
def prefixEnd_6264210 : Nat := 4983230072969 + 3 ^ 40 * 6264210 * 2
def baseEnd_6264210 : Nat := 357394516744560164807381

theorem tailTrace_6264210 : CollatzResearch.WordTrace tailWord_6264210 prefixEnd_6264210 357394516744560164807381 := by
  unfold tailWord_6264210
  simp only [CollatzResearch.WordTrace]
  refine ⟨57118627158961121684661521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 152316339090562991159097389 57118627158961121684661521)
  ·
    refine ⟨42838970369220841263496141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57118627158961121684661521 42838970369220841263496141)
    ·
      refine ⟨16064613888457815473811053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 42838970369220841263496141 16064613888457815473811053)
      ·
        refine ⟨6024230208171680802679145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16064613888457815473811053 6024230208171680802679145)
        ·
          refine ⟨4518172656128760602009359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6024230208171680802679145 4518172656128760602009359)
          ·
            refine ⟨6777258984193140903014039, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4518172656128760602009359 6777258984193140903014039)
            ·
              refine ⟨10165888476289711354521059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6777258984193140903014039 10165888476289711354521059)
              ·
                refine ⟨15248832714434567031781589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10165888476289711354521059 15248832714434567031781589)
                ·
                  refine ⟨357394516744560164807381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 15248832714434567031781589 357394516744560164807381)
                  ·
                    rfl

theorem cell23_6264210_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 3, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 3, 2, 1, 1, 1, 7].length) (baseStart_6264210 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6264210 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6264210 prefixEnd_6264210 := by exact prefixLift 6264210
  have htrace : WordTrace (prefixWord ++ tailWord_6264210) baseStart_6264210 baseEnd_6264210 := by
    simpa [prefixWord, tailWord_6264210, baseEnd_6264210] using wordTrace_append hprefix tailTrace_6264210
  have hstable : (prefixWord ++ tailWord_6264210).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6264210).length < 2 ^ (prefixWord ++ tailWord_6264210).sum := by decide
  have hdescent : baseEnd_6264210 < baseStart_6264210 := by decide
  rcases family_descends (prefixWord ++ tailWord_6264210) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6264216 : List Nat := [2, 1, 2, 5, 2, 1, 1, 1, 1, 2, 5]
def baseStart_6264216 : Nat := 118140960795 + 6264216 * 2 ^ 59
def prefixEnd_6264216 : Nat := 4983230072969 + 3 ^ 40 * 6264216 * 2
def baseEnd_6264216 : Nat := 3216553731584968459791401

theorem tailTrace_6264216 : CollatzResearch.WordTrace tailWord_6264216 prefixEnd_6264216 3216553731584968459791401 := by
  unfold tailWord_6264216
  simp only [CollatzResearch.WordTrace]
  refine ⟨114237363736911374881682251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 152316484982548499842243001 114237363736911374881682251)
  ·
    refine ⟨171356045605367062322523377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114237363736911374881682251 171356045605367062322523377)
    ·
      refine ⟨128517034204025296741892533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 171356045605367062322523377 128517034204025296741892533)
      ·
        refine ⟨12048471956627371569552425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 128517034204025296741892533 12048471956627371569552425)
        ·
          refine ⟨9036353967470528677164319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12048471956627371569552425 9036353967470528677164319)
          ·
            refine ⟨13554530951205793015746479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9036353967470528677164319 13554530951205793015746479)
            ·
              refine ⟨20331796426808689523619719, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13554530951205793015746479 20331796426808689523619719)
              ·
                refine ⟨30497694640213034285429579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20331796426808689523619719 30497694640213034285429579)
                ·
                  refine ⟨45746541960319551428144369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30497694640213034285429579 45746541960319551428144369)
                  ·
                    refine ⟨34309906470239663571108277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 45746541960319551428144369 34309906470239663571108277)
                    ·
                      refine ⟨3216553731584968459791401, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 34309906470239663571108277 3216553731584968459791401)
                      ·
                        rfl

theorem cell23_6264216_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 2, 1, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 2, 1, 1, 1, 1, 2, 5].length) (baseStart_6264216 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6264216 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6264216 prefixEnd_6264216 := by exact prefixLift 6264216
  have htrace : WordTrace (prefixWord ++ tailWord_6264216) baseStart_6264216 baseEnd_6264216 := by
    simpa [prefixWord, tailWord_6264216, baseEnd_6264216] using wordTrace_append hprefix tailTrace_6264216
  have hstable : (prefixWord ++ tailWord_6264216).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6264216).length < 2 ^ (prefixWord ++ tailWord_6264216).sum := by decide
  have hdescent : baseEnd_6264216 < baseStart_6264216 := by decide
  rcases family_descends (prefixWord ++ tailWord_6264216) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6264229 : List Nat := [1, 3, 1, 2, 1, 1, 2, 4, 1, 4, 3]
def baseStart_6264229 : Nat := 118140960795 + 6264229 * 2 ^ 59
def prefixEnd_6264229 : Nat := 4983230072969 + 3 ^ 40 * 6264229 * 2
def baseEnd_6264229 : Nat := 3216560406833476908928841

theorem tailTrace_6264229 : CollatzResearch.WordTrace tailWord_6264229 prefixEnd_6264229 3216560406833476908928841 := by
  unfold tailWord_6264229
  simp only [CollatzResearch.WordTrace]
  refine ⟨228475201622775652983587741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152316801081850435322391827 228475201622775652983587741)
  ·
    refine ⟨85678200608540869868845403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 228475201622775652983587741 85678200608540869868845403)
    ·
      refine ⟨128517300912811304803268105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85678200608540869868845403 128517300912811304803268105)
      ·
        refine ⟨96387975684608478602451079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 128517300912811304803268105 96387975684608478602451079)
        ·
          refine ⟨144581963526912717903676619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 96387975684608478602451079 144581963526912717903676619)
          ·
            refine ⟨216872945290369076855514929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 144581963526912717903676619 216872945290369076855514929)
            ·
              refine ⟨162654708967776807641636197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 216872945290369076855514929 162654708967776807641636197)
              ·
                refine ⟨30497757931458151432806787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 162654708967776807641636197 30497757931458151432806787)
                ·
                  refine ⟨45746636897187227149210181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30497757931458151432806787 45746636897187227149210181)
                  ·
                    refine ⟨8577494418222605090476909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 45746636897187227149210181 8577494418222605090476909)
                    ·
                      refine ⟨3216560406833476908928841, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8577494418222605090476909 3216560406833476908928841)
                      ·
                        rfl

theorem cell23_6264229_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 2, 4, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 2, 4, 1, 4, 3].length) (baseStart_6264229 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6264229 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6264229 prefixEnd_6264229 := by exact prefixLift 6264229
  have htrace : WordTrace (prefixWord ++ tailWord_6264229) baseStart_6264229 baseEnd_6264229 := by
    simpa [prefixWord, tailWord_6264229, baseEnd_6264229] using wordTrace_append hprefix tailTrace_6264229
  have hstable : (prefixWord ++ tailWord_6264229).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6264229).length < 2 ^ (prefixWord ++ tailWord_6264229).sum := by decide
  have hdescent : baseEnd_6264229 < baseStart_6264229 := by decide
  rcases family_descends (prefixWord ++ tailWord_6264229) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6264253 : List Nat := [1, 4, 1, 2, 2, 1, 2, 5, 1, 4]
def baseStart_6264253 : Nat := 118140960795 + 6264253 * 2 ^ 59
def prefixEnd_6264253 : Nat := 4983230072969 + 3 ^ 40 * 6264253 * 2
def baseEnd_6264253 : Nat := 1072190910123061605009577

theorem tailTrace_6264253 : CollatzResearch.WordTrace tailWord_6264253 prefixEnd_6264253 1072190910123061605009577 := by
  unfold tailWord_6264253
  simp only [CollatzResearch.WordTrace]
  refine ⟨228476076974688705082461413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152317384649792470054974275 228476076974688705082461413)
  ·
    refine ⟨42839264432754132202961515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 228476076974688705082461413 42839264432754132202961515)
    ·
      refine ⟨64258896649131198304442273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42839264432754132202961515 64258896649131198304442273)
      ·
        refine ⟨48194172486848398728331705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 64258896649131198304442273 48194172486848398728331705)
        ·
          refine ⟨36145629365136299046248779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48194172486848398728331705 36145629365136299046248779)
          ·
            refine ⟨54218444047704448569373169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36145629365136299046248779 54218444047704448569373169)
            ·
              refine ⟨40663833035778336427029877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 54218444047704448569373169 40663833035778336427029877)
              ·
                refine ⟨3812234347104219040034051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 40663833035778336427029877 3812234347104219040034051)
                ·
                  refine ⟨5718351520656328560051077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3812234347104219040034051 5718351520656328560051077)
                  ·
                    refine ⟨1072190910123061605009577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5718351520656328560051077 1072190910123061605009577)
                    ·
                      rfl

theorem cell23_6264253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 2, 5, 1, 4].length) (baseStart_6264253 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6264253 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6264253 prefixEnd_6264253 := by exact prefixLift 6264253
  have htrace : WordTrace (prefixWord ++ tailWord_6264253) baseStart_6264253 baseEnd_6264253 := by
    simpa [prefixWord, tailWord_6264253, baseEnd_6264253] using wordTrace_append hprefix tailTrace_6264253
  have hstable : (prefixWord ++ tailWord_6264253).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6264253).length < 2 ^ (prefixWord ++ tailWord_6264253).sum := by decide
  have hdescent : baseEnd_6264253 < baseStart_6264253 := by decide
  rcases family_descends (prefixWord ++ tailWord_6264253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6264266 : List Nat := [3, 1, 2, 1, 2, 4, 2, 2, 6]
def baseStart_6264266 : Nat := 118140960795 + 6264266 * 2 ^ 59
def prefixEnd_6264266 : Nat := 4983230072969 + 3 ^ 40 * 6264266 * 2
def baseEnd_6264266 : Nat := 357397711735299251574019

theorem tailTrace_6264266 : CollatzResearch.WordTrace tailWord_6264266 prefixEnd_6264266 357397711735299251574019 := by
  unfold tailWord_6264266
  simp only [CollatzResearch.WordTrace]
  refine ⟨57119137780910402075671163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 152317700749094405535123101 57119137780910402075671163)
  ·
    refine ⟨85678706671365603113506745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57119137780910402075671163 85678706671365603113506745)
    ·
      refine ⟨64259030003524202335130059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 85678706671365603113506745 64259030003524202335130059)
      ·
        refine ⟨96388545005286303502695089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64259030003524202335130059 96388545005286303502695089)
        ·
          refine ⟨72291408753964727627021317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 96388545005286303502695089 72291408753964727627021317)
          ·
            refine ⟨13554639141368386430066497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 72291408753964727627021317 13554639141368386430066497)
            ·
              refine ⟨10165979356026289822549873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13554639141368386430066497 10165979356026289822549873)
              ·
                refine ⟨7624484517019717366912405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10165979356026289822549873 7624484517019717366912405)
                ·
                  refine ⟨357397711735299251574019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7624484517019717366912405 357397711735299251574019)
                  ·
                    rfl

theorem cell23_6264266_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 4, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 4, 2, 2, 6].length) (baseStart_6264266 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6264266 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6264266 prefixEnd_6264266 := by exact prefixLift 6264266
  have htrace : WordTrace (prefixWord ++ tailWord_6264266) baseStart_6264266 baseEnd_6264266 := by
    simpa [prefixWord, tailWord_6264266, baseEnd_6264266] using wordTrace_append hprefix tailTrace_6264266
  have hstable : (prefixWord ++ tailWord_6264266).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6264266).length < 2 ^ (prefixWord ++ tailWord_6264266).sum := by decide
  have hdescent : baseEnd_6264266 < baseStart_6264266 := by decide
  rcases family_descends (prefixWord ++ tailWord_6264266) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6264270 : List Nat := [4, 1, 1, 1, 2, 1, 6, 2, 1, 4]
def baseStart_6264270 : Nat := 118140960795 + 6264270 * 2 ^ 59
def prefixEnd_6264270 : Nat := 4983230072969 + 3 ^ 40 * 6264270 * 2
def baseEnd_6264270 : Nat := 1072193819846770416172051

theorem tailTrace_6264270 : CollatzResearch.WordTrace tailWord_6264270 prefixEnd_6264270 1072193819846770416172051 := by
  unfold tailWord_6264270
  simp only [CollatzResearch.WordTrace]
  refine ⟨28559587126953389623228783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 152317798010418077990553509 28559587126953389623228783)
  ·
    refine ⟨42839380690430084434843175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28559587126953389623228783 42839380690430084434843175)
    ·
      refine ⟨64259071035645126652264763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42839380690430084434843175 64259071035645126652264763)
      ·
        refine ⟨96388606553467689978397145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64259071035645126652264763 96388606553467689978397145)
        ·
          refine ⟨72291454915100767483797859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 96388606553467689978397145 72291454915100767483797859)
          ·
            refine ⟨108437182372651151225696789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 72291454915100767483797859 108437182372651151225696789)
            ·
              refine ⟨5082992923718022713704537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 108437182372651151225696789 5082992923718022713704537)
              ·
                refine ⟨3812244692788517035278403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5082992923718022713704537 3812244692788517035278403)
                ·
                  refine ⟨5718367039182775552917605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3812244692788517035278403 5718367039182775552917605)
                  ·
                    refine ⟨1072193819846770416172051, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5718367039182775552917605 1072193819846770416172051)
                    ·
                      rfl

theorem cell23_6264270_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 6, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 6, 2, 1, 4].length) (baseStart_6264270 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6264270 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6264270 prefixEnd_6264270 := by exact prefixLift 6264270
  have htrace : WordTrace (prefixWord ++ tailWord_6264270) baseStart_6264270 baseEnd_6264270 := by
    simpa [prefixWord, tailWord_6264270, baseEnd_6264270] using wordTrace_append hprefix tailTrace_6264270
  have hstable : (prefixWord ++ tailWord_6264270).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6264270).length < 2 ^ (prefixWord ++ tailWord_6264270).sum := by decide
  have hdescent : baseEnd_6264270 < baseStart_6264270 := by decide
  rcases family_descends (prefixWord ++ tailWord_6264270) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6264293 : List Nat := [1, 3, 1, 5, 1, 1, 1, 1, 5, 1, 3]
def baseStart_6264293 : Nat := 118140960795 + 6264293 * 2 ^ 59
def prefixEnd_6264293 : Nat := 4983230072969 + 3 ^ 40 * 6264293 * 2
def baseEnd_6264293 : Nat := 3216593269595364658528547

theorem tailTrace_6264293 : CollatzResearch.WordTrace tailWord_6264293 prefixEnd_6264293 3216593269595364658528547 := by
  unfold tailWord_6264293
  simp only [CollatzResearch.WordTrace]
  refine ⟨228477535894543791913917533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152318357263029194609278355 228477535894543791913917533)
  ·
    refine ⟨85679075960453921967719075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 228477535894543791913917533 85679075960453921967719075)
    ·
      refine ⟨128518613940680882951578613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85679075960453921967719075 128518613940680882951578613)
      ·
        refine ⟨12048620056938832776710495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 128518613940680882951578613 12048620056938832776710495)
        ·
          refine ⟨18072930085408249165065743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12048620056938832776710495 18072930085408249165065743)
          ·
            refine ⟨27109395128112373747598615, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18072930085408249165065743 27109395128112373747598615)
            ·
              refine ⟨40664092692168560621397923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27109395128112373747598615 40664092692168560621397923)
              ·
                refine ⟨60996139038252840932096885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40664092692168560621397923 60996139038252840932096885)
                ·
                  refine ⟨5718388034836203837384083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 60996139038252840932096885 5718388034836203837384083)
                  ·
                    refine ⟨8577582052254305756076125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5718388034836203837384083 8577582052254305756076125)
                    ·
                      refine ⟨3216593269595364658528547, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8577582052254305756076125 3216593269595364658528547)
                      ·
                        rfl

theorem cell23_6264293_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 1, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 1, 1, 1, 5, 1, 3].length) (baseStart_6264293 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6264293 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6264293 prefixEnd_6264293 := by exact prefixLift 6264293
  have htrace : WordTrace (prefixWord ++ tailWord_6264293) baseStart_6264293 baseEnd_6264293 := by
    simpa [prefixWord, tailWord_6264293, baseEnd_6264293] using wordTrace_append hprefix tailTrace_6264293
  have hstable : (prefixWord ++ tailWord_6264293).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6264293).length < 2 ^ (prefixWord ++ tailWord_6264293).sum := by decide
  have hdescent : baseEnd_6264293 < baseStart_6264293 := by decide
  rcases family_descends (prefixWord ++ tailWord_6264293) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6264296 : List Nat := [2, 1, 4, 1, 1, 2, 2, 4, 1, 5]
def baseStart_6264296 : Nat := 118140960795 + 6264296 * 2 ^ 59
def prefixEnd_6264296 : Nat := 4983230072969 + 3 ^ 40 * 6264296 * 2
def baseEnd_6264296 : Nat := 1072198270012442715597011

theorem tailTrace_6264296 : CollatzResearch.WordTrace tailWord_6264296 prefixEnd_6264296 1072198270012442715597011 := by
  unfold tailWord_6264296
  simp only [CollatzResearch.WordTrace]
  refine ⟨114238822656766461713138371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 152318430209021948950851161 114238822656766461713138371)
  ·
    refine ⟨171358233985149692569707557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114238822656766461713138371 171358233985149692569707557)
    ·
      refine ⟨32129668872215567356820167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 171358233985149692569707557 32129668872215567356820167)
      ·
        refine ⟨48194503308323351035230251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32129668872215567356820167 48194503308323351035230251)
        ·
          refine ⟨72291754962485026552845377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48194503308323351035230251 72291754962485026552845377)
          ·
            refine ⟨54218816221863769914634033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 72291754962485026552845377 54218816221863769914634033)
            ·
              refine ⟨40664112166397827435975525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 54218816221863769914634033 40664112166397827435975525)
              ·
                refine ⟨7624521031199592644245411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 40664112166397827435975525 7624521031199592644245411)
                ·
                  refine ⟨11436781546799388966368117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7624521031199592644245411 11436781546799388966368117)
                  ·
                    refine ⟨1072198270012442715597011, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11436781546799388966368117 1072198270012442715597011)
                    ·
                      rfl

theorem cell23_6264296_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 2, 4, 1, 5].length) (baseStart_6264296 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6264296 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6264296 prefixEnd_6264296 := by exact prefixLift 6264296
  have htrace : WordTrace (prefixWord ++ tailWord_6264296) baseStart_6264296 baseEnd_6264296 := by
    simpa [prefixWord, tailWord_6264296, baseEnd_6264296] using wordTrace_append hprefix tailTrace_6264296
  have hstable : (prefixWord ++ tailWord_6264296).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6264296).length < 2 ^ (prefixWord ++ tailWord_6264296).sum := by decide
  have hdescent : baseEnd_6264296 < baseStart_6264296 := by decide
  rcases family_descends (prefixWord ++ tailWord_6264296) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6264303 : List Nat := [1, 1, 2, 1, 4, 1, 5, 1, 2, 3, 2]
def baseStart_6264303 : Nat := 118140960795 + 6264303 * 2 ^ 59
def prefixEnd_6264303 : Nat := 4983230072969 + 3 ^ 40 * 6264303 * 2
def baseEnd_6264303 : Nat := 3216598404401909619403501

theorem tailTrace_6264303 : CollatzResearch.WordTrace tailWord_6264303 prefixEnd_6264303 3216598404401909619403501 := by
  unfold tailWord_6264303
  simp only [CollatzResearch.WordTrace]
  refine ⟨228477900624507563621781563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152318600416338375747854375 228477900624507563621781563)
  ·
    refine ⟨342716850936761345432672345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 228477900624507563621781563 342716850936761345432672345)
    ·
      refine ⟨257037638202571009074504259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 342716850936761345432672345 257037638202571009074504259)
      ·
        refine ⟨385556457303856513611756389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 257037638202571009074504259 385556457303856513611756389)
        ·
          refine ⟨72291835744473096302204323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 385556457303856513611756389 72291835744473096302204323)
          ·
            refine ⟨108437753616709644453306485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 72291835744473096302204323 108437753616709644453306485)
            ·
              refine ⟨10166039401566529167497483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 108437753616709644453306485 10166039401566529167497483)
              ·
                refine ⟨15249059102349793751246225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10166039401566529167497483 15249059102349793751246225)
                ·
                  refine ⟨11436794326762345313434669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15249059102349793751246225 11436794326762345313434669)
                  ·
                    refine ⟨4288797872535879492538001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11436794326762345313434669 4288797872535879492538001)
                    ·
                      refine ⟨3216598404401909619403501, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4288797872535879492538001 3216598404401909619403501)
                      ·
                        rfl

theorem cell23_6264303_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 5, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 5, 1, 2, 3, 2].length) (baseStart_6264303 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6264303 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6264303 prefixEnd_6264303 := by exact prefixLift 6264303
  have htrace : WordTrace (prefixWord ++ tailWord_6264303) baseStart_6264303 baseEnd_6264303 := by
    simpa [prefixWord, tailWord_6264303, baseEnd_6264303] using wordTrace_append hprefix tailTrace_6264303
  have hstable : (prefixWord ++ tailWord_6264303).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6264303).length < 2 ^ (prefixWord ++ tailWord_6264303).sum := by decide
  have hdescent : baseEnd_6264303 < baseStart_6264303 := by decide
  rcases family_descends (prefixWord ++ tailWord_6264303) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6264329 : List Nat := [1, 2, 1, 1, 3, 1, 4, 2, 1, 1, 6]
def baseStart_6264329 : Nat := 118140960795 + 6264329 * 2 ^ 59
def prefixEnd_6264329 : Nat := 4983230072969 + 3 ^ 40 * 6264329 * 2
def baseEnd_6264329 : Nat := 3216611754898926517678381

theorem tailTrace_6264329 : CollatzResearch.WordTrace tailWord_6264329 prefixEnd_6264329 3216611754898926517678381 := by
  unfold tailWord_6264329
  simp only [CollatzResearch.WordTrace]
  refine ⟨228478848922413370062228041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152319232614942246708152027 228478848922413370062228041)
  ·
    refine ⟨171359136691810027546671031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 228478848922413370062228041 171359136691810027546671031)
    ·
      refine ⟨257038705037715041320006547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 171359136691810027546671031 257038705037715041320006547)
      ·
        refine ⟨385558057556572561980009821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 257038705037715041320006547 385558057556572561980009821)
        ·
          refine ⟨144584271583714710742503683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 385558057556572561980009821 144584271583714710742503683)
          ·
            refine ⟨216876407375572066113755525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 144584271583714710742503683 216876407375572066113755525)
            ·
              refine ⟨40664326382919762396329161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 216876407375572066113755525 40664326382919762396329161)
              ·
                refine ⟨30498244787189821797246871, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 40664326382919762396329161 30498244787189821797246871)
                ·
                  refine ⟨45747367180784732695870307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30498244787189821797246871 45747367180784732695870307)
                  ·
                    refine ⟨68621050771177099043805461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 45747367180784732695870307 68621050771177099043805461)
                    ·
                      refine ⟨3216611754898926517678381, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 68621050771177099043805461 3216611754898926517678381)
                      ·
                        rfl

theorem cell23_6264329_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 4, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 4, 2, 1, 1, 6].length) (baseStart_6264329 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6264329 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6264329 prefixEnd_6264329 := by exact prefixLift 6264329
  have htrace : WordTrace (prefixWord ++ tailWord_6264329) baseStart_6264329 baseEnd_6264329 := by
    simpa [prefixWord, tailWord_6264329, baseEnd_6264329] using wordTrace_append hprefix tailTrace_6264329
  have hstable : (prefixWord ++ tailWord_6264329).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6264329).length < 2 ^ (prefixWord ++ tailWord_6264329).sum := by decide
  have hdescent : baseEnd_6264329 < baseStart_6264329 := by decide
  rcases family_descends (prefixWord ++ tailWord_6264329) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6264353 : List Nat := [1, 2, 3, 2, 2, 2, 1, 4, 1, 2, 3]
def baseStart_6264353 : Nat := 118140960795 + 6264353 * 2 ^ 59
def prefixEnd_6264353 : Nat := 4983230072969 + 3 ^ 40 * 6264353 * 2
def baseEnd_6264353 : Nat := 3216624078434634423778271

theorem tailTrace_6264353 : CollatzResearch.WordTrace tailWord_6264353 prefixEnd_6264353 3216624078434634423778271 := by
  unfold tailWord_6264353
  simp only [CollatzResearch.WordTrace]
  refine ⟨228479724274326422161101713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152319816182884281440734475 228479724274326422161101713)
  ·
    refine ⟨171359793205744816620826285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 228479724274326422161101713 171359793205744816620826285)
    ·
      refine ⟨64259922452154306232809857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 171359793205744816620826285 64259922452154306232809857)
      ·
        refine ⟨48194941839115729674607393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 64259922452154306232809857 48194941839115729674607393)
        ·
          refine ⟨36146206379336797255955545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48194941839115729674607393 36146206379336797255955545)
          ·
            refine ⟨27109654784502597941966659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36146206379336797255955545 27109654784502597941966659)
            ·
              refine ⟨40664482176753896912949989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27109654784502597941966659 40664482176753896912949989)
              ·
                refine ⟨7624590408141355671178123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 40664482176753896912949989 7624590408141355671178123)
                ·
                  refine ⟨11436885612212033506767185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7624590408141355671178123 11436885612212033506767185)
                  ·
                    refine ⟨8577664209159025130075389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11436885612212033506767185 8577664209159025130075389)
                    ·
                      refine ⟨3216624078434634423778271, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8577664209159025130075389 3216624078434634423778271)
                      ·
                        rfl

theorem cell23_6264353_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 2, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 2, 1, 4, 1, 2, 3].length) (baseStart_6264353 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6264353 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6264353 prefixEnd_6264353 := by exact prefixLift 6264353
  have htrace : WordTrace (prefixWord ++ tailWord_6264353) baseStart_6264353 baseEnd_6264353 := by
    simpa [prefixWord, tailWord_6264353, baseEnd_6264353] using wordTrace_append hprefix tailTrace_6264353
  have hstable : (prefixWord ++ tailWord_6264353).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6264353).length < 2 ^ (prefixWord ++ tailWord_6264353).sum := by decide
  have hdescent : baseEnd_6264353 < baseStart_6264353 := by decide
  rcases family_descends (prefixWord ++ tailWord_6264353) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6264369 : List Nat := [1, 2, 2, 3, 1, 1, 1, 2, 1, 9]
def baseStart_6264369 : Nat := 118140960795 + 6264369 * 2 ^ 59
def prefixEnd_6264369 : Nat := 4983230072969 + 3 ^ 40 * 6264369 * 2
def baseEnd_6264369 : Nat := 1072210764708368787059399

theorem tailTrace_6264369 : CollatzResearch.WordTrace tailWord_6264369 prefixEnd_6264369 1072210764708368787059399 := by
  unfold tailWord_6264369
  simp only [CollatzResearch.WordTrace]
  refine ⟨228480307842268456893684161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152320205228178971262456107 228480307842268456893684161)
  ·
    refine ⟨171360230881701342670263121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 228480307842268456893684161 171360230881701342670263121)
    ·
      refine ⟨128520173161276007002697341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 171360230881701342670263121 128520173161276007002697341)
      ·
        refine ⟨48195064935478502626011503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 128520173161276007002697341 48195064935478502626011503)
        ·
          refine ⟨72292597403217753939017255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48195064935478502626011503 72292597403217753939017255)
          ·
            refine ⟨108438896104826630908525883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 72292597403217753939017255 108438896104826630908525883)
            ·
              refine ⟨162658344157239946362788825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 108438896104826630908525883 162658344157239946362788825)
              ·
                refine ⟨121993758117929959772091619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 162658344157239946362788825 121993758117929959772091619)
                ·
                  refine ⟨182990637176894939658137429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 121993758117929959772091619 182990637176894939658137429)
                  ·
                    refine ⟨1072210764708368787059399, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 182990637176894939658137429 1072210764708368787059399)
                    ·
                      rfl

theorem cell23_6264369_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 1, 2, 1, 9].length) (baseStart_6264369 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6264369 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6264369 prefixEnd_6264369 := by exact prefixLift 6264369
  have htrace : WordTrace (prefixWord ++ tailWord_6264369) baseStart_6264369 baseEnd_6264369 := by
    simpa [prefixWord, tailWord_6264369, baseEnd_6264369] using wordTrace_append hprefix tailTrace_6264369
  have hstable : (prefixWord ++ tailWord_6264369).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6264369).length < 2 ^ (prefixWord ++ tailWord_6264369).sum := by decide
  have hdescent : baseEnd_6264369 < baseStart_6264369 := by decide
  rcases family_descends (prefixWord ++ tailWord_6264369) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6264383 : List Nat := [1, 1, 2, 2, 3, 3, 2, 1, 4, 1, 3]
def baseStart_6264383 : Nat := 118140960795 + 6264383 * 2 ^ 59
def prefixEnd_6264383 : Nat := 4983230072969 + 3 ^ 40 * 6264383 * 2
def baseEnd_6264383 : Nat := 3216639482854269306403133

theorem tailTrace_6264383 : CollatzResearch.WordTrace tailWord_6264383 prefixEnd_6264383 3216639482854269306403133 := by
  unfold tailWord_6264383
  simp only [CollatzResearch.WordTrace]
  refine ⟨228480818464217737284693803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152320545642811824856462535 228480818464217737284693803)
  ·
    refine ⟨342721227696326605927040705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 228480818464217737284693803 342721227696326605927040705)
    ·
      refine ⟨257040920772244954445280529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 342721227696326605927040705 257040920772244954445280529)
      ·
        refine ⟨192780690579183715833960397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 257040920772244954445280529 192780690579183715833960397)
        ·
          refine ⟨72292758967193893437735149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 192780690579183715833960397 72292758967193893437735149)
          ·
            refine ⟨27109784612697710039150681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 72292758967193893437735149 27109784612697710039150681)
            ·
              refine ⟨20332338459523282529363011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27109784612697710039150681 20332338459523282529363011)
              ·
                refine ⟨30498507689284923794044517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20332338459523282529363011 30498507689284923794044517)
                ·
                  refine ⟨5718470191740923211383347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 30498507689284923794044517 5718470191740923211383347)
                  ·
                    refine ⟨8577705287611384817075021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5718470191740923211383347 8577705287611384817075021)
                    ·
                      refine ⟨3216639482854269306403133, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8577705287611384817075021 3216639482854269306403133)
                      ·
                        rfl

theorem cell23_6264383_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 3, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 3, 2, 1, 4, 1, 3].length) (baseStart_6264383 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6264383 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6264383 prefixEnd_6264383 := by exact prefixLift 6264383
  have htrace : WordTrace (prefixWord ++ tailWord_6264383) baseStart_6264383 baseEnd_6264383 := by
    simpa [prefixWord, tailWord_6264383, baseEnd_6264383] using wordTrace_append hprefix tailTrace_6264383
  have hstable : (prefixWord ++ tailWord_6264383).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6264383).length < 2 ^ (prefixWord ++ tailWord_6264383).sum := by decide
  have hdescent : baseEnd_6264383 < baseStart_6264383 := by decide
  rcases family_descends (prefixWord ++ tailWord_6264383) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6264390 : List Nat := [6, 1, 1, 1, 3, 1, 2, 8]
def baseStart_6264390 : Nat := 118140960795 + 6264390 * 2 ^ 59
def prefixEnd_6264390 : Nat := 4983230072969 + 3 ^ 40 * 6264390 * 2
def baseEnd_6264390 : Nat := 119134928785883362185763

theorem tailTrace_6264390 : CollatzResearch.WordTrace tailWord_6264390 prefixEnd_6264390 119134928785883362185763 := by
  unfold tailWord_6264390
  simp only [CollatzResearch.WordTrace]
  refine ⟨7140033555474761796256207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 152320715850128251653465749 7140033555474761796256207)
  ·
    refine ⟨10710050333212142694384311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7140033555474761796256207 10710050333212142694384311)
    ·
      refine ⟨16065075499818214041576467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10710050333212142694384311 16065075499818214041576467)
      ·
        refine ⟨24097613249727321062364701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16065075499818214041576467 24097613249727321062364701)
        ·
          refine ⟨9036604968647745398386763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24097613249727321062364701 9036604968647745398386763)
          ·
            refine ⟨13554907452971618097580145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9036604968647745398386763 13554907452971618097580145)
            ·
              refine ⟨10166180589728713573185109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13554907452971618097580145 10166180589728713573185109)
              ·
                refine ⟨119134928785883362185763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 10166180589728713573185109 119134928785883362185763)
                ·
                  rfl

theorem cell23_6264390_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 3, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 3, 1, 2, 8].length) (baseStart_6264390 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6264390 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6264390 prefixEnd_6264390 := by exact prefixLift 6264390
  have htrace : WordTrace (prefixWord ++ tailWord_6264390) baseStart_6264390 baseEnd_6264390 := by
    simpa [prefixWord, tailWord_6264390, baseEnd_6264390] using wordTrace_append hprefix tailTrace_6264390
  have hstable : (prefixWord ++ tailWord_6264390).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6264390).length < 2 ^ (prefixWord ++ tailWord_6264390).sum := by decide
  have hdescent : baseEnd_6264390 < baseStart_6264390 := by decide
  rcases family_descends (prefixWord ++ tailWord_6264390) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6264399 : List Nat := [1, 1, 2, 1, 1, 2, 3, 3, 1, 8]
def baseStart_6264399 : Nat := 118140960795 + 6264399 * 2 ^ 59
def prefixEnd_6264399 : Nat := 4983230072969 + 3 ^ 40 * 6264399 * 2
def baseEnd_6264399 : Nat := 1072215899514913747934353

theorem tailTrace_6264399 : CollatzResearch.WordTrace tailWord_6264399 prefixEnd_6264399 1072215899514913747934353 := by
  unfold tailWord_6264399
  simp only [CollatzResearch.WordTrace]
  refine ⟨228481402032159772017276251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152320934688106514678184167 228481402032159772017276251)
  ·
    refine ⟨342722103048239658025914377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 228481402032159772017276251 342722103048239658025914377)
    ·
      refine ⟨257041577286179743519435783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 342722103048239658025914377 257041577286179743519435783)
      ·
        refine ⟨385562365929269615279153675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 257041577286179743519435783 385562365929269615279153675)
        ·
          refine ⟨578343548893904422918730513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 385562365929269615279153675 578343548893904422918730513)
          ·
            refine ⟨433757661670428317189047885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 578343548893904422918730513 433757661670428317189047885)
            ·
              refine ⟨162659123126410618945892957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 433757661670428317189047885 162659123126410618945892957)
              ·
                refine ⟨60997171172403982104709859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 162659123126410618945892957 60997171172403982104709859)
                ·
                  refine ⟨91495756758605973157064789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 60997171172403982104709859 91495756758605973157064789)
                  ·
                    refine ⟨1072215899514913747934353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 91495756758605973157064789 1072215899514913747934353)
                    ·
                      rfl

theorem cell23_6264399_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 3, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 3, 3, 1, 8].length) (baseStart_6264399 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6264399 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6264399 prefixEnd_6264399 := by exact prefixLift 6264399
  have htrace : WordTrace (prefixWord ++ tailWord_6264399) baseStart_6264399 baseEnd_6264399 := by
    simpa [prefixWord, tailWord_6264399, baseEnd_6264399] using wordTrace_append hprefix tailTrace_6264399
  have hstable : (prefixWord ++ tailWord_6264399).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6264399).length < 2 ^ (prefixWord ++ tailWord_6264399).sum := by decide
  have hdescent : baseEnd_6264399 < baseStart_6264399 := by decide
  rcases family_descends (prefixWord ++ tailWord_6264399) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6264423 : List Nat := [1, 1, 5, 1, 1, 1, 3, 1, 3, 4, 2]
def baseStart_6264423 : Nat := 118140960795 + 6264423 * 2 ^ 59
def prefixEnd_6264423 : Nat := 4983230072969 + 3 ^ 40 * 6264423 * 2
def baseEnd_6264423 : Nat := 3216660022080449149902949

theorem tailTrace_6264423 : CollatzResearch.WordTrace tailWord_6264423 prefixEnd_6264423 3216660022080449149902949 := by
  unfold tailWord_6264423
  simp only [CollatzResearch.WordTrace]
  refine ⟨228482277384072824116149923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152321518256048549410766615 228482277384072824116149923)
  ·
    refine ⟨342723416076109236174224885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 228482277384072824116149923 342723416076109236174224885)
    ·
      refine ⟨32130320257135240891333583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 342723416076109236174224885 32130320257135240891333583)
      ·
        refine ⟨48195480385702861337000375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32130320257135240891333583 48195480385702861337000375)
        ·
          refine ⟨72293220578554292005500563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48195480385702861337000375 72293220578554292005500563)
          ·
            refine ⟨108439830867831438008250845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 72293220578554292005500563 108439830867831438008250845)
            ·
              refine ⟨40664936575436789253094067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 108439830867831438008250845 40664936575436789253094067)
              ·
                refine ⟨60997404863155183879641101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40664936575436789253094067 60997404863155183879641101)
                ·
                  refine ⟨22874026823683193954865413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 60997404863155183879641101 22874026823683193954865413)
                  ·
                    refine ⟨4288880029440598866537265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 22874026823683193954865413 4288880029440598866537265)
                    ·
                      refine ⟨3216660022080449149902949, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4288880029440598866537265 3216660022080449149902949)
                      ·
                        rfl

theorem cell23_6264423_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 3, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 3, 1, 3, 4, 2].length) (baseStart_6264423 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6264423 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6264423 prefixEnd_6264423 := by exact prefixLift 6264423
  have htrace : WordTrace (prefixWord ++ tailWord_6264423) baseStart_6264423 baseEnd_6264423 := by
    simpa [prefixWord, tailWord_6264423, baseEnd_6264423] using wordTrace_append hprefix tailTrace_6264423
  have hstable : (prefixWord ++ tailWord_6264423).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6264423).length < 2 ^ (prefixWord ++ tailWord_6264423).sum := by decide
  have hdescent : baseEnd_6264423 < baseStart_6264423 := by decide
  rcases family_descends (prefixWord ++ tailWord_6264423) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6264480 : List Nat := [2, 1, 1, 4, 3, 2, 2, 3, 5]
def baseStart_6264480 : Nat := 118140960795 + 6264480 * 2 ^ 59
def prefixEnd_6264480 : Nat := 4983230072969 + 3 ^ 40 * 6264480 * 2
def baseEnd_6264480 : Nat := 357409921164195047432243

theorem tailTrace_6264480 : CollatzResearch.WordTrace tailWord_6264480 prefixEnd_6264480 357409921164195047432243 := by
  unfold tailWord_6264480
  simp only [CollatzResearch.WordTrace]
  refine ⟨114242178172433161425487447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 152322904229910881900649929 114242178172433161425487447)
  ·
    refine ⟨171363267258649742138231171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114242178172433161425487447 171363267258649742138231171)
    ·
      refine ⟨257044900887974613207346757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 171363267258649742138231171 257044900887974613207346757)
      ·
        refine ⟨48195918916495239976377517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 257044900887974613207346757 48195918916495239976377517)
        ·
          refine ⟨18073469593685714991141569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 48195918916495239976377517 18073469593685714991141569)
          ·
            refine ⟨13555102195264286243356177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18073469593685714991141569 13555102195264286243356177)
            ·
              refine ⟨10166326646448214682517133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13555102195264286243356177 10166326646448214682517133)
              ·
                refine ⟨3812372492418080505943925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10166326646448214682517133 3812372492418080505943925)
                ·
                  refine ⟨357409921164195047432243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3812372492418080505943925 357409921164195047432243)
                  ·
                    rfl

theorem cell23_6264480_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 2, 2, 3, 5].length) (baseStart_6264480 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6264480 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6264480 prefixEnd_6264480 := by exact prefixLift 6264480
  have htrace : WordTrace (prefixWord ++ tailWord_6264480) baseStart_6264480 baseEnd_6264480 := by
    simpa [prefixWord, tailWord_6264480, baseEnd_6264480] using wordTrace_append hprefix tailTrace_6264480
  have hstable : (prefixWord ++ tailWord_6264480).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6264480).length < 2 ^ (prefixWord ++ tailWord_6264480).sum := by decide
  have hdescent : baseEnd_6264480 < baseStart_6264480 := by decide
  rcases family_descends (prefixWord ++ tailWord_6264480) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6264493 : List Nat := [1, 5, 2, 1, 1, 1, 2, 1, 4, 5]
def baseStart_6264493 : Nat := 118140960795 + 6264493 * 2 ^ 59
def prefixEnd_6264493 : Nat := 4983230072969 + 3 ^ 40 * 6264493 * 2
def baseEnd_6264493 : Nat := 1072231988575421292009209

theorem tailTrace_6264493 : CollatzResearch.WordTrace tailWord_6264493 prefixEnd_6264493 1072231988575421292009209 := by
  unfold tailWord_6264493
  simp only [CollatzResearch.WordTrace]
  refine ⟨228484830493819226071198133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152323220329212817380798755 228484830493819226071198133)
  ·
    refine ⟨21420452858795552444174825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 228484830493819226071198133 21420452858795552444174825)
    ·
      refine ⟨16065339644096664333131119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21420452858795552444174825 16065339644096664333131119)
      ·
        refine ⟨24098009466144996499696679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16065339644096664333131119 24098009466144996499696679)
        ·
          refine ⟨36147014199217494749545019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24098009466144996499696679 36147014199217494749545019)
          ·
            refine ⟨54220521298826242124317529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36147014199217494749545019 54220521298826242124317529)
            ·
              refine ⟨40665390974119681593238147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 54220521298826242124317529 40665390974119681593238147)
              ·
                refine ⟨60998086461179522389857221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40665390974119681593238147 60998086461179522389857221)
                ·
                  refine ⟨11437141211471160448098229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 60998086461179522389857221 11437141211471160448098229)
                  ·
                    refine ⟨1072231988575421292009209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11437141211471160448098229 1072231988575421292009209)
                    ·
                      rfl

theorem cell23_6264493_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 2, 1, 4, 5].length) (baseStart_6264493 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6264493 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6264493 prefixEnd_6264493 := by exact prefixLift 6264493
  have htrace : WordTrace (prefixWord ++ tailWord_6264493) baseStart_6264493 baseEnd_6264493 := by
    simpa [prefixWord, tailWord_6264493, baseEnd_6264493] using wordTrace_append hprefix tailTrace_6264493
  have hstable : (prefixWord ++ tailWord_6264493).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6264493).length < 2 ^ (prefixWord ++ tailWord_6264493).sum := by decide
  have hdescent : baseEnd_6264493 < baseStart_6264493 := by decide
  rcases family_descends (prefixWord ++ tailWord_6264493) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6264536 : List Nat := [2, 1, 2, 2, 3, 1, 1, 1, 10]
def baseStart_6264536 : Nat := 118140960795 + 6264536 * 2 ^ 59
def prefixEnd_6264536 : Nat := 4983230072969 + 3 ^ 40 * 6264536 * 2
def baseEnd_6264536 : Nat := 357413116154934134198881

theorem tailTrace_6264536 : CollatzResearch.WordTrace tailWord_6264536 prefixEnd_6264536 357413116154934134198881 := by
  unfold tailWord_6264536
  simp only [CollatzResearch.WordTrace]
  refine ⟨114243199416331722207506731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 152324265888442296276675641 114243199416331722207506731)
  ·
    refine ⟨171364799124497583311260097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114243199416331722207506731 171364799124497583311260097)
    ·
      refine ⟨128523599343373187483445073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 171364799124497583311260097 128523599343373187483445073)
      ·
        refine ⟨96392699507529890612583805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 128523599343373187483445073 96392699507529890612583805)
        ·
          refine ⟨36147262315323708979718927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 96392699507529890612583805 36147262315323708979718927)
          ·
            refine ⟨54220893472985563469578391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36147262315323708979718927 54220893472985563469578391)
            ·
              refine ⟨81331340209478345204367587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 54220893472985563469578391 81331340209478345204367587)
              ·
                refine ⟨121997010314217517806551381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 81331340209478345204367587 121997010314217517806551381)
                ·
                  refine ⟨357413116154934134198881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 121997010314217517806551381 357413116154934134198881)
                  ·
                    rfl

theorem cell23_6264536_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 1, 1, 10].length) (baseStart_6264536 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6264536 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6264536 prefixEnd_6264536 := by exact prefixLift 6264536
  have htrace : WordTrace (prefixWord ++ tailWord_6264536) baseStart_6264536 baseEnd_6264536 := by
    simpa [prefixWord, tailWord_6264536, baseEnd_6264536] using wordTrace_append hprefix tailTrace_6264536
  have hstable : (prefixWord ++ tailWord_6264536).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6264536).length < 2 ^ (prefixWord ++ tailWord_6264536).sum := by decide
  have hdescent : baseEnd_6264536 < baseStart_6264536 := by decide
  rcases family_descends (prefixWord ++ tailWord_6264536) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6264556 : List Nat := [2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 8]
def baseStart_6264556 : Nat := 118140960795 + 6264556 * 2 ^ 59
def prefixEnd_6264556 : Nat := 4983230072969 + 3 ^ 40 * 6264556 * 2
def baseEnd_6264556 : Nat := 3216728315007497129539837

theorem tailTrace_6264556 : CollatzResearch.WordTrace tailWord_6264556 prefixEnd_6264556 3216728315007497129539837 := by
  unfold tailWord_6264556
  simp only [CollatzResearch.WordTrace]
  refine ⟨114243564146295493915370761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 152324752195060658553827681 114243564146295493915370761)
  ·
    refine ⟨85682673109721620436528071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 114243564146295493915370761 85682673109721620436528071)
    ·
      refine ⟨128524009664582430654792107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85682673109721620436528071 128524009664582430654792107)
      ·
        refine ⟨192786014496873645982188161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 128524009664582430654792107 192786014496873645982188161)
        ·
          refine ⟨144589510872655234486641121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 192786014496873645982188161 144589510872655234486641121)
          ·
            refine ⟨108442133154491425864980841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 144589510872655234486641121 108442133154491425864980841)
            ·
              refine ⟨81331599865868569398735631, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 108442133154491425864980841 81331599865868569398735631)
              ·
                refine ⟨121997399798802854098103447, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 81331599865868569398735631 121997399798802854098103447)
                ·
                  refine ⟨182996099698204281147155171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 121997399798802854098103447 182996099698204281147155171)
                  ·
                    refine ⟨274494149547306421720732757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 182996099698204281147155171 274494149547306421720732757)
                    ·
                      refine ⟨3216728315007497129539837, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 274494149547306421720732757 3216728315007497129539837)
                      ·
                        rfl

theorem cell23_6264556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 8].length) (baseStart_6264556 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6264556 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6264556 prefixEnd_6264556 := by exact prefixLift 6264556
  have htrace : WordTrace (prefixWord ++ tailWord_6264556) baseStart_6264556 baseEnd_6264556 := by
    simpa [prefixWord, tailWord_6264556, baseEnd_6264556] using wordTrace_append hprefix tailTrace_6264556
  have hstable : (prefixWord ++ tailWord_6264556).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6264556).length < 2 ^ (prefixWord ++ tailWord_6264556).sum := by decide
  have hdescent : baseEnd_6264556 < baseStart_6264556 := by decide
  rcases family_descends (prefixWord ++ tailWord_6264556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6264557 : List Nat := [1, 5, 1, 2, 1, 4, 1, 1, 3, 4]
def baseStart_6264557 : Nat := 118140960795 + 6264557 * 2 ^ 59
def prefixEnd_6264557 : Nat := 4983230072969 + 3 ^ 40 * 6264557 * 2
def baseEnd_6264557 : Nat := 1072242942829383875209111

theorem tailTrace_6264557 : CollatzResearch.WordTrace tailWord_6264557 prefixEnd_6264557 1072242942829383875209111 := by
  unfold tailWord_6264557
  simp only [CollatzResearch.WordTrace]
  refine ⟨228487164765587365001527925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152324776510391576667685283 228487164765587365001527925)
  ·
    refine ⟨21420671696773815468893243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 228487164765587365001527925 21420671696773815468893243)
    ·
      refine ⟨32131007545160723203339865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21420671696773815468893243 32131007545160723203339865)
      ·
        refine ⟨24098255658870542402504899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32131007545160723203339865 24098255658870542402504899)
        ·
          refine ⟨36147383488305813603757349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24098255658870542402504899 36147383488305813603757349)
          ·
            refine ⟨6777634404057340050704503, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 36147383488305813603757349 6777634404057340050704503)
            ·
              refine ⟨10166451606086010076056755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6777634404057340050704503 10166451606086010076056755)
              ·
                refine ⟨15249677409129015114085133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10166451606086010076056755 15249677409129015114085133)
                ·
                  refine ⟨5718629028423380667781925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15249677409129015114085133 5718629028423380667781925)
                  ·
                    refine ⟨1072242942829383875209111, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5718629028423380667781925 1072242942829383875209111)
                    ·
                      rfl

theorem cell23_6264557_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 4, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 4, 1, 1, 3, 4].length) (baseStart_6264557 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6264557 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6264557 prefixEnd_6264557 := by exact prefixLift 6264557
  have htrace : WordTrace (prefixWord ++ tailWord_6264557) baseStart_6264557 baseEnd_6264557 := by
    simpa [prefixWord, tailWord_6264557, baseEnd_6264557] using wordTrace_append hprefix tailTrace_6264557
  have hstable : (prefixWord ++ tailWord_6264557).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6264557).length < 2 ^ (prefixWord ++ tailWord_6264557).sum := by decide
  have hdescent : baseEnd_6264557 < baseStart_6264557 := by decide
  rcases family_descends (prefixWord ++ tailWord_6264557) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6264576 : List Nat := [2, 1, 1, 2, 1, 1, 2, 3, 2, 1, 7]
def baseStart_6264576 : Nat := 118140960795 + 6264576 * 2 ^ 59
def prefixEnd_6264576 : Nat := 4983230072969 + 3 ^ 40 * 6264576 * 2
def baseEnd_6264576 : Nat := 3216738584620587051289745

theorem tailTrace_6264576 : CollatzResearch.WordTrace tailWord_6264576 prefixEnd_6264576 3216738584620587051289745 := by
  unfold tailWord_6264576
  simp only [CollatzResearch.WordTrace]
  refine ⟨114243928876259265623234791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 152325238501679020830979721 114243928876259265623234791)
  ·
    refine ⟨171365893314388898434852187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114243928876259265623234791 171365893314388898434852187)
    ·
      refine ⟨257048839971583347652278281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 171365893314388898434852187 257048839971583347652278281)
      ·
        refine ⟨192786629978687510739208711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 257048839971583347652278281 192786629978687510739208711)
        ·
          refine ⟨289179944968031266108813067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 192786629978687510739208711 289179944968031266108813067)
          ·
            refine ⟨433769917452046899163219601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 289179944968031266108813067 433769917452046899163219601)
            ·
              refine ⟨325327438089035174372414701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 433769917452046899163219601 325327438089035174372414701)
              ·
                refine ⟨121997789283388190389655513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 325327438089035174372414701 121997789283388190389655513)
                ·
                  refine ⟨91498341962541142792241635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 121997789283388190389655513 91498341962541142792241635)
                  ·
                    refine ⟨137247512943811714188362453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 91498341962541142792241635 137247512943811714188362453)
                    ·
                      refine ⟨3216738584620587051289745, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 137247512943811714188362453 3216738584620587051289745)
                      ·
                        rfl

theorem cell23_6264576_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 2, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 2, 3, 2, 1, 7].length) (baseStart_6264576 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6264576 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6264576 prefixEnd_6264576 := by exact prefixLift 6264576
  have htrace : WordTrace (prefixWord ++ tailWord_6264576) baseStart_6264576 baseEnd_6264576 := by
    simpa [prefixWord, tailWord_6264576, baseEnd_6264576] using wordTrace_append hprefix tailTrace_6264576
  have hstable : (prefixWord ++ tailWord_6264576).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6264576).length < 2 ^ (prefixWord ++ tailWord_6264576).sum := by decide
  have hdescent : baseEnd_6264576 < baseStart_6264576 := by decide
  rcases family_descends (prefixWord ++ tailWord_6264576) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6264590 : List Nat := [4, 1, 1, 2, 1, 1, 2, 3, 1, 5, 2]
def baseStart_6264590 : Nat := 118140960795 + 6264590 * 2 ^ 59
def prefixEnd_6264590 : Nat := 4983230072969 + 3 ^ 40 * 6264590 * 2
def baseEnd_6264590 : Nat := 3216745773349749996514681

theorem tailTrace_6264590 : CollatzResearch.WordTrace tailWord_6264590 prefixEnd_6264590 3216745773349749996514681 := by
  unfold tailWord_6264590
  simp only [CollatzResearch.WordTrace]
  refine ⟨28561046046808476454684903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 152325578916311874424986149 28561046046808476454684903)
  ·
    refine ⟨42841569070212714682027355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28561046046808476454684903 42841569070212714682027355)
    ·
      refine ⟨64262353605319072023041033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42841569070212714682027355 64262353605319072023041033)
      ·
        refine ⟨48196765203989304017280775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 64262353605319072023041033 48196765203989304017280775)
        ·
          refine ⟨72295147805983956025921163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48196765203989304017280775 72295147805983956025921163)
          ·
            refine ⟨108442721708975934038881745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 72295147805983956025921163 108442721708975934038881745)
            ·
              refine ⟨81332041281731950529161309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 108442721708975934038881745 81332041281731950529161309)
              ·
                refine ⟨30499515480649481448435491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 81332041281731950529161309 30499515480649481448435491)
                ·
                  refine ⟨45749273220974222172653237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30499515480649481448435491 45749273220974222172653237)
                  ·
                    refine ⟨4288994364466333328686241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 45749273220974222172653237 4288994364466333328686241)
                    ·
                      refine ⟨3216745773349749996514681, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4288994364466333328686241 3216745773349749996514681)
                      ·
                        rfl

theorem cell23_6264590_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 2, 3, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 2, 3, 1, 5, 2].length) (baseStart_6264590 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6264590 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6264590 prefixEnd_6264590 := by exact prefixLift 6264590
  have htrace : WordTrace (prefixWord ++ tailWord_6264590) baseStart_6264590 baseEnd_6264590 := by
    simpa [prefixWord, tailWord_6264590, baseEnd_6264590] using wordTrace_append hprefix tailTrace_6264590
  have hstable : (prefixWord ++ tailWord_6264590).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6264590).length < 2 ^ (prefixWord ++ tailWord_6264590).sum := by decide
  have hdescent : baseEnd_6264590 < baseStart_6264590 := by decide
  rcases family_descends (prefixWord ++ tailWord_6264590) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6264657 : List Nat := [1, 2, 2, 1, 5, 2, 1, 3, 1, 2, 3]
def baseStart_6264657 : Nat := 118140960795 + 6264657 * 2 ^ 59
def prefixEnd_6264657 : Nat := 4983230072969 + 3 ^ 40 * 6264657 * 2
def baseEnd_6264657 : Nat := 3216780176553601234376873

theorem tailTrace_6264657 : CollatzResearch.WordTrace tailWord_6264657 prefixEnd_6264657 3216780176553601234376873 := by
  unfold tailWord_6264657
  simp only [CollatzResearch.WordTrace]
  refine ⟨228490812065225082080168225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152327208043483388053445483 228490812065225082080168225)
  ·
    refine ⟨171368109048918811560126169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 228490812065225082080168225 171368109048918811560126169)
    ·
      refine ⟨128526081786689108670094627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 171368109048918811560126169 128526081786689108670094627)
      ·
        refine ⟨192789122680033663005141941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 128526081786689108670094627 192789122680033663005141941)
        ·
          refine ⟨18073980251253155906732057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 192789122680033663005141941 18073980251253155906732057)
          ·
            refine ⟨13555485188439866930049043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18073980251253155906732057 13555485188439866930049043)
            ·
              refine ⟨20333227782659800395073565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13555485188439866930049043 20333227782659800395073565)
              ·
                refine ⟨7624960418497425148152587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20333227782659800395073565 7624960418497425148152587)
                ·
                  refine ⟨11437440627746137722228881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7624960418497425148152587 11437440627746137722228881)
                  ·
                    refine ⟨8578080470809603291671661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11437440627746137722228881 8578080470809603291671661)
                    ·
                      refine ⟨3216780176553601234376873, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8578080470809603291671661 3216780176553601234376873)
                      ·
                        rfl

theorem cell23_6264657_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 2, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 2, 1, 3, 1, 2, 3].length) (baseStart_6264657 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6264657 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6264657 prefixEnd_6264657 := by exact prefixLift 6264657
  have htrace : WordTrace (prefixWord ++ tailWord_6264657) baseStart_6264657 baseEnd_6264657 := by
    simpa [prefixWord, tailWord_6264657, baseEnd_6264657] using wordTrace_append hprefix tailTrace_6264657
  have hstable : (prefixWord ++ tailWord_6264657).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6264657).length < 2 ^ (prefixWord ++ tailWord_6264657).sum := by decide
  have hdescent : baseEnd_6264657 < baseStart_6264657 := by decide
  rcases family_descends (prefixWord ++ tailWord_6264657) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6264694 : List Nat := [5, 1, 1, 3, 2, 2, 2, 7]
def baseStart_6264694 : Nat := 118140960795 + 6264694 * 2 ^ 59
def prefixEnd_6264694 : Nat := 4983230072969 + 3 ^ 40 * 6264694 * 2
def baseEnd_6264694 : Nat := 119140710197696947763489

theorem tailTrace_6264694 : CollatzResearch.WordTrace tailWord_6264694 prefixEnd_6264694 119140710197696947763489 := by
  unfold tailWord_6264694
  simp only [CollatzResearch.WordTrace]
  refine ⟨14280760097880689837454071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 152328107710727358266176757 14280760097880689837454071)
  ·
    refine ⟨21421140146821034756181107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14280760097880689837454071 21421140146821034756181107)
    ·
      refine ⟨32131710220231552134271661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21421140146821034756181107 32131710220231552134271661)
      ·
        refine ⟨12049391332586832050351873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 32131710220231552134271661 12049391332586832050351873)
        ·
          refine ⟨9037043499440124037763905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12049391332586832050351873 9037043499440124037763905)
          ·
            refine ⟨6777782624580093028322929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9037043499440124037763905 6777782624580093028322929)
            ·
              refine ⟨5083336968435069771242197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6777782624580093028322929 5083336968435069771242197)
              ·
                refine ⟨119140710197696947763489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5083336968435069771242197 119140710197696947763489)
                ·
                  rfl

theorem cell23_6264694_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 2, 2, 2, 7].length) (baseStart_6264694 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6264694 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6264694 prefixEnd_6264694 := by exact prefixLift 6264694
  have htrace : WordTrace (prefixWord ++ tailWord_6264694) baseStart_6264694 baseEnd_6264694 := by
    simpa [prefixWord, tailWord_6264694, baseEnd_6264694] using wordTrace_append hprefix tailTrace_6264694
  have hstable : (prefixWord ++ tailWord_6264694).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6264694).length < 2 ^ (prefixWord ++ tailWord_6264694).sum := by decide
  have hdescent : baseEnd_6264694 < baseStart_6264694 := by decide
  rcases family_descends (prefixWord ++ tailWord_6264694) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6264705 : List Nat := [1, 2, 4, 4, 1, 2, 1, 3, 1, 2, 2]
def baseStart_6264705 : Nat := 118140960795 + 6264705 * 2 ^ 59
def prefixEnd_6264705 : Nat := 4983230072969 + 3 ^ 40 * 6264705 * 2
def baseEnd_6264705 : Nat := 3216804823625017046576653

theorem tailTrace_6264705 : CollatzResearch.WordTrace tailWord_6264705 prefixEnd_6264705 3216804823625017046576653 := by
  unfold tailWord_6264705
  simp only [CollatzResearch.WordTrace]
  refine ⟨228492562769051186277915569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152328375179367457518610379 228492562769051186277915569)
  ·
    refine ⟨171369422076788389708436677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 228492562769051186277915569 171369422076788389708436677)
    ·
      refine ⟨32131766639397823070331877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 171369422076788389708436677 32131766639397823070331877)
      ·
        refine ⟨6024706244887091825687227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 32131766639397823070331877 6024706244887091825687227)
        ·
          refine ⟨9037059367330637738530841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6024706244887091825687227 9037059367330637738530841)
          ·
            refine ⟨6777794525497978303898131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9037059367330637738530841 6777794525497978303898131)
            ·
              refine ⟨10166691788246967455847197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6777794525497978303898131 10166691788246967455847197)
              ·
                refine ⟨3812509420592612795942699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10166691788246967455847197 3812509420592612795942699)
                ·
                  refine ⟨5718764130888919193914049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3812509420592612795942699 5718764130888919193914049)
                  ·
                    refine ⟨4289073098166689395435537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5718764130888919193914049 4289073098166689395435537)
                    ·
                      refine ⟨3216804823625017046576653, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4289073098166689395435537 3216804823625017046576653)
                      ·
                        rfl

theorem cell23_6264705_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 4, 1, 2, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 4, 1, 2, 1, 3, 1, 2, 2].length) (baseStart_6264705 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6264705 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6264705 prefixEnd_6264705 := by exact prefixLift 6264705
  have htrace : WordTrace (prefixWord ++ tailWord_6264705) baseStart_6264705 baseEnd_6264705 := by
    simpa [prefixWord, tailWord_6264705, baseEnd_6264705] using wordTrace_append hprefix tailTrace_6264705
  have hstable : (prefixWord ++ tailWord_6264705).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6264705).length < 2 ^ (prefixWord ++ tailWord_6264705).sum := by decide
  have hdescent : baseEnd_6264705 < baseStart_6264705 := by decide
  rcases family_descends (prefixWord ++ tailWord_6264705) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6264738 : List Nat := [3, 3, 1, 2, 3, 2, 2, 1, 2, 1, 3]
def baseStart_6264738 : Nat := 118140960795 + 6264738 * 2 ^ 59
def prefixEnd_6264738 : Nat := 4983230072969 + 3 ^ 40 * 6264738 * 2
def baseEnd_6264738 : Nat := 3216821768486615417464001

theorem tailTrace_6264738 : CollatzResearch.WordTrace tailWord_6264738 prefixEnd_6264738 3216821768486615417464001 := by
  unfold tailWord_6264738
  simp only [CollatzResearch.WordTrace]
  refine ⟨57123441594482908228466717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 152329177585287755275911245 57123441594482908228466717)
  ·
    refine ⟨21421290597931090585675019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 57123441594482908228466717 21421290597931090585675019)
    ·
      refine ⟨32131935896896635878512529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21421290597931090585675019 32131935896896635878512529)
      ·
        refine ⟨24098951922672476908884397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32131935896896635878512529 24098951922672476908884397)
        ·
          refine ⟨9037106971002178840831649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24098951922672476908884397 9037106971002178840831649)
          ·
            refine ⟨6777830228251634130623737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9037106971002178840831649 6777830228251634130623737)
            ·
              refine ⟨5083372671188725597967803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6777830228251634130623737 5083372671188725597967803)
              ·
                refine ⟨7625059006783088396951705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5083372671188725597967803 7625059006783088396951705)
                ·
                  refine ⟨5718794255087316297713779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7625059006783088396951705 5718794255087316297713779)
                  ·
                    refine ⟨8578191382630974446570669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5718794255087316297713779 8578191382630974446570669)
                    ·
                      refine ⟨3216821768486615417464001, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8578191382630974446570669 3216821768486615417464001)
                      ·
                        rfl

theorem cell23_6264738_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 3, 2, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 3, 2, 2, 1, 2, 1, 3].length) (baseStart_6264738 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6264738 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6264738 prefixEnd_6264738 := by exact prefixLift 6264738
  have htrace : WordTrace (prefixWord ++ tailWord_6264738) baseStart_6264738 baseEnd_6264738 := by
    simpa [prefixWord, tailWord_6264738, baseEnd_6264738] using wordTrace_append hprefix tailTrace_6264738
  have hstable : (prefixWord ++ tailWord_6264738).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6264738).length < 2 ^ (prefixWord ++ tailWord_6264738).sum := by decide
  have hdescent : baseEnd_6264738 < baseStart_6264738 := by decide
  rcases family_descends (prefixWord ++ tailWord_6264738) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6264800 : List Nat := [2, 1, 1, 3, 1, 1, 1, 4, 4, 1, 4]
def baseStart_6264800 : Nat := 118140960795 + 6264800 * 2 ^ 59
def prefixEnd_6264800 : Nat := 4983230072969 + 3 ^ 40 * 6264800 * 2
def baseEnd_6264800 : Nat := 3216853604287194174888715

theorem tailTrace_6264800 : CollatzResearch.WordTrace tailWord_6264800 prefixEnd_6264800 3216853604287194174888715 := by
  unfold tailWord_6264800
  simp only [CollatzResearch.WordTrace]
  refine ⟨114248013851853508751311927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 152330685135804678335082569 114248013851853508751311927)
  ·
    refine ⟨171372020777780263126967891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114248013851853508751311927 171372020777780263126967891)
    ·
      refine ⟨257058031166670394690451837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 171372020777780263126967891 257058031166670394690451837)
      ·
        refine ⟨96396761687501398008919439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 257058031166670394690451837 96396761687501398008919439)
        ·
          refine ⟨144595142531252097013379159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 96396761687501398008919439 144595142531252097013379159)
          ·
            refine ⟨216892713796878145520068739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 144595142531252097013379159 216892713796878145520068739)
            ·
              refine ⟨325339070695317218280103109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 216892713796878145520068739 325339070695317218280103109)
              ·
                refine ⟨61001075755371978427519333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 325339070695317218280103109 61001075755371978427519333)
                ·
                  refine ⟨11437701704132245955159875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 61001075755371978427519333 11437701704132245955159875)
                  ·
                    refine ⟨17156552556198368932739813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11437701704132245955159875 17156552556198368932739813)
                    ·
                      refine ⟨3216853604287194174888715, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17156552556198368932739813 3216853604287194174888715)
                      ·
                        rfl

theorem cell23_6264800_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 1, 4, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 1, 4, 4, 1, 4].length) (baseStart_6264800 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6264800 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6264800 prefixEnd_6264800 := by exact prefixLift 6264800
  have htrace : WordTrace (prefixWord ++ tailWord_6264800) baseStart_6264800 baseEnd_6264800 := by
    simpa [prefixWord, tailWord_6264800, baseEnd_6264800] using wordTrace_append hprefix tailTrace_6264800
  have hstable : (prefixWord ++ tailWord_6264800).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6264800).length < 2 ^ (prefixWord ++ tailWord_6264800).sum := by decide
  have hdescent : baseEnd_6264800 < baseStart_6264800 := by decide
  rcases family_descends (prefixWord ++ tailWord_6264800) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6264814 : List Nat := [4, 1, 2, 1, 3, 3, 1, 1, 2, 5]
def baseStart_6264814 : Nat := 118140960795 + 6264814 * 2 ^ 59
def prefixEnd_6264814 : Nat := 4983230072969 + 3 ^ 40 * 6264814 * 2
def baseEnd_6264814 : Nat := 1072286931005452373371217

theorem tailTrace_6264814 : CollatzResearch.WordTrace tailWord_6264814 prefixEnd_6264814 1072286931005452373371217 := by
  unfold tailWord_6264814
  simp only [CollatzResearch.WordTrace]
  refine ⟨28562067290707037236704187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 152331025550437531929088997 28562067290707037236704187)
  ·
    refine ⟨42843100936060555855056281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28562067290707037236704187 42843100936060555855056281)
    ·
      refine ⟨32132325702045416891292211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42843100936060555855056281 32132325702045416891292211)
      ·
        refine ⟨48198488553068125336938317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32132325702045416891292211 48198488553068125336938317)
        ·
          refine ⟨18074433207400547001351869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 48198488553068125336938317 18074433207400547001351869)
          ·
            refine ⟨6777912452775205125506951, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18074433207400547001351869 6777912452775205125506951)
            ·
              refine ⟨10166868679162807688260427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6777912452775205125506951 10166868679162807688260427)
              ·
                refine ⟨15250303018744211532390641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10166868679162807688260427 15250303018744211532390641)
                ·
                  refine ⟨11437727264058158649292981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15250303018744211532390641 11437727264058158649292981)
                  ·
                    refine ⟨1072286931005452373371217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11437727264058158649292981 1072286931005452373371217)
                    ·
                      rfl

theorem cell23_6264814_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 3, 1, 1, 2, 5].length) (baseStart_6264814 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6264814 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6264814 prefixEnd_6264814 := by exact prefixLift 6264814
  have htrace : WordTrace (prefixWord ++ tailWord_6264814) baseStart_6264814 baseEnd_6264814 := by
    simpa [prefixWord, tailWord_6264814, baseEnd_6264814] using wordTrace_append hprefix tailTrace_6264814
  have hstable : (prefixWord ++ tailWord_6264814).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6264814).length < 2 ^ (prefixWord ++ tailWord_6264814).sum := by decide
  have hdescent : baseEnd_6264814 < baseStart_6264814 := by decide
  rcases family_descends (prefixWord ++ tailWord_6264814) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6264817 : List Nat := [1, 2, 2, 2, 5, 1, 1, 1, 1, 3, 4]
def baseStart_6264817 : Nat := 118140960795 + 6264817 * 2 ^ 59
def prefixEnd_6264817 : Nat := 4983230072969 + 3 ^ 40 * 6264817 * 2
def baseEnd_6264817 : Nat := 3216862333458320608376137

theorem tailTrace_6264817 : CollatzResearch.WordTrace tailWord_6264817 prefixEnd_6264817 3216862333458320608376137 := by
  unfold tailWord_6264817
  simp only [CollatzResearch.WordTrace]
  refine ⟨228496647744645429405992705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152331098496430286270661803 228496647744645429405992705)
  ·
    refine ⟨171372485808484072054494529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 228496647744645429405992705 171372485808484072054494529)
    ·
      refine ⟨128529364356363054040870897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 171372485808484072054494529 128529364356363054040870897)
      ·
        refine ⟨96397023267272290530653173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 128529364356363054040870897 96397023267272290530653173)
        ·
          refine ⟨9037220931306777237248735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 96397023267272290530653173 9037220931306777237248735)
          ·
            refine ⟨13555831396960165855873103, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9037220931306777237248735 13555831396960165855873103)
            ·
              refine ⟨20333747095440248783809655, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13555831396960165855873103 20333747095440248783809655)
              ·
                refine ⟨30500620643160373175714483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20333747095440248783809655 30500620643160373175714483)
                ·
                  refine ⟨45750930964740559763571725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30500620643160373175714483 45750930964740559763571725)
                  ·
                    refine ⟨17156599111777709911339397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 45750930964740559763571725 17156599111777709911339397)
                    ·
                      refine ⟨3216862333458320608376137, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17156599111777709911339397 3216862333458320608376137)
                      ·
                        rfl

theorem cell23_6264817_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 5, 1, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 5, 1, 1, 1, 1, 3, 4].length) (baseStart_6264817 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6264817 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6264817 prefixEnd_6264817 := by exact prefixLift 6264817
  have htrace : WordTrace (prefixWord ++ tailWord_6264817) baseStart_6264817 baseEnd_6264817 := by
    simpa [prefixWord, tailWord_6264817, baseEnd_6264817] using wordTrace_append hprefix tailTrace_6264817
  have hstable : (prefixWord ++ tailWord_6264817).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6264817).length < 2 ^ (prefixWord ++ tailWord_6264817).sum := by decide
  have hdescent : baseEnd_6264817 < baseStart_6264817 := by decide
  rcases family_descends (prefixWord ++ tailWord_6264817) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6264840 : List Nat := [2, 1, 3, 2, 1, 2, 3, 1, 8]
def baseStart_6264840 : Nat := 118140960795 + 6264840 * 2 ^ 59
def prefixEnd_6264840 : Nat := 4983230072969 + 3 ^ 40 * 6264840 * 2
def baseEnd_6264840 : Nat := 357430460390374890932059

theorem tailTrace_6264840 : CollatzResearch.WordTrace tailWord_6264840 prefixEnd_6264840 357430460390374890932059 := by
  unfold tailWord_6264840
  simp only [CollatzResearch.WordTrace]
  refine ⟨114248743311781052167039987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 152331657749041402889386649 114248743311781052167039987)
  ·
    refine ⟨171373114967671578250559981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114248743311781052167039987 171373114967671578250559981)
    ·
      refine ⟨64264918112876841843959993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 171373114967671578250559981 64264918112876841843959993)
      ·
        refine ⟨48198688584657631382969995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 64264918112876841843959993 48198688584657631382969995)
        ·
          refine ⟨72298032876986447074454993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48198688584657631382969995 72298032876986447074454993)
          ·
            refine ⟨54223524657739835305841245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 72298032876986447074454993 54223524657739835305841245)
            ·
              refine ⟨20333821746652438239690467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 54223524657739835305841245 20333821746652438239690467)
              ·
                refine ⟨30500732619978657359535701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20333821746652438239690467 30500732619978657359535701)
                ·
                  refine ⟨357430460390374890932059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 30500732619978657359535701 357430460390374890932059)
                  ·
                    rfl

theorem cell23_6264840_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 3, 1, 8].length) (baseStart_6264840 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6264840 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6264840 prefixEnd_6264840 := by exact prefixLift 6264840
  have htrace : WordTrace (prefixWord ++ tailWord_6264840) baseStart_6264840 baseEnd_6264840 := by
    simpa [prefixWord, tailWord_6264840, baseEnd_6264840] using wordTrace_append hprefix tailTrace_6264840
  have hstable : (prefixWord ++ tailWord_6264840).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6264840).length < 2 ^ (prefixWord ++ tailWord_6264840).sum := by decide
  have hdescent : baseEnd_6264840 < baseStart_6264840 := by decide
  rcases family_descends (prefixWord ++ tailWord_6264840) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6264844 : List Nat := [2, 2, 1, 2, 3, 1, 1, 6, 1, 4]
def baseStart_6264844 : Nat := 118140960795 + 6264844 * 2 ^ 59
def prefixEnd_6264844 : Nat := 4983230072969 + 3 ^ 40 * 6264844 * 2
def baseEnd_6264844 : Nat := 1072292065811997334246171

theorem tailTrace_6264844 : CollatzResearch.WordTrace tailWord_6264844 prefixEnd_6264844 1072292065811997334246171 := by
  unfold tailWord_6264844
  simp only [CollatzResearch.WordTrace]
  refine ⟨114248816257773806508612793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 152331755010365075344817057 114248816257773806508612793)
  ·
    refine ⟨85686612193330354881459595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 114248816257773806508612793 85686612193330354881459595)
    ·
      refine ⟨128529918289995532322189393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85686612193330354881459595 128529918289995532322189393)
      ·
        refine ⟨96397438717496649241642045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 128529918289995532322189393 96397438717496649241642045)
        ·
          refine ⟨36149039519061243465615767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 96397438717496649241642045 36149039519061243465615767)
          ·
            refine ⟨54223559278591865198423651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36149039519061243465615767 54223559278591865198423651)
            ·
              refine ⟨81335338917887797797635477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 54223559278591865198423651 81335338917887797797635477)
              ·
                refine ⟨3812594011775990521764163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 81335338917887797797635477 3812594011775990521764163)
                ·
                  refine ⟨5718891017663985782646245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3812594011775990521764163 5718891017663985782646245)
                  ·
                    refine ⟨1072292065811997334246171, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5718891017663985782646245 1072292065811997334246171)
                    ·
                      rfl

theorem cell23_6264844_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 1, 6, 1, 4].length) (baseStart_6264844 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6264844 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6264844 prefixEnd_6264844 := by exact prefixLift 6264844
  have htrace : WordTrace (prefixWord ++ tailWord_6264844) baseStart_6264844 baseEnd_6264844 := by
    simpa [prefixWord, tailWord_6264844, baseEnd_6264844] using wordTrace_append hprefix tailTrace_6264844
  have hstable : (prefixWord ++ tailWord_6264844).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6264844).length < 2 ^ (prefixWord ++ tailWord_6264844).sum := by decide
  have hdescent : baseEnd_6264844 < baseStart_6264844 := by decide
  rcases family_descends (prefixWord ++ tailWord_6264844) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6264878 : List Nat := [4, 1, 3, 1, 1, 4, 1, 3, 1, 4]
def baseStart_6264878 : Nat := 118140960795 + 6264878 * 2 ^ 59
def prefixEnd_6264878 : Nat := 4983230072969 + 3 ^ 40 * 6264878 * 2
def baseEnd_6264878 : Nat := 1072297885259414956571119

theorem tailTrace_6264878 : CollatzResearch.WordTrace tailWord_6264878 prefixEnd_6264878 1072297885259414956571119 := by
  unfold tailWord_6264878
  simp only [CollatzResearch.WordTrace]
  refine ⟨28562359074678054602995411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 152332581731616291215975525 28562359074678054602995411)
  ·
    refine ⟨42843538612017081904493117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28562359074678054602995411 42843538612017081904493117)
    ·
      refine ⟨16066326979506405714184919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 42843538612017081904493117 16066326979506405714184919)
      ·
        refine ⟨24099490469259608571277379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16066326979506405714184919 24099490469259608571277379)
        ·
          refine ⟨36149235703889412856916069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24099490469259608571277379 36149235703889412856916069)
          ·
            refine ⟨6777981694479264910671763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 36149235703889412856916069 6777981694479264910671763)
            ·
              refine ⟨10166972541718897366007645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6777981694479264910671763 10166972541718897366007645)
              ·
                refine ⟨3812614703144586512252867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10166972541718897366007645 3812614703144586512252867)
                ·
                  refine ⟨5718922054716879768379301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3812614703144586512252867 5718922054716879768379301)
                  ·
                    refine ⟨1072297885259414956571119, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5718922054716879768379301 1072297885259414956571119)
                    ·
                      rfl

theorem cell23_6264878_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 4, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 4, 1, 3, 1, 4].length) (baseStart_6264878 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6264878 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6264878 prefixEnd_6264878 := by exact prefixLift 6264878
  have htrace : WordTrace (prefixWord ++ tailWord_6264878) baseStart_6264878 baseEnd_6264878 := by
    simpa [prefixWord, tailWord_6264878, baseEnd_6264878] using wordTrace_append hprefix tailTrace_6264878
  have hstable : (prefixWord ++ tailWord_6264878).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6264878).length < 2 ^ (prefixWord ++ tailWord_6264878).sum := by decide
  have hdescent : baseEnd_6264878 < baseStart_6264878 := by decide
  rcases family_descends (prefixWord ++ tailWord_6264878) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6264887 : List Nat := [1, 1, 3, 1, 2, 2, 4, 3, 1, 5]
def baseStart_6264887 : Nat := 118140960795 + 6264887 * 2 ^ 59
def prefixEnd_6264887 : Nat := 4983230072969 + 3 ^ 40 * 6264887 * 2
def baseEnd_6264887 : Nat := 1072299425701378444833605

theorem tailTrace_6264887 : CollatzResearch.WordTrace tailWord_6264887 prefixEnd_6264887 1072299425701378444833605 := by
  unfold tailWord_6264887
  simp only [CollatzResearch.WordTrace]
  refine ⟨228499200854391831361040915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152332800569594554240693943 228499200854391831361040915)
  ·
    refine ⟨342748801281587747041561373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 228499200854391831361040915 342748801281587747041561373)
    ·
      refine ⟨128530800480595405140585515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 342748801281587747041561373 128530800480595405140585515)
      ·
        refine ⟨192796200720893107710878273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 128530800480595405140585515 192796200720893107710878273)
        ·
          refine ⟨144597150540669830783158705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 192796200720893107710878273 144597150540669830783158705)
          ·
            refine ⟨108447862905502373087369029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 144597150540669830783158705 108447862905502373087369029)
            ·
              refine ⟨20333974294781694953881693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 108447862905502373087369029 20333974294781694953881693)
              ·
                refine ⟨7625240360543135607705635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20333974294781694953881693 7625240360543135607705635)
                ·
                  refine ⟨11437860540814703411558453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7625240360543135607705635 11437860540814703411558453)
                  ·
                    refine ⟨1072299425701378444833605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11437860540814703411558453 1072299425701378444833605)
                    ·
                      rfl

theorem cell23_6264887_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 4, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 4, 3, 1, 5].length) (baseStart_6264887 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6264887 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6264887 prefixEnd_6264887 := by exact prefixLift 6264887
  have htrace : WordTrace (prefixWord ++ tailWord_6264887) baseStart_6264887 baseEnd_6264887 := by
    simpa [prefixWord, tailWord_6264887, baseEnd_6264887] using wordTrace_append hprefix tailTrace_6264887
  have hstable : (prefixWord ++ tailWord_6264887).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6264887).length < 2 ^ (prefixWord ++ tailWord_6264887).sum := by decide
  have hdescent : baseEnd_6264887 < baseStart_6264887 := by decide
  rcases family_descends (prefixWord ++ tailWord_6264887) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6264924 : List Nat := [2, 2, 4, 1, 1, 3, 1, 1, 3, 1, 4]
def baseStart_6264924 : Nat := 118140960795 + 6264924 * 2 ^ 59
def prefixEnd_6264924 : Nat := 4983230072969 + 3 ^ 40 * 6264924 * 2
def baseEnd_6264924 : Nat := 3216917275888351689738145

theorem tailTrace_6264924 : CollatzResearch.WordTrace tailWord_6264924 prefixEnd_6264924 3216917275888351689738145 := by
  unfold tailWord_6264924
  simp only [CollatzResearch.WordTrace]
  refine ⟨114250275177628893340068913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 152333700236838524453425217 114250275177628893340068913)
  ·
    refine ⟨85687706383221670005051685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 114250275177628893340068913 85687706383221670005051685)
    ·
      refine ⟨16066444946854063125947191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 85687706383221670005051685 16066444946854063125947191)
      ·
        refine ⟨24099667420281094688920787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16066444946854063125947191 24099667420281094688920787)
        ·
          refine ⟨36149501130421642033381181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24099667420281094688920787 36149501130421642033381181)
          ·
            refine ⟨13556062923908115762517943, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 36149501130421642033381181 13556062923908115762517943)
            ·
              refine ⟨20334094385862173643776915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13556062923908115762517943 20334094385862173643776915)
              ·
                refine ⟨30501141578793260465665373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20334094385862173643776915 30501141578793260465665373)
                ·
                  refine ⟨11437928092047472674624515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 30501141578793260465665373 11437928092047472674624515)
                  ·
                    refine ⟨17156892138071209011936773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11437928092047472674624515 17156892138071209011936773)
                    ·
                      refine ⟨3216917275888351689738145, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17156892138071209011936773 3216917275888351689738145)
                      ·
                        rfl

theorem cell23_6264924_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 3, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 3, 1, 1, 3, 1, 4].length) (baseStart_6264924 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6264924 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6264924 prefixEnd_6264924 := by exact prefixLift 6264924
  have htrace : WordTrace (prefixWord ++ tailWord_6264924) baseStart_6264924 baseEnd_6264924 := by
    simpa [prefixWord, tailWord_6264924, baseEnd_6264924] using wordTrace_append hprefix tailTrace_6264924
  have hstable : (prefixWord ++ tailWord_6264924).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6264924).length < 2 ^ (prefixWord ++ tailWord_6264924).sum := by decide
  have hdescent : baseEnd_6264924 < baseStart_6264924 := by decide
  rcases family_descends (prefixWord ++ tailWord_6264924) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6264937 : List Nat := [1, 2, 1, 1, 1, 5, 3, 2, 1, 2, 4]
def baseStart_6264937 : Nat := 118140960795 + 6264937 * 2 ^ 59
def prefixEnd_6264937 : Nat := 4983230072969 + 3 ^ 40 * 6264937 * 2
def baseEnd_6264937 : Nat := 3216923951136860138875585

theorem tailTrace_6264937 : CollatzResearch.WordTrace tailWord_6264937 prefixEnd_6264937 3216923951136860138875585 := by
  unfold tailWord_6264937
  simp only [CollatzResearch.WordTrace]
  refine ⟨228501024504210689900361065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152334016336140459933574043 228501024504210689900361065)
  ·
    refine ⟨171375768378158017425270799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 228501024504210689900361065 171375768378158017425270799)
    ·
      refine ⟨257063652567237026137906199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 171375768378158017425270799 257063652567237026137906199)
      ·
        refine ⟨385595478850855539206859299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 257063652567237026137906199 385595478850855539206859299)
        ·
          refine ⟨578393218276283308810288949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 385595478850855539206859299 578393218276283308810288949)
          ·
            refine ⟨54224364213401560200964589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 578393218276283308810288949 54224364213401560200964589)
            ·
              refine ⟨20334136580025585075361721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 54224364213401560200964589 20334136580025585075361721)
              ·
                refine ⟨15250602435019188806521291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20334136580025585075361721 15250602435019188806521291)
                ·
                  refine ⟨22875903652528783209781937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15250602435019188806521291 22875903652528783209781937)
                  ·
                    refine ⟨17156927739396587407336453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 22875903652528783209781937 17156927739396587407336453)
                    ·
                      refine ⟨3216923951136860138875585, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17156927739396587407336453 3216923951136860138875585)
                      ·
                        rfl

theorem cell23_6264937_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 3, 2, 1, 2, 4].length) (baseStart_6264937 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6264937 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6264937 prefixEnd_6264937 := by exact prefixLift 6264937
  have htrace : WordTrace (prefixWord ++ tailWord_6264937) baseStart_6264937 baseEnd_6264937 := by
    simpa [prefixWord, tailWord_6264937, baseEnd_6264937] using wordTrace_append hprefix tailTrace_6264937
  have hstable : (prefixWord ++ tailWord_6264937).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6264937).length < 2 ^ (prefixWord ++ tailWord_6264937).sum := by decide
  have hdescent : baseEnd_6264937 < baseStart_6264937 := by decide
  rcases family_descends (prefixWord ++ tailWord_6264937) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6264941 : List Nat := [1, 5, 1, 1, 2, 1, 5, 1, 1, 1, 4]
def baseStart_6264941 : Nat := 118140960795 + 6264941 * 2 ^ 59
def prefixEnd_6264941 : Nat := 4983230072969 + 3 ^ 40 * 6264941 * 2
def baseEnd_6264941 : Nat := 3216926005059478123225567

theorem tailTrace_6264941 : CollatzResearch.WordTrace tailWord_6264941 prefixEnd_6264941 3216926005059478123225567 := by
  unfold tailWord_6264941
  simp only [CollatzResearch.WordTrace]
  refine ⟨228501170396196198583506677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152334113597464132389004451 228501170396196198583506677)
  ·
    refine ⟨21421984724643393617203751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 228501170396196198583506677 21421984724643393617203751)
    ·
      refine ⟨32132977086965090425805627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21421984724643393617203751 32132977086965090425805627)
      ·
        refine ⟨48199465630447635638708441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32132977086965090425805627 48199465630447635638708441)
        ·
          refine ⟨36149599222835726729031331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48199465630447635638708441 36149599222835726729031331)
          ·
            refine ⟨54224398834253590093546997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36149599222835726729031331 54224398834253590093546997)
            ·
              refine ⟨5083537390711274071270031, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 54224398834253590093546997 5083537390711274071270031)
              ·
                refine ⟨7625306086066911106905047, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5083537390711274071270031 7625306086066911106905047)
                ·
                  refine ⟨11437959129100366660357571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7625306086066911106905047 11437959129100366660357571)
                  ·
                    refine ⟨17156938693650549990536357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11437959129100366660357571 17156938693650549990536357)
                    ·
                      refine ⟨3216926005059478123225567, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17156938693650549990536357 3216926005059478123225567)
                      ·
                        rfl

theorem cell23_6264941_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 5, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 5, 1, 1, 1, 4].length) (baseStart_6264941 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6264941 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6264941 prefixEnd_6264941 := by exact prefixLift 6264941
  have htrace : WordTrace (prefixWord ++ tailWord_6264941) baseStart_6264941 baseEnd_6264941 := by
    simpa [prefixWord, tailWord_6264941, baseEnd_6264941] using wordTrace_append hprefix tailTrace_6264941
  have hstable : (prefixWord ++ tailWord_6264941).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6264941).length < 2 ^ (prefixWord ++ tailWord_6264941).sum := by decide
  have hdescent : baseEnd_6264941 < baseStart_6264941 := by decide
  rcases family_descends (prefixWord ++ tailWord_6264941) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6264944 : List Nat := [2, 1, 1, 1, 5, 4, 1, 1, 1, 1, 5]
def baseStart_6264944 : Nat := 118140960795 + 6264944 * 2 ^ 59
def prefixEnd_6264944 : Nat := 4983230072969 + 3 ^ 40 * 6264944 * 2
def baseEnd_6264944 : Nat := 3216927545501441611488053

theorem tailTrace_6264944 : CollatzResearch.WordTrace tailWord_6264944 prefixEnd_6264944 3216927545501441611488053 := by
  unfold tailWord_6264944
  simp only [CollatzResearch.WordTrace]
  refine ⟨114250639907592665047932943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 152334186543456886730577257 114250639907592665047932943)
  ·
    refine ⟨171375959861388997571899415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114250639907592665047932943 171375959861388997571899415)
    ·
      refine ⟨257063939792083496357849123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 171375959861388997571899415 257063939792083496357849123)
      ·
        refine ⟨385595909688125244536773685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 257063939792083496357849123 385595909688125244536773685)
        ·
          refine ⟨36149616533261741675322533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 385595909688125244536773685 36149616533261741675322533)
          ·
            refine ⟨6778053099986576564122975, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 36149616533261741675322533 6778053099986576564122975)
            ·
              refine ⟨10167079649979864846184463, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6778053099986576564122975 10167079649979864846184463)
              ·
                refine ⟨15250619474969797269276695, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10167079649979864846184463 15250619474969797269276695)
                ·
                  refine ⟨22875929212454695903915043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15250619474969797269276695 22875929212454695903915043)
                  ·
                    refine ⟨34313893818682043855872565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 22875929212454695903915043 34313893818682043855872565)
                    ·
                      refine ⟨3216927545501441611488053, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 34313893818682043855872565 3216927545501441611488053)
                      ·
                        rfl

theorem cell23_6264944_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 4, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 4, 1, 1, 1, 1, 5].length) (baseStart_6264944 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6264944 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6264944 prefixEnd_6264944 := by exact prefixLift 6264944
  have htrace : WordTrace (prefixWord ++ tailWord_6264944) baseStart_6264944 baseEnd_6264944 := by
    simpa [prefixWord, tailWord_6264944, baseEnd_6264944] using wordTrace_append hprefix tailTrace_6264944
  have hstable : (prefixWord ++ tailWord_6264944).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6264944).length < 2 ^ (prefixWord ++ tailWord_6264944).sum := by decide
  have hdescent : baseEnd_6264944 < baseStart_6264944 := by decide
  rcases family_descends (prefixWord ++ tailWord_6264944) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6265025 : List Nat := [1, 2, 6, 1, 3, 1, 1, 1, 1, 3, 3]
def baseStart_6265025 : Nat := 118140960795 + 6265025 * 2 ^ 59
def prefixEnd_6265025 : Nat := 4983230072969 + 3 ^ 40 * 6265025 * 2
def baseEnd_6265025 : Nat := 3216969137434455794575181

theorem tailTrace_6265025 : CollatzResearch.WordTrace tailWord_6265025 prefixEnd_6265025 3216969137434455794575181 := by
  unfold tailWord_6265025
  simp only [CollatzResearch.WordTrace]
  refine ⟨228504234127891880929564529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152336156085261253953043019 228504234127891880929564529)
  ·
    refine ⟨171378175595918910697173397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 228504234127891880929564529 171378175595918910697173397)
    ·
      refine ⟨8033351981058698938930003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 171378175595918910697173397 8033351981058698938930003)
      ·
        refine ⟨12050027971588048408395005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8033351981058698938930003 12050027971588048408395005)
        ·
          refine ⟨4518760489345518153148127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12050027971588048408395005 4518760489345518153148127)
          ·
            refine ⟨6778140734018277229722191, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4518760489345518153148127 6778140734018277229722191)
            ·
              refine ⟨10167211101027415844583287, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6778140734018277229722191 10167211101027415844583287)
              ·
                refine ⟨15250816651541123766874931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10167211101027415844583287 15250816651541123766874931)
                ·
                  refine ⟨22876224977311685650312397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15250816651541123766874931 22876224977311685650312397)
                  ·
                    refine ⟨8578584366491882118867149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 22876224977311685650312397 8578584366491882118867149)
                    ·
                      refine ⟨3216969137434455794575181, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8578584366491882118867149 3216969137434455794575181)
                      ·
                        rfl

theorem cell23_6265025_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 3, 1, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 3, 1, 1, 1, 1, 3, 3].length) (baseStart_6265025 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6265025 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6265025 prefixEnd_6265025 := by exact prefixLift 6265025
  have htrace : WordTrace (prefixWord ++ tailWord_6265025) baseStart_6265025 baseEnd_6265025 := by
    simpa [prefixWord, tailWord_6265025, baseEnd_6265025] using wordTrace_append hprefix tailTrace_6265025
  have hstable : (prefixWord ++ tailWord_6265025).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6265025).length < 2 ^ (prefixWord ++ tailWord_6265025).sum := by decide
  have hdescent : baseEnd_6265025 < baseStart_6265025 := by decide
  rcases family_descends (prefixWord ++ tailWord_6265025) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6265118 : List Nat := [4, 3, 2, 1, 1, 1, 2, 2, 2, 5]
def baseStart_6265118 : Nat := 118140960795 + 6265118 * 2 ^ 59
def prefixEnd_6265118 : Nat := 4983230072969 + 3 ^ 40 * 6265118 * 2
def baseEnd_6265118 : Nat := 1072338963711774643570751

theorem tailTrace_6265118 : CollatzResearch.WordTrace tailWord_6265118 prefixEnd_6265118 1072338963711774643570751 := by
  unfold tailWord_6265118
  simp only [CollatzResearch.WordTrace]
  refine ⟨28563453264569369726587501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 152338417411036638541800005 28563453264569369726587501)
  ·
    refine ⟨10711294974213513647470313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 28563453264569369726587501 10711294974213513647470313)
    ·
      refine ⟨8033471230660135235602735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10711294974213513647470313 8033471230660135235602735)
      ·
        refine ⟨12050206845990202853404103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8033471230660135235602735 12050206845990202853404103)
        ·
          refine ⟨18075310268985304280106155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12050206845990202853404103 18075310268985304280106155)
          ·
            refine ⟨27112965403477956420159233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18075310268985304280106155 27112965403477956420159233)
            ·
              refine ⟨20334724052608467315119425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27112965403477956420159233 20334724052608467315119425)
              ·
                refine ⟨15251043039456350486339569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20334724052608467315119425 15251043039456350486339569)
                ·
                  refine ⟨11438282279592262864754677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15251043039456350486339569 11438282279592262864754677)
                  ·
                    refine ⟨1072338963711774643570751, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11438282279592262864754677 1072338963711774643570751)
                    ·
                      rfl

theorem cell23_6265118_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 1, 2, 2, 2, 5].length) (baseStart_6265118 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6265118 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6265118 prefixEnd_6265118 := by exact prefixLift 6265118
  have htrace : WordTrace (prefixWord ++ tailWord_6265118) baseStart_6265118 baseEnd_6265118 := by
    simpa [prefixWord, tailWord_6265118, baseEnd_6265118] using wordTrace_append hprefix tailTrace_6265118
  have hstable : (prefixWord ++ tailWord_6265118).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6265118).length < 2 ^ (prefixWord ++ tailWord_6265118).sum := by decide
  have hdescent : baseEnd_6265118 < baseStart_6265118 := by decide
  rcases family_descends (prefixWord ++ tailWord_6265118) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6265138 : List Nat := [3, 2, 1, 1, 5, 1, 1, 1, 2, 4, 2]
def baseStart_6265138 : Nat := 118140960795 + 6265138 * 2 ^ 59
def prefixEnd_6265138 : Nat := 4983230072969 + 3 ^ 40 * 6265138 * 2
def baseEnd_6265138 : Nat := 3217027160748413852462161

theorem tailTrace_6265138 : CollatzResearch.WordTrace tailWord_6265138 prefixEnd_6265138 3217027160748413852462161 := by
  unfold tailWord_6265138
  simp only [CollatzResearch.WordTrace]
  refine ⟨57127088894120625307107017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 152338903717655000818952045 57127088894120625307107017)
  ·
    refine ⟨42845316670590468980330263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57127088894120625307107017 42845316670590468980330263)
    ·
      refine ⟨64267975005885703470495395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42845316670590468980330263 64267975005885703470495395)
      ·
        refine ⟨96401962508828555205743093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64267975005885703470495395 96401962508828555205743093)
        ·
          refine ⟨9037683985202677050538415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 96401962508828555205743093 9037683985202677050538415)
          ·
            refine ⟨13556525977804015575807623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9037683985202677050538415 13556525977804015575807623)
            ·
              refine ⟨20334788966706023363711435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13556525977804015575807623 20334788966706023363711435)
              ·
                refine ⟨30502183450059035045567153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20334788966706023363711435 30502183450059035045567153)
                ·
                  refine ⟨22876637587544276284175365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 30502183450059035045567153 22876637587544276284175365)
                  ·
                    refine ⟨4289369547664551803282881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 22876637587544276284175365 4289369547664551803282881)
                    ·
                      refine ⟨3217027160748413852462161, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4289369547664551803282881 3217027160748413852462161)
                      ·
                        rfl

theorem cell23_6265138_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 5, 1, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 5, 1, 1, 1, 2, 4, 2].length) (baseStart_6265138 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6265138 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6265138 prefixEnd_6265138 := by exact prefixLift 6265138
  have htrace : WordTrace (prefixWord ++ tailWord_6265138) baseStart_6265138 baseEnd_6265138 := by
    simpa [prefixWord, tailWord_6265138, baseEnd_6265138] using wordTrace_append hprefix tailTrace_6265138
  have hstable : (prefixWord ++ tailWord_6265138).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6265138).length < 2 ^ (prefixWord ++ tailWord_6265138).sum := by decide
  have hdescent : baseEnd_6265138 < baseStart_6265138 := by decide
  rcases family_descends (prefixWord ++ tailWord_6265138) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6265144 : List Nat := [2, 1, 2, 1, 3, 1, 4, 3, 6]
def baseStart_6265144 : Nat := 118140960795 + 6265144 * 2 ^ 59
def prefixEnd_6265144 : Nat := 4983230072969 + 3 ^ 40 * 6265144 * 2
def baseEnd_6265144 : Nat := 357447804625815647665237

theorem tailTrace_6265144 : CollatzResearch.WordTrace tailWord_6265144 prefixEnd_6265144 357447804625815647665237 := by
  unfold tailWord_6265144
  simp only [CollatzResearch.WordTrace]
  refine ⟨114254287207230382126573243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 152339049609640509502097657 114254287207230382126573243)
  ·
    refine ⟨171381430810845573189859865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114254287207230382126573243 171381430810845573189859865)
    ·
      refine ⟨128536073108134179892394899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 171381430810845573189859865 128536073108134179892394899)
      ·
        refine ⟨192804109662201269838592349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 128536073108134179892394899 192804109662201269838592349)
        ·
          refine ⟨72301541123325476189472131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 192804109662201269838592349 72301541123325476189472131)
          ·
            refine ⟨108452311684988214284208197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 72301541123325476189472131 108452311684988214284208197)
            ·
              refine ⟨20334808440935290178289037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 108452311684988214284208197 20334808440935290178289037)
              ·
                refine ⟨7625553165350733816858389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20334808440935290178289037 7625553165350733816858389)
                ·
                  refine ⟨357447804625815647665237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7625553165350733816858389 357447804625815647665237)
                  ·
                    rfl

theorem cell23_6265144_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 4, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 4, 3, 6].length) (baseStart_6265144 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6265144 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6265144 prefixEnd_6265144 := by exact prefixLift 6265144
  have htrace : WordTrace (prefixWord ++ tailWord_6265144) baseStart_6265144 baseEnd_6265144 := by
    simpa [prefixWord, tailWord_6265144, baseEnd_6265144] using wordTrace_append hprefix tailTrace_6265144
  have hstable : (prefixWord ++ tailWord_6265144).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6265144).length < 2 ^ (prefixWord ++ tailWord_6265144).sum := by decide
  have hdescent : baseEnd_6265144 < baseStart_6265144 := by decide
  rcases family_descends (prefixWord ++ tailWord_6265144) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6265188 : List Nat := [2, 3, 1, 1, 3, 1, 4, 1, 3, 1, 3]
def baseStart_6265188 : Nat := 118140960795 + 6265188 * 2 ^ 59
def prefixEnd_6265188 : Nat := 4983230072969 + 3 ^ 40 * 6265188 * 2
def baseEnd_6265188 : Nat := 3217052834781138656836931

theorem tailTrace_6265188 : CollatzResearch.WordTrace tailWord_6265188 prefixEnd_6265188 3217052834781138656836931 := by
  unfold tailWord_6265188
  simp only [CollatzResearch.WordTrace]
  refine ⟨114255089613150679883874109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 152340119484200906511832145 114255089613150679883874109)
  ·
    refine ⟨42845658604931504956452791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 114255089613150679883874109 42845658604931504956452791)
    ·
      refine ⟨64268487907397257434679187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42845658604931504956452791 64268487907397257434679187)
      ·
        refine ⟨96402731861095886152018781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64268487907397257434679187 96402731861095886152018781)
        ·
          refine ⟨36151024447910957307007043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 96402731861095886152018781 36151024447910957307007043)
          ·
            refine ⟨54226536671866435960510565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36151024447910957307007043 54226536671866435960510565)
            ·
              refine ⟨10167475625974956742595731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 54226536671866435960510565 10167475625974956742595731)
              ·
                refine ⟨15251213438962435113893597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10167475625974956742595731 15251213438962435113893597)
                ·
                  refine ⟨5719205039610913167710099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15251213438962435113893597 5719205039610913167710099)
                  ·
                    refine ⟨8578807559416369751565149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5719205039610913167710099 8578807559416369751565149)
                    ·
                      refine ⟨3217052834781138656836931, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8578807559416369751565149 3217052834781138656836931)
                      ·
                        rfl

theorem cell23_6265188_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 4, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 4, 1, 3, 1, 3].length) (baseStart_6265188 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6265188 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6265188 prefixEnd_6265188 := by exact prefixLift 6265188
  have htrace : WordTrace (prefixWord ++ tailWord_6265188) baseStart_6265188 baseEnd_6265188 := by
    simpa [prefixWord, tailWord_6265188, baseEnd_6265188] using wordTrace_append hprefix tailTrace_6265188
  have hstable : (prefixWord ++ tailWord_6265188).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6265188).length < 2 ^ (prefixWord ++ tailWord_6265188).sum := by decide
  have hdescent : baseEnd_6265188 < baseStart_6265188 := by decide
  rcases family_descends (prefixWord ++ tailWord_6265188) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6265211 : List Nat := [1, 1, 1, 1, 1, 7, 1, 4, 1, 1, 4]
def baseStart_6265211 : Nat := 118140960795 + 6265211 * 2 ^ 59
def prefixEnd_6265211 : Nat := 4983230072969 + 3 ^ 40 * 6265211 * 2
def baseEnd_6265211 : Nat := 3217064644836192066849325

theorem tailTrace_6265211 : CollatzResearch.WordTrace tailWord_6265211 prefixEnd_6265211 3217064644836192066849325 := by
  unfold tailWord_6265211
  simp only [CollatzResearch.WordTrace]
  refine ⟨228511018105218034695835487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152340678736812023130556991 228511018105218034695835487)
  ·
    refine ⟨342766527157827052043753231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 228511018105218034695835487 342766527157827052043753231)
    ·
      refine ⟨514149790736740578065629847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 342766527157827052043753231 514149790736740578065629847)
      ·
        refine ⟨771224686105110867098444771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 514149790736740578065629847 771224686105110867098444771)
        ·
          refine ⟨1156837029157666300647667157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 771224686105110867098444771 1156837029157666300647667157)
          ·
            refine ⟨27113367870882803921429699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 1156837029157666300647667157 27113367870882803921429699)
            ·
              refine ⟨40670051806324205882144549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27113367870882803921429699 40670051806324205882144549)
              ·
                refine ⟨7625634713685788602902103, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 40670051806324205882144549 7625634713685788602902103)
                ·
                  refine ⟨11438452070528682904353155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7625634713685788602902103 11438452070528682904353155)
                  ·
                    refine ⟨17157678105793024356529733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11438452070528682904353155 17157678105793024356529733)
                    ·
                      refine ⟨3217064644836192066849325, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17157678105793024356529733 3217064644836192066849325)
                      ·
                        rfl

theorem cell23_6265211_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 7, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 7, 1, 4, 1, 1, 4].length) (baseStart_6265211 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6265211 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6265211 prefixEnd_6265211 := by exact prefixLift 6265211
  have htrace : WordTrace (prefixWord ++ tailWord_6265211) baseStart_6265211 baseEnd_6265211 := by
    simpa [prefixWord, tailWord_6265211, baseEnd_6265211] using wordTrace_append hprefix tailTrace_6265211
  have hstable : (prefixWord ++ tailWord_6265211).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6265211).length < 2 ^ (prefixWord ++ tailWord_6265211).sum := by decide
  have hdescent : baseEnd_6265211 < baseStart_6265211 := by decide
  rcases family_descends (prefixWord ++ tailWord_6265211) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6265255 : List Nat := [1, 1, 6, 1, 1, 2, 4, 1, 2, 4]
def baseStart_6265255 : Nat := 118140960795 + 6265255 * 2 ^ 59
def prefixEnd_6265255 : Nat := 4983230072969 + 3 ^ 40 * 6265255 * 2
def baseEnd_6265255 : Nat := 1072362412661663298233041

theorem tailTrace_6265255 : CollatzResearch.WordTrace tailWord_6265255 prefixEnd_6265255 1072362412661663298233041 := by
  unfold tailWord_6265255
  simp only [CollatzResearch.WordTrace]
  refine ⟨228512622917058630210437219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152341748611372420140291479 228512622917058630210437219)
  ·
    refine ⟨342768934375587945315655829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 228512622917058630210437219 342768934375587945315655829)
    ·
      refine ⟨16067293798855684936671367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 342768934375587945315655829 16067293798855684936671367)
      ·
        refine ⟨24100940698283527405007051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16067293798855684936671367 24100940698283527405007051)
        ·
          refine ⟨36151411047425291107510577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24100940698283527405007051 36151411047425291107510577)
          ·
            refine ⟨27113558285568968330632933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36151411047425291107510577 27113558285568968330632933)
            ·
              refine ⟨5083792178544181561993675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 27113558285568968330632933 5083792178544181561993675)
              ·
                refine ⟨7625688267816272342990513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5083792178544181561993675 7625688267816272342990513)
                ·
                  refine ⟨5719266200862204257242885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7625688267816272342990513 5719266200862204257242885)
                  ·
                    refine ⟨1072362412661663298233041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5719266200862204257242885 1072362412661663298233041)
                    ·
                      rfl

theorem cell23_6265255_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 2, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 2, 4, 1, 2, 4].length) (baseStart_6265255 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6265255 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6265255 prefixEnd_6265255 := by exact prefixLift 6265255
  have htrace : WordTrace (prefixWord ++ tailWord_6265255) baseStart_6265255 baseEnd_6265255 := by
    simpa [prefixWord, tailWord_6265255, baseEnd_6265255] using wordTrace_append hprefix tailTrace_6265255
  have hstable : (prefixWord ++ tailWord_6265255).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6265255).length < 2 ^ (prefixWord ++ tailWord_6265255).sum := by decide
  have hdescent : baseEnd_6265255 < baseStart_6265255 := by decide
  rcases family_descends (prefixWord ++ tailWord_6265255) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6265265 : List Nat := [1, 2, 2, 4, 1, 4, 1, 2, 1, 2, 3]
def baseStart_6265265 : Nat := 118140960795 + 6265265 * 2 ^ 59
def prefixEnd_6265265 : Nat := 4983230072969 + 3 ^ 40 * 6265265 * 2
def baseEnd_6265265 : Nat := 3217092372791534855574077

theorem tailTrace_6265265 : CollatzResearch.WordTrace tailWord_6265265 prefixEnd_6265265 3217092372791534855574077 := by
  unfold tailWord_6265265
  simp only [CollatzResearch.WordTrace]
  refine ⟨228512987647022401918301249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152341991764681601278867499 228512987647022401918301249)
  ·
    refine ⟨171384740735266801438725937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 228512987647022401918301249 171384740735266801438725937)
    ·
      refine ⟨128538555551450101079044453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 171384740735266801438725937 128538555551450101079044453)
      ·
        refine ⟨24100979165896893952320835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 128538555551450101079044453 24100979165896893952320835)
        ·
          refine ⟨36151468748845340928481253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24100979165896893952320835 36151468748845340928481253)
          ·
            refine ⟨6778400390408501424090235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 36151468748845340928481253 6778400390408501424090235)
            ·
              refine ⟨10167600585612752136135353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6778400390408501424090235 10167600585612752136135353)
              ·
                refine ⟨7625700439209564102101515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10167600585612752136135353 7625700439209564102101515)
                ·
                  refine ⟨11438550658814346153152273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7625700439209564102101515 11438550658814346153152273)
                  ·
                    refine ⟨8578912994110759614864205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11438550658814346153152273 8578912994110759614864205)
                    ·
                      refine ⟨3217092372791534855574077, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8578912994110759614864205 3217092372791534855574077)
                      ·
                        rfl

theorem cell23_6265265_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 4, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 4, 1, 2, 1, 2, 3].length) (baseStart_6265265 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6265265 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6265265 prefixEnd_6265265 := by exact prefixLift 6265265
  have htrace : WordTrace (prefixWord ++ tailWord_6265265) baseStart_6265265 baseEnd_6265265 := by
    simpa [prefixWord, tailWord_6265265, baseEnd_6265265] using wordTrace_append hprefix tailTrace_6265265
  have hstable : (prefixWord ++ tailWord_6265265).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6265265).length < 2 ^ (prefixWord ++ tailWord_6265265).sum := by decide
  have hdescent : baseEnd_6265265 < baseStart_6265265 := by decide
  rcases family_descends (prefixWord ++ tailWord_6265265) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6265274 : List Nat := [3, 1, 1, 1, 2, 1, 1, 3, 1, 4, 5]
def baseStart_6265274 : Nat := 118140960795 + 6265274 * 2 ^ 59
def prefixEnd_6265274 : Nat := 4983230072969 + 3 ^ 40 * 6265274 * 2
def baseEnd_6265274 : Nat := 3217096994117425320361535

theorem tailTrace_6265274 : CollatzResearch.WordTrace tailWord_6265274 prefixEnd_6265274 3217096994117425320361535 := by
  unfold tailWord_6265274
  simp only [CollatzResearch.WordTrace]
  refine ⟨57128328975997449113844719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 152342210602659864303585917 57128328975997449113844719)
  ·
    refine ⟨85692493463996173670767079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57128328975997449113844719 85692493463996173670767079)
    ·
      refine ⟨128538740195994260506150619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85692493463996173670767079 128538740195994260506150619)
      ·
        refine ⟨192808110293991390759225929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 128538740195994260506150619 192808110293991390759225929)
        ·
          refine ⟨144606082720493543069419447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 192808110293991390759225929 144606082720493543069419447)
          ·
            refine ⟨216909124080740314604129171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 144606082720493543069419447 216909124080740314604129171)
            ·
              refine ⟨325363686121110471906193757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 216909124080740314604129171 325363686121110471906193757)
              ·
                refine ⟨122011382295416426964822659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 325363686121110471906193757 122011382295416426964822659)
                ·
                  refine ⟨183017073443124640447233989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 122011382295416426964822659 183017073443124640447233989)
                  ·
                    refine ⟨34315701270585870083856373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 183017073443124640447233989 34315701270585870083856373)
                    ·
                      refine ⟨3217096994117425320361535, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 34315701270585870083856373 3217096994117425320361535)
                      ·
                        rfl

theorem cell23_6265274_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 1, 3, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 1, 3, 1, 4, 5].length) (baseStart_6265274 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6265274 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6265274 prefixEnd_6265274 := by exact prefixLift 6265274
  have htrace : WordTrace (prefixWord ++ tailWord_6265274) baseStart_6265274 baseEnd_6265274 := by
    simpa [prefixWord, tailWord_6265274, baseEnd_6265274] using wordTrace_append hprefix tailTrace_6265274
  have hstable : (prefixWord ++ tailWord_6265274).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6265274).length < 2 ^ (prefixWord ++ tailWord_6265274).sum := by decide
  have hdescent : baseEnd_6265274 < baseStart_6265274 := by decide
  rcases family_descends (prefixWord ++ tailWord_6265274) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6265278 : List Nat := [4, 2, 1, 1, 1, 1, 2, 1, 6, 1, 3]
def baseStart_6265278 : Nat := 118140960795 + 6265278 * 2 ^ 59
def prefixEnd_6265278 : Nat := 4983230072969 + 3 ^ 40 * 6265278 * 2
def baseEnd_6265278 : Nat := 3217099048040043304711517

theorem tailTrace_6265278 : CollatzResearch.WordTrace tailWord_6265278 prefixEnd_6265278 3217099048040043304711517 := by
  unfold tailWord_6265278
  simp only [CollatzResearch.WordTrace]
  refine ⟨28564182724496913142315561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 152342307863983536759016325 28564182724496913142315561)
  ·
    refine ⟨21423137043372684856736671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28564182724496913142315561 21423137043372684856736671)
    ·
      refine ⟨32134705565059027285105007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21423137043372684856736671 32134705565059027285105007)
      ·
        refine ⟨48202058347588540927657511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32134705565059027285105007 48202058347588540927657511)
        ·
          refine ⟨72303087521382811391486267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48202058347588540927657511 72303087521382811391486267)
          ·
            refine ⟨108454631282074217087229401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 72303087521382811391486267 108454631282074217087229401)
            ·
              refine ⟨81340973461555662815422051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 108454631282074217087229401 81340973461555662815422051)
              ·
                refine ⟨122011460192333494223133077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 81340973461555662815422051 122011460192333494223133077)
                ·
                  refine ⟨5719287196515632541709363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 122011460192333494223133077 5719287196515632541709363)
                  ·
                    refine ⟨8578930794773448812564045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5719287196515632541709363 8578930794773448812564045)
                    ·
                      refine ⟨3217099048040043304711517, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8578930794773448812564045 3217099048040043304711517)
                      ·
                        rfl

theorem cell23_6265278_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 2, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 2, 1, 6, 1, 3].length) (baseStart_6265278 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6265278 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6265278 prefixEnd_6265278 := by exact prefixLift 6265278
  have htrace : WordTrace (prefixWord ++ tailWord_6265278) baseStart_6265278 baseEnd_6265278 := by
    simpa [prefixWord, tailWord_6265278, baseEnd_6265278] using wordTrace_append hprefix tailTrace_6265278
  have hstable : (prefixWord ++ tailWord_6265278).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6265278).length < 2 ^ (prefixWord ++ tailWord_6265278).sum := by decide
  have hdescent : baseEnd_6265278 < baseStart_6265278 := by decide
  rcases family_descends (prefixWord ++ tailWord_6265278) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6265301 : List Nat := [1, 3, 2, 3, 1, 2, 1, 1, 2, 3, 4]
def baseStart_6265301 : Nat := 118140960795 + 6265301 * 2 ^ 59
def prefixEnd_6265301 : Nat := 4983230072969 + 3 ^ 40 * 6265301 * 2
def baseEnd_6265301 : Nat := 3217110858095096714723911

theorem tailTrace_6265301 : CollatzResearch.WordTrace tailWord_6265301 prefixEnd_6265301 3217110858095096714723911 := by
  unfold tailWord_6265301
  simp only [CollatzResearch.WordTrace]
  refine ⟨228514300674891980066611757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152342867116594653377741171 228514300674891980066611757)
  ·
    refine ⟨85692862753084492524979409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 228514300674891980066611757 85692862753084492524979409)
    ·
      refine ⟨64269647064813369393734557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 85692862753084492524979409 64269647064813369393734557)
      ·
        refine ⟨24101117649305013522650459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 64269647064813369393734557 24101117649305013522650459)
        ·
          refine ⟨36151676473957520283975689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24101117649305013522650459 36151676473957520283975689)
          ·
            refine ⟨27113757355468140212981767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36151676473957520283975689 27113757355468140212981767)
            ·
              refine ⟨40670636033202210319472651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27113757355468140212981767 40670636033202210319472651)
              ·
                refine ⟨61005954049803315479208977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40670636033202210319472651 61005954049803315479208977)
                ·
                  refine ⟨45754465537352486609406733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 61005954049803315479208977 45754465537352486609406733)
                  ·
                    refine ⟨17157924576507182478527525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 45754465537352486609406733 17157924576507182478527525)
                    ·
                      refine ⟨3217110858095096714723911, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17157924576507182478527525 3217110858095096714723911)
                      ·
                        rfl

theorem cell23_6265301_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 2, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 2, 1, 1, 2, 3, 4].length) (baseStart_6265301 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6265301 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6265301 prefixEnd_6265301 := by exact prefixLift 6265301
  have htrace : WordTrace (prefixWord ++ tailWord_6265301) baseStart_6265301 baseEnd_6265301 := by
    simpa [prefixWord, tailWord_6265301, baseEnd_6265301] using wordTrace_append hprefix tailTrace_6265301
  have hstable : (prefixWord ++ tailWord_6265301).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6265301).length < 2 ^ (prefixWord ++ tailWord_6265301).sum := by decide
  have hdescent : baseEnd_6265301 < baseStart_6265301 := by decide
  rcases family_descends (prefixWord ++ tailWord_6265301) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6265311 : List Nat := [1, 1, 2, 3, 3, 3, 1, 1, 2, 6]
def baseStart_6265311 : Nat := 118140960795 + 6265311 * 2 ^ 59
def prefixEnd_6265311 : Nat := 4983230072969 + 3 ^ 40 * 6265311 * 2
def baseEnd_6265311 : Nat := 1072371997633880558532955

theorem tailTrace_6265311 : CollatzResearch.WordTrace tailWord_6265311 prefixEnd_6265311 1072371997633880558532955 := by
  unfold tailWord_6265311
  simp only [CollatzResearch.WordTrace]
  refine ⟨228514665404855751774475787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152343110269903834516317191 228514665404855751774475787)
  ·
    refine ⟨342771998107283627661713681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 228514665404855751774475787 342771998107283627661713681)
    ·
      refine ⟨257078998580462720746285261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 342771998107283627661713681 257078998580462720746285261)
      ·
        refine ⟨96404624467673520279856973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 257078998580462720746285261 96404624467673520279856973)
        ·
          refine ⟨36151734175377570104946365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 96404624467673520279856973 36151734175377570104946365)
          ·
            refine ⟨13556900315766588789354887, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 36151734175377570104946365 13556900315766588789354887)
            ·
              refine ⟨20335350473649883184032331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13556900315766588789354887 20335350473649883184032331)
              ·
                refine ⟨30503025710474824776048497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20335350473649883184032331 30503025710474824776048497)
                ·
                  refine ⟨22877269282856118582036373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 30503025710474824776048497 22877269282856118582036373)
                  ·
                    refine ⟨1072371997633880558532955, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 22877269282856118582036373 1072371997633880558532955)
                    ·
                      rfl

theorem cell23_6265311_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 3, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 3, 1, 1, 2, 6].length) (baseStart_6265311 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6265311 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6265311 prefixEnd_6265311 := by exact prefixLift 6265311
  have htrace : WordTrace (prefixWord ++ tailWord_6265311) baseStart_6265311 baseEnd_6265311 := by
    simpa [prefixWord, tailWord_6265311, baseEnd_6265311] using wordTrace_append hprefix tailTrace_6265311
  have hstable : (prefixWord ++ tailWord_6265311).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6265311).length < 2 ^ (prefixWord ++ tailWord_6265311).sum := by decide
  have hdescent : baseEnd_6265311 < baseStart_6265311 := by decide
  rcases family_descends (prefixWord ++ tailWord_6265311) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6265346 : List Nat := [3, 4, 1, 2, 3, 1, 1, 2, 2, 1, 3]
def baseStart_6265346 : Nat := 118140960795 + 6265346 * 2 ^ 59
def prefixEnd_6265346 : Nat := 4983230072969 + 3 ^ 40 * 6265346 * 2
def baseEnd_6265346 : Nat := 3217133964724549038661205

theorem tailTrace_6265346 : CollatzResearch.WordTrace tailWord_6265346 prefixEnd_6265346 3217133964724549038661205 := by
  unfold tailWord_6265346
  simp only [CollatzResearch.WordTrace]
  refine ⟨57128985489932238187999973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 152343961306485968501333261 57128985489932238187999973)
  ·
    refine ⟨10711684779362294660249995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 57128985489932238187999973 10711684779362294660249995)
    ·
      refine ⟨16067527169043441990374993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10711684779362294660249995 16067527169043441990374993)
      ·
        refine ⟨12050645376782581492781245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16067527169043441990374993 12050645376782581492781245)
        ·
          refine ⟨4518992016293468059792967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12050645376782581492781245 4518992016293468059792967)
          ·
            refine ⟨6778488024440202089689451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4518992016293468059792967 6778488024440202089689451)
            ·
              refine ⟨10167732036660303134534177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6778488024440202089689451 10167732036660303134534177)
              ·
                refine ⟨7625799027495227350900633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10167732036660303134534177 7625799027495227350900633)
                ·
                  refine ⟨5719349270621420513175475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7625799027495227350900633 5719349270621420513175475)
                  ·
                    refine ⟨8579023905932130769763213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5719349270621420513175475 8579023905932130769763213)
                    ·
                      refine ⟨3217133964724549038661205, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8579023905932130769763213 3217133964724549038661205)
                      ·
                        rfl

theorem cell23_6265346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 3, 1, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 3, 1, 1, 2, 2, 1, 3].length) (baseStart_6265346 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6265346 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6265346 prefixEnd_6265346 := by exact prefixLift 6265346
  have htrace : WordTrace (prefixWord ++ tailWord_6265346) baseStart_6265346 baseEnd_6265346 := by
    simpa [prefixWord, tailWord_6265346, baseEnd_6265346] using wordTrace_append hprefix tailTrace_6265346
  have hstable : (prefixWord ++ tailWord_6265346).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6265346).length < 2 ^ (prefixWord ++ tailWord_6265346).sum := by decide
  have hdescent : baseEnd_6265346 < baseStart_6265346 := by decide
  rcases family_descends (prefixWord ++ tailWord_6265346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6265348 : List Nat := [2, 3, 2, 3, 1, 1, 1, 2, 2, 2, 4]
def baseStart_6265348 : Nat := 118140960795 + 6265348 * 2 ^ 59
def prefixEnd_6265348 : Nat := 4983230072969 + 3 ^ 40 * 6265348 * 2
def baseEnd_6265348 : Nat := 3217134991685858030836195

theorem tailTrace_6265348 : CollatzResearch.WordTrace tailWord_6265348 prefixEnd_6265348 3217134991685858030836195 := by
  unfold tailWord_6265348
  simp only [CollatzResearch.WordTrace]
  refine ⟨114258007452860853546786349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 152344009937147804729048465 114258007452860853546786349)
  ·
    refine ⟨42846752794822820080044881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 114258007452860853546786349 42846752794822820080044881)
    ·
      refine ⟨32135064596117115060033661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42846752794822820080044881 32135064596117115060033661)
      ·
        refine ⟨12050649223543918147512623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 32135064596117115060033661 12050649223543918147512623)
        ·
          refine ⟨18075973835315877221268935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12050649223543918147512623 18075973835315877221268935)
          ·
            refine ⟨27113960752973815831903403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18075973835315877221268935 27113960752973815831903403)
            ·
              refine ⟨40670941129460723747855105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27113960752973815831903403 40670941129460723747855105)
              ·
                refine ⟨30503205847095542810891329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 40670941129460723747855105 30503205847095542810891329)
                ·
                  refine ⟨22877404385321657108168497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 30503205847095542810891329 22877404385321657108168497)
                  ·
                    refine ⟨17158053288991242831126373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 22877404385321657108168497 17158053288991242831126373)
                    ·
                      refine ⟨3217134991685858030836195, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17158053288991242831126373 3217134991685858030836195)
                      ·
                        rfl

theorem cell23_6265348_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 1, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 1, 1, 2, 2, 2, 4].length) (baseStart_6265348 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6265348 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6265348 prefixEnd_6265348 := by exact prefixLift 6265348
  have htrace : WordTrace (prefixWord ++ tailWord_6265348) baseStart_6265348 baseEnd_6265348 := by
    simpa [prefixWord, tailWord_6265348, baseEnd_6265348] using wordTrace_append hprefix tailTrace_6265348
  have hstable : (prefixWord ++ tailWord_6265348).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6265348).length < 2 ^ (prefixWord ++ tailWord_6265348).sum := by decide
  have hdescent : baseEnd_6265348 < baseStart_6265348 := by decide
  rcases family_descends (prefixWord ++ tailWord_6265348) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6265358 : List Nat := [4, 1, 1, 2, 3, 2, 2, 1, 7]
def baseStart_6265358 : Nat := 118140960795 + 6265358 * 2 ^ 59
def prefixEnd_6265358 : Nat := 4983230072969 + 3 ^ 40 * 6265358 * 2
def baseEnd_6265358 : Nat := 357460014054711443523461

theorem tailTrace_6265358 : CollatzResearch.WordTrace tailWord_6265358 prefixEnd_6265358 357460014054711443523461 := by
  unfold tailWord_6265358
  simp only [CollatzResearch.WordTrace]
  refine ⟨28564547454460684850179591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 152344253090456985867624485 28564547454460684850179591)
  ·
    refine ⟨42846821181691027275269387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28564547454460684850179591 42846821181691027275269387)
    ·
      refine ⟨64270231772536540912904081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42846821181691027275269387 64270231772536540912904081)
      ·
        refine ⟨48202673829402405684678061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 64270231772536540912904081 48202673829402405684678061)
        ·
          refine ⟨18076002686025902131754273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 48202673829402405684678061 18076002686025902131754273)
          ·
            refine ⟨13557002014519426598815705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18076002686025902131754273 13557002014519426598815705)
            ·
              refine ⟨10167751510889569949111779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13557002014519426598815705 10167751510889569949111779)
              ·
                refine ⟨15251627266334354923667669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10167751510889569949111779 15251627266334354923667669)
                ·
                  refine ⟨357460014054711443523461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 15251627266334354923667669 357460014054711443523461)
                  ·
                    rfl

theorem cell23_6265358_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 2, 2, 1, 7].length) (baseStart_6265358 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6265358 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6265358 prefixEnd_6265358 := by exact prefixLift 6265358
  have htrace : WordTrace (prefixWord ++ tailWord_6265358) baseStart_6265358 baseEnd_6265358 := by
    simpa [prefixWord, tailWord_6265358, baseEnd_6265358] using wordTrace_append hprefix tailTrace_6265358
  have hstable : (prefixWord ++ tailWord_6265358).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6265358).length < 2 ^ (prefixWord ++ tailWord_6265358).sum := by decide
  have hdescent : baseEnd_6265358 < baseStart_6265358 := by decide
  rcases family_descends (prefixWord ++ tailWord_6265358) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6265368 : List Nat := [2, 1, 2, 3, 3, 1, 2, 1, 2, 3, 3]
def baseStart_6265368 : Nat := 118140960795 + 6265368 * 2 ^ 59
def prefixEnd_6265368 : Nat := 4983230072969 + 3 ^ 40 * 6265368 * 2
def baseEnd_6265368 : Nat := 3217145261298947952586103

theorem tailTrace_6265368 : CollatzResearch.WordTrace tailWord_6265368 prefixEnd_6265368 3217145261298947952586103 := by
  unfold tailWord_6265368
  simp only [CollatzResearch.WordTrace]
  refine ⟨114258372182824625254650379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 152344496243766167006200505 114258372182824625254650379)
  ·
    refine ⟨171387558274236937881975569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114258372182824625254650379 171387558274236937881975569)
    ·
      refine ⟨128540668705677703411481677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 171387558274236937881975569 128540668705677703411481677)
      ·
        refine ⟨48202750764629138779305629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 128540668705677703411481677 48202750764629138779305629)
        ·
          refine ⟨18076031536735927042239611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 48202750764629138779305629 18076031536735927042239611)
          ·
            refine ⟨27114047305103890563359417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18076031536735927042239611 27114047305103890563359417)
            ·
              refine ⟨20335535478827917922519563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27114047305103890563359417 20335535478827917922519563)
              ·
                refine ⟨30503303218241876883779345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20335535478827917922519563 30503303218241876883779345)
                ·
                  refine ⟨22877477413681407662834509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 30503303218241876883779345 22877477413681407662834509)
                  ·
                    refine ⟨8579054030130527873562941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 22877477413681407662834509 8579054030130527873562941)
                    ·
                      refine ⟨3217145261298947952586103, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8579054030130527873562941 3217145261298947952586103)
                      ·
                        rfl

theorem cell23_6265368_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 1, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 1, 2, 1, 2, 3, 3].length) (baseStart_6265368 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6265368 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6265368 prefixEnd_6265368 := by exact prefixLift 6265368
  have htrace : WordTrace (prefixWord ++ tailWord_6265368) baseStart_6265368 baseEnd_6265368 := by
    simpa [prefixWord, tailWord_6265368, baseEnd_6265368] using wordTrace_append hprefix tailTrace_6265368
  have hstable : (prefixWord ++ tailWord_6265368).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6265368).length < 2 ^ (prefixWord ++ tailWord_6265368).sum := by decide
  have hdescent : baseEnd_6265368 < baseStart_6265368 := by decide
  rcases family_descends (prefixWord ++ tailWord_6265368) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6265391 : List Nat := [1, 1, 2, 1, 2, 1, 1, 1, 8, 1, 4]
def baseStart_6265391 : Nat := 118140960795 + 6265391 * 2 ^ 59
def prefixEnd_6265391 : Nat := 4983230072969 + 3 ^ 40 * 6265391 * 2
def baseEnd_6265391 : Nat := 3217157071354001362598497

theorem tailTrace_6265391 : CollatzResearch.WordTrace tailWord_6265391 prefixEnd_6265391 3217157071354001362598497 := by
  unfold tailWord_6265391
  simp only [CollatzResearch.WordTrace]
  refine ⟨228517583244565925437388027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152345055496377283624925351 228517583244565925437388027)
  ·
    refine ⟨342776374866848888156082041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 228517583244565925437388027 342776374866848888156082041)
    ·
      refine ⟨257082281150136666117061531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 342776374866848888156082041 257082281150136666117061531)
      ·
        refine ⟨385623421725204999175592297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 257082281150136666117061531 385623421725204999175592297)
        ·
          refine ⟨289217566293903749381694223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 385623421725204999175592297 289217566293903749381694223)
          ·
            refine ⟨433826349440855624072541335, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 289217566293903749381694223 433826349440855624072541335)
            ·
              refine ⟨650739524161283436108812003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 433826349440855624072541335 650739524161283436108812003)
              ·
                refine ⟨976109286241925154163218005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 650739524161283436108812003 976109286241925154163218005)
                ·
                  refine ⟨11438780698147560400350211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 976109286241925154163218005 11438780698147560400350211)
                  ·
                    refine ⟨17158171047221340600525317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11438780698147560400350211 17158171047221340600525317)
                    ·
                      refine ⟨3217157071354001362598497, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17158171047221340600525317 3217157071354001362598497)
                      ·
                        rfl

theorem cell23_6265391_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 1, 8, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 1, 8, 1, 4].length) (baseStart_6265391 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6265391 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6265391 prefixEnd_6265391 := by exact prefixLift 6265391
  have htrace : WordTrace (prefixWord ++ tailWord_6265391) baseStart_6265391 baseEnd_6265391 := by
    simpa [prefixWord, tailWord_6265391, baseEnd_6265391] using wordTrace_append hprefix tailTrace_6265391
  have hstable : (prefixWord ++ tailWord_6265391).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6265391).length < 2 ^ (prefixWord ++ tailWord_6265391).sum := by decide
  have hdescent : baseEnd_6265391 < baseStart_6265391 := by decide
  rcases family_descends (prefixWord ++ tailWord_6265391) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6265408 : List Nat := [2, 1, 1, 2, 2, 2, 2, 1, 4, 4, 2]
def baseStart_6265408 : Nat := 118140960795 + 6265408 * 2 ^ 59
def prefixEnd_6265408 : Nat := 4983230072969 + 3 ^ 40 * 6265408 * 2
def baseEnd_6265408 : Nat := 3217165800525127796085919

theorem tailTrace_6265408 : CollatzResearch.WordTrace tailWord_6265408 prefixEnd_6265408 3217165800525127796085919 := by
  unfold tailWord_6265408
  simp only [CollatzResearch.WordTrace]
  refine ⟨114259101642752168670378439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 152345468857002891560504585 114259101642752168670378439)
  ·
    refine ⟨171388652464128253005567659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114259101642752168670378439 171388652464128253005567659)
    ·
      refine ⟨257082978696192379508351489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 171388652464128253005567659 257082978696192379508351489)
      ·
        refine ⟨192812234022144284631263617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 257082978696192379508351489 192812234022144284631263617)
        ·
          refine ⟨144609175516608213473447713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 192812234022144284631263617 144609175516608213473447713)
          ·
            refine ⟨108456881637456160105085785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 144609175516608213473447713 108456881637456160105085785)
            ·
              refine ⟨81342661228092120078814339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 108456881637456160105085785 81342661228092120078814339)
              ·
                refine ⟨122013991842138180118221509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 81342661228092120078814339 122013991842138180118221509)
                ·
                  refine ⟨22877623470400908772166533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 122013991842138180118221509 22877623470400908772166533)
                  ·
                    refine ⟨4289554400700170394781225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 22877623470400908772166533 4289554400700170394781225)
                    ·
                      refine ⟨3217165800525127796085919, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4289554400700170394781225 3217165800525127796085919)
                      ·
                        rfl

theorem cell23_6265408_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 2, 1, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 2, 1, 4, 4, 2].length) (baseStart_6265408 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6265408 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6265408 prefixEnd_6265408 := by exact prefixLift 6265408
  have htrace : WordTrace (prefixWord ++ tailWord_6265408) baseStart_6265408 baseEnd_6265408 := by
    simpa [prefixWord, tailWord_6265408, baseEnd_6265408] using wordTrace_append hprefix tailTrace_6265408
  have hstable : (prefixWord ++ tailWord_6265408).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6265408).length < 2 ^ (prefixWord ++ tailWord_6265408).sum := by decide
  have hdescent : baseEnd_6265408 < baseStart_6265408 := by decide
  rcases family_descends (prefixWord ++ tailWord_6265408) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6265491 : List Nat := [1, 1, 1, 2, 1, 2, 2, 2, 5, 6]
def baseStart_6265491 : Nat := 118140960795 + 6265491 * 2 ^ 59
def prefixEnd_6265491 : Nat := 4983230072969 + 3 ^ 40 * 6265491 * 2
def baseEnd_6265491 : Nat := 1072402806473150323782679

theorem tailTrace_6265491 : CollatzResearch.WordTrace tailWord_6265491 prefixEnd_6265491 1072402806473150323782679 := by
  unfold tailWord_6265491
  simp only [CollatzResearch.WordTrace]
  refine ⟨228521230544203642516028327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152347487029469095010685551 228521230544203642516028327)
  ·
    refine ⟨342781845816305463774042491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 228521230544203642516028327 342781845816305463774042491)
    ·
      refine ⟨514172768724458195661063737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 342781845816305463774042491 514172768724458195661063737)
      ·
        refine ⟨385629576543343646745797803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 514172768724458195661063737 385629576543343646745797803)
        ·
          refine ⟨578444364815015470118696705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 385629576543343646745797803 578444364815015470118696705)
          ·
            refine ⟨433833273611261602589022529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 578444364815015470118696705 433833273611261602589022529)
            ·
              refine ⟨325374955208446201941766897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 433833273611261602589022529 325374955208446201941766897)
              ·
                refine ⟨244031216406334651456325173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 325374955208446201941766897 244031216406334651456325173)
                ·
                  refine ⟨22877926538093873574030485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 244031216406334651456325173 22877926538093873574030485)
                  ·
                    refine ⟨1072402806473150323782679, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 22877926538093873574030485 1072402806473150323782679)
                    ·
                      rfl

theorem cell23_6265491_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 2, 2, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 2, 2, 5, 6].length) (baseStart_6265491 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6265491 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6265491 prefixEnd_6265491 := by exact prefixLift 6265491
  have htrace : WordTrace (prefixWord ++ tailWord_6265491) baseStart_6265491 baseEnd_6265491 := by
    simpa [prefixWord, tailWord_6265491, baseEnd_6265491] using wordTrace_append hprefix tailTrace_6265491
  have hstable : (prefixWord ++ tailWord_6265491).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6265491).length < 2 ^ (prefixWord ++ tailWord_6265491).sum := by decide
  have hdescent : baseEnd_6265491 < baseStart_6265491 := by decide
  rcases family_descends (prefixWord ++ tailWord_6265491) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6265492 : List Nat := [2, 4, 2, 2, 1, 1, 1, 1, 5, 1, 3]
def baseStart_6265492 : Nat := 118140960795 + 6265492 * 2 ^ 59
def prefixEnd_6265492 : Nat := 4983230072969 + 3 ^ 40 * 6265492 * 2
def baseEnd_6265492 : Nat := 3217208932900105467435533

theorem tailTrace_6265492 : CollatzResearch.WordTrace tailWord_6265492 prefixEnd_6265492 3217208932900105467435533 := by
  unfold tailWord_6265492
  simp only [CollatzResearch.WordTrace]
  refine ⟨114260633508600009843407365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 152347511344800013124543153 114260633508600009843407365)
  ·
    refine ⟨21423868782862501845638881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 114260633508600009843407365 21423868782862501845638881)
    ·
      refine ⟨16067901587146876384229161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21423868782862501845638881 16067901587146876384229161)
      ·
        refine ⟨12050926190360157288171871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16067901587146876384229161 12050926190360157288171871)
        ·
          refine ⟨18076389285540235932257807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12050926190360157288171871 18076389285540235932257807)
          ·
            refine ⟨27114583928310353898386711, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18076389285540235932257807 27114583928310353898386711)
            ·
              refine ⟨40671875892465530847580067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27114583928310353898386711 40671875892465530847580067)
              ·
                refine ⟨61007813838698296271370101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40671875892465530847580067 61007813838698296271370101)
                ·
                  refine ⟨5719482547377965275440947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 61007813838698296271370101 5719482547377965275440947)
                  ·
                    refine ⟨8579223821066947913161421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5719482547377965275440947 8579223821066947913161421)
                    ·
                      refine ⟨3217208932900105467435533, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8579223821066947913161421 3217208932900105467435533)
                      ·
                        rfl

theorem cell23_6265492_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 1, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 1, 1, 1, 5, 1, 3].length) (baseStart_6265492 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6265492 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6265492 prefixEnd_6265492 := by exact prefixLift 6265492
  have htrace : WordTrace (prefixWord ++ tailWord_6265492) baseStart_6265492 baseEnd_6265492 := by
    simpa [prefixWord, tailWord_6265492, baseEnd_6265492] using wordTrace_append hprefix tailTrace_6265492
  have hstable : (prefixWord ++ tailWord_6265492).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6265492).length < 2 ^ (prefixWord ++ tailWord_6265492).sum := by decide
  have hdescent : baseEnd_6265492 < baseStart_6265492 := by decide
  rcases family_descends (prefixWord ++ tailWord_6265492) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6265502 : List Nat := [4, 3, 1, 1, 1, 1, 3, 1, 1, 5, 2]
def baseStart_6265502 : Nat := 118140960795 + 6265502 * 2 ^ 59
def prefixEnd_6265502 : Nat := 4983230072969 + 3 ^ 40 * 6265502 * 2
def baseEnd_6265502 : Nat := 3217214067706650428310487

theorem tailTrace_6265502 : CollatzResearch.WordTrace tailWord_6265502 prefixEnd_6265502 3217214067706650428310487 := by
  unfold tailWord_6265502
  simp only [CollatzResearch.WordTrace]
  refine ⟨28565203968395473924334845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 152347754498109194263119173 28565203968395473924334845)
  ·
    refine ⟨10711951488148302721625567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 28565203968395473924334845 10711951488148302721625567)
    ·
      refine ⟨16067927232222454082438351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10711951488148302721625567 16067927232222454082438351)
      ·
        refine ⟨24101890848333681123657527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16067927232222454082438351 24101890848333681123657527)
        ·
          refine ⟨36152836272500521685486291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24101890848333681123657527 36152836272500521685486291)
          ·
            refine ⟨54229254408750782528229437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36152836272500521685486291 54229254408750782528229437)
            ·
              refine ⟨20335970403281543448086039, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 54229254408750782528229437 20335970403281543448086039)
              ·
                refine ⟨30503955604922315172129059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20335970403281543448086039 30503955604922315172129059)
                ·
                  refine ⟨45755933407383472758193589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30503955604922315172129059 45755933407383472758193589)
                  ·
                    refine ⟨4289618756942200571080649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 45755933407383472758193589 4289618756942200571080649)
                    ·
                      refine ⟨3217214067706650428310487, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4289618756942200571080649 3217214067706650428310487)
                      ·
                        rfl

theorem cell23_6265502_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 3, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 3, 1, 1, 5, 2].length) (baseStart_6265502 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6265502 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6265502 prefixEnd_6265502 := by exact prefixLift 6265502
  have htrace : WordTrace (prefixWord ++ tailWord_6265502) baseStart_6265502 baseEnd_6265502 := by
    simpa [prefixWord, tailWord_6265502, baseEnd_6265502] using wordTrace_append hprefix tailTrace_6265502
  have hstable : (prefixWord ++ tailWord_6265502).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6265502).length < 2 ^ (prefixWord ++ tailWord_6265502).sum := by decide
  have hdescent : baseEnd_6265502 < baseStart_6265502 := by decide
  rcases family_descends (prefixWord ++ tailWord_6265502) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6265508 : List Nat := [2, 3, 1, 2, 2, 1, 1, 4, 1, 6]
def baseStart_6265508 : Nat := 118140960795 + 6265508 * 2 ^ 59
def prefixEnd_6265508 : Nat := 4983230072969 + 3 ^ 40 * 6265508 * 2
def baseEnd_6265508 : Nat := 1072405716196859134945153

theorem tailTrace_6265508 : CollatzResearch.WordTrace tailWord_6265508 prefixEnd_6265508 1072405716196859134945153 := by
  unfold tailWord_6265508
  simp only [CollatzResearch.WordTrace]
  refine ⟨114260925292571027209698589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 152347900390094702946264785 114260925292571027209698589)
  ·
    refine ⟨42847846984714135203636971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 114260925292571027209698589 42847846984714135203636971)
    ·
      refine ⟨64271770477071202805455457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42847846984714135203636971 64271770477071202805455457)
      ·
        refine ⟨48203827857803402104091593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 64271770477071202805455457 48203827857803402104091593)
        ·
          refine ⟨36152870893352551578068695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48203827857803402104091593 36152870893352551578068695)
          ·
            refine ⟨54229306340028827367103043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36152870893352551578068695 54229306340028827367103043)
            ·
              refine ⟨81343959510043241050654565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 54229306340028827367103043 81343959510043241050654565)
              ·
                refine ⟨15251992408133107696997731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 81343959510043241050654565 15251992408133107696997731)
                ·
                  refine ⟨22877988612199661545496597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15251992408133107696997731 22877988612199661545496597)
                  ·
                    refine ⟨1072405716196859134945153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 22877988612199661545496597 1072405716196859134945153)
                    ·
                      rfl

theorem cell23_6265508_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 1, 4, 1, 6].length) (baseStart_6265508 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6265508 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6265508 prefixEnd_6265508 := by exact prefixLift 6265508
  have htrace : WordTrace (prefixWord ++ tailWord_6265508) baseStart_6265508 baseEnd_6265508 := by
    simpa [prefixWord, tailWord_6265508, baseEnd_6265508] using wordTrace_append hprefix tailTrace_6265508
  have hstable : (prefixWord ++ tailWord_6265508).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6265508).length < 2 ^ (prefixWord ++ tailWord_6265508).sum := by decide
  have hdescent : baseEnd_6265508 < baseStart_6265508 := by decide
  rcases family_descends (prefixWord ++ tailWord_6265508) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6265526 : List Nat := [5, 1, 3, 1, 2, 1, 2, 1, 3, 1, 3]
def baseStart_6265526 : Nat := 118140960795 + 6265526 * 2 ^ 59
def prefixEnd_6265526 : Nat := 4983230072969 + 3 ^ 40 * 6265526 * 2
def baseEnd_6265526 : Nat := 3217226391242358334410377

theorem tailTrace_6265526 : CollatzResearch.WordTrace tailWord_6265526 prefixEnd_6265526 3217226391242358334410377 := by
  unfold tailWord_6265526
  simp only [CollatzResearch.WordTrace]
  refine ⟨14282656693692302718347027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 152348338066051228995701621 14282656693692302718347027)
  ·
    refine ⟨21423985040538454077520541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14282656693692302718347027 21423985040538454077520541)
    ·
      refine ⟨8033994390201920279070203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21423985040538454077520541 8033994390201920279070203)
      ·
        refine ⟨12050991585302880418605305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8033994390201920279070203 12050991585302880418605305)
        ·
          refine ⟨9038243688977160313953979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12050991585302880418605305 9038243688977160313953979)
          ·
            refine ⟨13557365533465740470930969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9038243688977160313953979 13557365533465740470930969)
            ·
              refine ⟨10168024150099305353198227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13557365533465740470930969 10168024150099305353198227)
              ·
                refine ⟨15252036225148958029797341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10168024150099305353198227 15252036225148958029797341)
                ·
                  refine ⟨5719513584430859261174003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15252036225148958029797341 5719513584430859261174003)
                  ·
                    refine ⟨8579270376646288891761005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5719513584430859261174003 8579270376646288891761005)
                    ·
                      refine ⟨3217226391242358334410377, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8579270376646288891761005 3217226391242358334410377)
                      ·
                        rfl

theorem cell23_6265526_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 2, 1, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 2, 1, 2, 1, 3, 1, 3].length) (baseStart_6265526 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6265526 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6265526 prefixEnd_6265526 := by exact prefixLift 6265526
  have htrace : WordTrace (prefixWord ++ tailWord_6265526) baseStart_6265526 baseEnd_6265526 := by
    simpa [prefixWord, tailWord_6265526, baseEnd_6265526] using wordTrace_append hprefix tailTrace_6265526
  have hstable : (prefixWord ++ tailWord_6265526).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6265526).length < 2 ^ (prefixWord ++ tailWord_6265526).sum := by decide
  have hdescent : baseEnd_6265526 < baseStart_6265526 := by decide
  rcases family_descends (prefixWord ++ tailWord_6265526) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6265531 : List Nat := [1, 1, 1, 1, 1, 2, 3, 1, 1, 4, 7]
def baseStart_6265531 : Nat := 118140960795 + 6265531 * 2 ^ 59
def prefixEnd_6265531 : Nat := 4983230072969 + 3 ^ 40 * 6265531 * 2
def baseEnd_6265531 : Nat := 3217228958645630814847853

theorem tailTrace_6265531 : CollatzResearch.WordTrace tailWord_6265531 prefixEnd_6265531 3217228958645630814847853 := by
  unfold tailWord_6265531
  simp only [CollatzResearch.WordTrace]
  refine ⟨228522689464058729347484447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152348459642705819564989631 228522689464058729347484447)
  ·
    refine ⟨342784034196088094021226671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 228522689464058729347484447 342784034196088094021226671)
    ·
      refine ⟨514176051294132141031840007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 342784034196088094021226671 514176051294132141031840007)
      ·
        refine ⟨771264076941198211547760011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 514176051294132141031840007 771264076941198211547760011)
        ·
          refine ⟨1156896115411797317321640017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 771264076941198211547760011 1156896115411797317321640017)
          ·
            refine ⟨867672086558847987991230013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1156896115411797317321640017 867672086558847987991230013)
            ·
              refine ⟨325377032459567995496711255, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 867672086558847987991230013 325377032459567995496711255)
              ·
                refine ⟨488065548689351993245066883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 325377032459567995496711255 488065548689351993245066883)
                ·
                  refine ⟨732098323034027989867600325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 488065548689351993245066883 732098323034027989867600325)
                  ·
                    refine ⟨137268435568880248100175061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 732098323034027989867600325 137268435568880248100175061)
                    ·
                      refine ⟨3217228958645630814847853, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 137268435568880248100175061 3217228958645630814847853)
                      ·
                        rfl

theorem cell23_6265531_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 3, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 3, 1, 1, 4, 7].length) (baseStart_6265531 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6265531 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6265531 prefixEnd_6265531 := by exact prefixLift 6265531
  have htrace : WordTrace (prefixWord ++ tailWord_6265531) baseStart_6265531 baseEnd_6265531 := by
    simpa [prefixWord, tailWord_6265531, baseEnd_6265531] using wordTrace_append hprefix tailTrace_6265531
  have hstable : (prefixWord ++ tailWord_6265531).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6265531).length < 2 ^ (prefixWord ++ tailWord_6265531).sum := by decide
  have hdescent : baseEnd_6265531 < baseStart_6265531 := by decide
  rcases family_descends (prefixWord ++ tailWord_6265531) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6265578 : List Nat := [3, 1, 3, 1, 1, 1, 1, 1, 4, 2, 5]
def baseStart_6265578 : Nat := 118140960795 + 6265578 * 2 ^ 59
def prefixEnd_6265578 : Nat := 4983230072969 + 3 ^ 40 * 6265578 * 2
def baseEnd_6265578 : Nat := 3217253092236392130960137

theorem tailTrace_6265578 : CollatzResearch.WordTrace tailWord_6265578 prefixEnd_6265578 3217253092236392130960137 := by
  unfold tailWord_6265578
  simp only [CollatzResearch.WordTrace]
  refine ⟨57131100923722114093611347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 152349602463258970916296925 57131100923722114093611347)
  ·
    refine ⟨85696651385583171140417021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57131100923722114093611347 85696651385583171140417021)
    ·
      refine ⟨32136244269593689177656383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 85696651385583171140417021 32136244269593689177656383)
      ·
        refine ⟨48204366404390533766484575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32136244269593689177656383 48204366404390533766484575)
        ·
          refine ⟨72306549606585800649726863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48204366404390533766484575 72306549606585800649726863)
          ·
            refine ⟨108459824409878700974590295, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 72306549606585800649726863 108459824409878700974590295)
            ·
              refine ⟨162689736614818051461885443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 108459824409878700974590295 162689736614818051461885443)
              ·
                refine ⟨244034604922227077192828165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 162689736614818051461885443 244034604922227077192828165)
                ·
                  refine ⟨45756488422917576973655281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 244034604922227077192828165 45756488422917576973655281)
                  ·
                    refine ⟨34317366317188182730241461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 45756488422917576973655281 34317366317188182730241461)
                    ·
                      refine ⟨3217253092236392130960137, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 34317366317188182730241461 3217253092236392130960137)
                      ·
                        rfl

theorem cell23_6265578_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 1, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 1, 1, 4, 2, 5].length) (baseStart_6265578 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6265578 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6265578 prefixEnd_6265578 := by exact prefixLift 6265578
  have htrace : WordTrace (prefixWord ++ tailWord_6265578) baseStart_6265578 baseEnd_6265578 := by
    simpa [prefixWord, tailWord_6265578, baseEnd_6265578] using wordTrace_append hprefix tailTrace_6265578
  have hstable : (prefixWord ++ tailWord_6265578).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6265578).length < 2 ^ (prefixWord ++ tailWord_6265578).sum := by decide
  have hdescent : baseEnd_6265578 < baseStart_6265578 := by decide
  rcases family_descends (prefixWord ++ tailWord_6265578) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6265582 : List Nat := [4, 1, 2, 1, 1, 3, 2, 1, 4, 1, 3]
def baseStart_6265582 : Nat := 118140960795 + 6265582 * 2 ^ 59
def prefixEnd_6265582 : Nat := 4983230072969 + 3 ^ 40 * 6265582 * 2
def baseEnd_6265582 : Nat := 3217255146159010115310119

theorem tailTrace_6265582 : CollatzResearch.WordTrace tailWord_6265582 prefixEnd_6265582 3217255146159010115310119 := by
  unfold tailWord_6265582
  simp only [CollatzResearch.WordTrace]
  refine ⟨28565568698359245632198875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 152349699724582643371727333 28565568698359245632198875)
  ·
    refine ⟨42848353047538868448298313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28565568698359245632198875 42848353047538868448298313)
    ·
      refine ⟨32136264785654151336223735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42848353047538868448298313 32136264785654151336223735)
      ·
        refine ⟨48204397178481227004335603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32136264785654151336223735 48204397178481227004335603)
        ·
          refine ⟨72306595767721840506503405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48204397178481227004335603 72306595767721840506503405)
          ·
            refine ⟨27114973412895690189938777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 72306595767721840506503405 27114973412895690189938777)
            ·
              refine ⟨20336230059671767642454083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27114973412895690189938777 20336230059671767642454083)
              ·
                refine ⟨30504345089507651463681125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20336230059671767642454083 30504345089507651463681125)
                ·
                  refine ⟨5719564704282684649440211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 30504345089507651463681125 5719564704282684649440211)
                  ·
                    refine ⟨8579347056424026974160317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5719564704282684649440211 8579347056424026974160317)
                    ·
                      refine ⟨3217255146159010115310119, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8579347056424026974160317 3217255146159010115310119)
                      ·
                        rfl

theorem cell23_6265582_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 3, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 3, 2, 1, 4, 1, 3].length) (baseStart_6265582 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6265582 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6265582 prefixEnd_6265582 := by exact prefixLift 6265582
  have htrace : WordTrace (prefixWord ++ tailWord_6265582) baseStart_6265582 baseEnd_6265582 := by
    simpa [prefixWord, tailWord_6265582, baseEnd_6265582] using wordTrace_append hprefix tailTrace_6265582
  have hstable : (prefixWord ++ tailWord_6265582).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6265582).length < 2 ^ (prefixWord ++ tailWord_6265582).sum := by decide
  have hdescent : baseEnd_6265582 < baseStart_6265582 := by decide
  rcases family_descends (prefixWord ++ tailWord_6265582) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6265589 : List Nat := [1, 3, 6, 1, 1, 1, 2, 8]
def baseStart_6265589 : Nat := 118140960795 + 6265589 * 2 ^ 59
def prefixEnd_6265589 : Nat := 4983230072969 + 3 ^ 40 * 6265589 * 2
def baseEnd_6265589 : Nat := 119157731130503392145281

theorem tailTrace_6265589 : CollatzResearch.WordTrace tailWord_6265589 prefixEnd_6265589 119157731130503392145281 := by
  unfold tailWord_6265589
  simp only [CollatzResearch.WordTrace]
  refine ⟨228524804897848605253095821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152349869931899070168730547 228524804897848605253095821)
  ·
    refine ⟨85696801836693226969910933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 228524804897848605253095821 85696801836693226969910933)
    ·
      refine ⟨4017037586094995014214575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 85696801836693226969910933 4017037586094995014214575)
      ·
        refine ⟨6025556379142492521321863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4017037586094995014214575 6025556379142492521321863)
        ·
          refine ⟨9038334568713738781982795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6025556379142492521321863 9038334568713738781982795)
          ·
            refine ⟨13557501853070608172974193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9038334568713738781982795 13557501853070608172974193)
            ·
              refine ⟨10168126389802956129730645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13557501853070608172974193 10168126389802956129730645)
              ·
                refine ⟨119157731130503392145281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 10168126389802956129730645 119157731130503392145281)
                ·
                  rfl

theorem cell23_6265589_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 6, 1, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 6, 1, 1, 1, 2, 8].length) (baseStart_6265589 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6265589 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6265589 prefixEnd_6265589 := by exact prefixLift 6265589
  have htrace : WordTrace (prefixWord ++ tailWord_6265589) baseStart_6265589 baseEnd_6265589 := by
    simpa [prefixWord, tailWord_6265589, baseEnd_6265589] using wordTrace_append hprefix tailTrace_6265589
  have hstable : (prefixWord ++ tailWord_6265589).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6265589).length < 2 ^ (prefixWord ++ tailWord_6265589).sum := by decide
  have hdescent : baseEnd_6265589 < baseStart_6265589 := by decide
  rcases family_descends (prefixWord ++ tailWord_6265589) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6265605 : List Nat := [1, 3, 1, 1, 2, 1, 1, 2, 5, 4, 2]
def baseStart_6265605 : Nat := 118140960795 + 6265605 * 2 ^ 59
def prefixEnd_6265605 : Nat := 4983230072969 + 3 ^ 40 * 6265605 * 2
def baseEnd_6265605 : Nat := 3217266956214063525322513

theorem tailTrace_6265605 : CollatzResearch.WordTrace tailWord_6265605 prefixEnd_6265605 3217266956214063525322513 := by
  unfold tailWord_6265605
  simp only [CollatzResearch.WordTrace]
  refine ⟨228525388465790639985678269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152350258977193759990452179 228525388465790639985678269)
  ·
    refine ⟨85697020674671489994629351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 228525388465790639985678269 85697020674671489994629351)
    ·
      refine ⟨128545531012007234991944027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85697020674671489994629351 128545531012007234991944027)
      ·
        refine ⟨192818296518010852487916041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 128545531012007234991944027 192818296518010852487916041)
        ·
          refine ⟨144613722388508139365937031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 192818296518010852487916041 144613722388508139365937031)
          ·
            refine ⟨216920583582762209048905547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 144613722388508139365937031 216920583582762209048905547)
            ·
              refine ⟨325380875374143313573358321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 216920583582762209048905547 325380875374143313573358321)
              ·
                refine ⟨244035656530607485180018741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 325380875374143313573358321 244035656530607485180018741)
                ·
                  refine ⟨22878342799744451735626757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 244035656530607485180018741 22878342799744451735626757)
                  ·
                    refine ⟨4289689274952084700430017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 22878342799744451735626757 4289689274952084700430017)
                    ·
                      refine ⟨3217266956214063525322513, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4289689274952084700430017 3217266956214063525322513)
                      ·
                        rfl

theorem cell23_6265605_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 1, 2, 5, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 1, 2, 5, 4, 2].length) (baseStart_6265605 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6265605 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6265605 prefixEnd_6265605 := by exact prefixLift 6265605
  have htrace : WordTrace (prefixWord ++ tailWord_6265605) baseStart_6265605 baseEnd_6265605 := by
    simpa [prefixWord, tailWord_6265605, baseEnd_6265605] using wordTrace_append hprefix tailTrace_6265605
  have hstable : (prefixWord ++ tailWord_6265605).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6265605).length < 2 ^ (prefixWord ++ tailWord_6265605).sum := by decide
  have hdescent : baseEnd_6265605 < baseStart_6265605 := by decide
  rcases family_descends (prefixWord ++ tailWord_6265605) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6265655 : List Nat := [1, 1, 3, 1, 2, 1, 5, 1, 2, 3, 3]
def baseStart_6265655 : Nat := 118140960795 + 6265655 * 2 ^ 59
def prefixEnd_6265655 : Nat := 4983230072969 + 3 ^ 40 * 6265655 * 2
def baseEnd_6265655 : Nat := 3217292630246788329697283

theorem tailTrace_6265655 : CollatzResearch.WordTrace tailWord_6265655 prefixEnd_6265655 3217292630246788329697283 := by
  unfold tailWord_6265655
  simp only [CollatzResearch.WordTrace]
  refine ⟨228527212115609498524998419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152351474743739665683332279 228527212115609498524998419)
  ·
    refine ⟨342790818173414247787497629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 228527212115609498524998419 342790818173414247787497629)
    ·
      refine ⟨128546556815030342920311611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 342790818173414247787497629 128546556815030342920311611)
      ·
        refine ⟨192819835222545514380467417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 128546556815030342920311611 192819835222545514380467417)
        ·
          refine ⟨144614876416909135785350563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 192819835222545514380467417 144614876416909135785350563)
          ·
            refine ⟨216922314625363703678025845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 144614876416909135785350563 216922314625363703678025845)
            ·
              refine ⟨20336466996127847219814923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 216922314625363703678025845 20336466996127847219814923)
              ·
                refine ⟨30504700494191770829722385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20336466996127847219814923 30504700494191770829722385)
                ·
                  refine ⟨22878525370643828122291789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 30504700494191770829722385 22878525370643828122291789)
                  ·
                    refine ⟨8579447013991435545859421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 22878525370643828122291789 8579447013991435545859421)
                    ·
                      refine ⟨3217292630246788329697283, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8579447013991435545859421 3217292630246788329697283)
                      ·
                        rfl

theorem cell23_6265655_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 5, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 5, 1, 2, 3, 3].length) (baseStart_6265655 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6265655 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6265655 prefixEnd_6265655 := by exact prefixLift 6265655
  have htrace : WordTrace (prefixWord ++ tailWord_6265655) baseStart_6265655 baseEnd_6265655 := by
    simpa [prefixWord, tailWord_6265655, baseEnd_6265655] using wordTrace_append hprefix tailTrace_6265655
  have hstable : (prefixWord ++ tailWord_6265655).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6265655).length < 2 ^ (prefixWord ++ tailWord_6265655).sum := by decide
  have hdescent : baseEnd_6265655 < baseStart_6265655 := by decide
  rcases family_descends (prefixWord ++ tailWord_6265655) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6265662 : List Nat := [4, 2, 1, 2, 3, 1, 1, 2, 7]
def baseStart_6265662 : Nat := 118140960795 + 6265662 * 2 ^ 59
def prefixEnd_6265662 : Nat := 4983230072969 + 3 ^ 40 * 6265662 * 2
def baseEnd_6265662 : Nat := 357477358290152200256639

theorem tailTrace_6265662 : CollatzResearch.WordTrace tailWord_6265662 prefixEnd_6265662 357477358290152200256639 := by
  unfold tailWord_6265662
  simp only [CollatzResearch.WordTrace]
  refine ⟨28565933428323017340062905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 152351644951056092480335493 28565933428323017340062905)
  ·
    refine ⟨21424450071242263005047179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28565933428323017340062905 21424450071242263005047179)
    ·
      refine ⟨32136675106863394507570769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21424450071242263005047179 32136675106863394507570769)
      ·
        refine ⟨24102506330147545880678077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32136675106863394507570769 24102506330147545880678077)
        ·
          refine ⟨9038439873805329705254279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24102506330147545880678077 9038439873805329705254279)
          ·
            refine ⟨13557659810707994557881419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9038439873805329705254279 13557659810707994557881419)
            ·
              refine ⟨20336489716061991836822129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13557659810707994557881419 20336489716061991836822129)
              ·
                refine ⟨15252367287046493877616597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20336489716061991836822129 15252367287046493877616597)
                ·
                  refine ⟨357477358290152200256639, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 15252367287046493877616597 357477358290152200256639)
                  ·
                    rfl

theorem cell23_6265662_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 3, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 3, 1, 1, 2, 7].length) (baseStart_6265662 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6265662 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6265662 prefixEnd_6265662 := by exact prefixLift 6265662
  have htrace : WordTrace (prefixWord ++ tailWord_6265662) baseStart_6265662 baseEnd_6265662 := by
    simpa [prefixWord, tailWord_6265662, baseEnd_6265662] using wordTrace_append hprefix tailTrace_6265662
  have hstable : (prefixWord ++ tailWord_6265662).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6265662).length < 2 ^ (prefixWord ++ tailWord_6265662).sum := by decide
  have hdescent : baseEnd_6265662 < baseStart_6265662 := by decide
  rcases family_descends (prefixWord ++ tailWord_6265662) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6265688 : List Nat := [2, 1, 2, 2, 1, 1, 1, 2, 1, 10]
def baseStart_6265688 : Nat := 118140960795 + 6265688 * 2 ^ 59
def prefixEnd_6265688 : Nat := 4983230072969 + 3 ^ 40 * 6265688 * 2
def baseEnd_6265688 : Nat := 1072436525036128900194877

theorem tailTrace_6265688 : CollatzResearch.WordTrace tailWord_6265688 prefixEnd_6265688 1072436525036128900194877 := by
  unfold tailWord_6265688
  simp only [CollatzResearch.WordTrace]
  refine ⟨114264207862244972580474859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 152352277149659963440633145 114264207862244972580474859)
  ·
    refine ⟨171396311793367458870712289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114264207862244972580474859 171396311793367458870712289)
    ·
      refine ⟨128547233845025594153034217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 171396311793367458870712289 128547233845025594153034217)
      ·
        refine ⟨96410425383769195614775663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 128547233845025594153034217 96410425383769195614775663)
        ·
          refine ⟨144615638075653793422163495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 96410425383769195614775663 144615638075653793422163495)
          ·
            refine ⟨216923457113480690133245243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 144615638075653793422163495 216923457113480690133245243)
            ·
              refine ⟨325385185670221035199867865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 216923457113480690133245243 325385185670221035199867865)
              ·
                refine ⟨244038889252665776399900899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 325385185670221035199867865 244038889252665776399900899)
                ·
                  refine ⟨366058333878998664599851349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 244038889252665776399900899 366058333878998664599851349)
                  ·
                    refine ⟨1072436525036128900194877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 366058333878998664599851349 1072436525036128900194877)
                    ·
                      rfl

theorem cell23_6265688_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 1, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 1, 2, 1, 10].length) (baseStart_6265688 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6265688 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6265688 prefixEnd_6265688 := by exact prefixLift 6265688
  have htrace : WordTrace (prefixWord ++ tailWord_6265688) baseStart_6265688 baseEnd_6265688 := by
    simpa [prefixWord, tailWord_6265688, baseEnd_6265688] using wordTrace_append hprefix tailTrace_6265688
  have hstable : (prefixWord ++ tailWord_6265688).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6265688).length < 2 ^ (prefixWord ++ tailWord_6265688).sum := by decide
  have hdescent : baseEnd_6265688 < baseStart_6265688 := by decide
  rcases family_descends (prefixWord ++ tailWord_6265688) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6265695 : List Nat := [1, 1, 2, 3, 1, 3, 2, 1, 4, 1, 4]
def baseStart_6265695 : Nat := 118140960795 + 6265695 * 2 ^ 59
def prefixEnd_6265695 : Nat := 4983230072969 + 3 ^ 40 * 6265695 * 2
def baseEnd_6265695 : Nat := 3217313169472968173197099

theorem tailTrace_6265695 : CollatzResearch.WordTrace tailWord_6265695 prefixEnd_6265695 3217313169472968173197099 := by
  unfold tailWord_6265695
  simp only [CollatzResearch.WordTrace]
  refine ⟨228528671035464585356454539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152352447356976390237636359 228528671035464585356454539)
  ·
    refine ⟨342793006553196878034681809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 228528671035464585356454539 342793006553196878034681809)
    ·
      refine ⟨257094754914897658526011357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 342793006553196878034681809 257094754914897658526011357)
      ·
        refine ⟨96410533093086621947254259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 257094754914897658526011357 96410533093086621947254259)
        ·
          refine ⟨144615799639629932920881389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 96410533093086621947254259 144615799639629932920881389)
          ·
            refine ⟨54230924864861224845330521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 144615799639629932920881389 54230924864861224845330521)
            ·
              refine ⟨40673193648645918633997891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 54230924864861224845330521 40673193648645918633997891)
              ·
                refine ⟨61009790472968877950996837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40673193648645918633997891 61009790472968877950996837)
                ·
                  refine ⟨11439335713681664615811907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 61009790472968877950996837 11439335713681664615811907)
                  ·
                    refine ⟨17159003570522496923717861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11439335713681664615811907 17159003570522496923717861)
                    ·
                      refine ⟨3217313169472968173197099, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17159003570522496923717861 3217313169472968173197099)
                      ·
                        rfl

theorem cell23_6265695_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 2, 1, 4, 1, 4].length) (baseStart_6265695 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6265695 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6265695 prefixEnd_6265695 := by exact prefixLift 6265695
  have htrace : WordTrace (prefixWord ++ tailWord_6265695) baseStart_6265695 baseEnd_6265695 := by
    simpa [prefixWord, tailWord_6265695, baseEnd_6265695] using wordTrace_append hprefix tailTrace_6265695
  have hstable : (prefixWord ++ tailWord_6265695).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6265695).length < 2 ^ (prefixWord ++ tailWord_6265695).sum := by decide
  have hdescent : baseEnd_6265695 < baseStart_6265695 := by decide
  rcases family_descends (prefixWord ++ tailWord_6265695) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6265712 : List Nat := [2, 1, 1, 1, 4, 1, 4, 1, 2, 4, 2]
def baseStart_6265712 : Nat := 118140960795 + 6265712 * 2 ^ 59
def prefixEnd_6265712 : Nat := 4983230072969 + 3 ^ 40 * 6265712 * 2
def baseEnd_6265712 : Nat := 3217321898644094606684521

theorem tailTrace_6265712 : CollatzResearch.WordTrace tailWord_6265712 prefixEnd_6265712 3217321898644094606684521 := by
  unfold tailWord_6265712
  simp only [CollatzResearch.WordTrace]
  refine ⟨114264645538201498629911695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 152352860717601998173215593 114264645538201498629911695)
  ·
    refine ⟨171396968307302247944867543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114264645538201498629911695 171396968307302247944867543)
    ·
      refine ⟨257095452460953371917301315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 171396968307302247944867543 257095452460953371917301315)
      ·
        refine ⟨385643178691430057875951973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 257095452460953371917301315 385643178691430057875951973)
        ·
          refine ⟨72308096004643135851740995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 385643178691430057875951973 72308096004643135851740995)
          ·
            refine ⟨108462144006964703777611493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 72308096004643135851740995 108462144006964703777611493)
            ·
              refine ⟨20336652001305881958302155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 108462144006964703777611493 20336652001305881958302155)
              ·
                refine ⟨30504978001958822937453233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20336652001305881958302155 30504978001958822937453233)
                ·
                  refine ⟨22878733501469117203089925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 30504978001958822937453233 22878733501469117203089925)
                  ·
                    refine ⟨4289762531525459475579361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 22878733501469117203089925 4289762531525459475579361)
                    ·
                      refine ⟨3217321898644094606684521, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4289762531525459475579361 3217321898644094606684521)
                      ·
                        rfl

theorem cell23_6265712_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 4, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 4, 1, 2, 4, 2].length) (baseStart_6265712 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6265712 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6265712 prefixEnd_6265712 := by exact prefixLift 6265712
  have htrace : WordTrace (prefixWord ++ tailWord_6265712) baseStart_6265712 baseEnd_6265712 := by
    simpa [prefixWord, tailWord_6265712, baseEnd_6265712] using wordTrace_append hprefix tailTrace_6265712
  have hstable : (prefixWord ++ tailWord_6265712).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6265712).length < 2 ^ (prefixWord ++ tailWord_6265712).sum := by decide
  have hdescent : baseEnd_6265712 < baseStart_6265712 := by decide
  rcases family_descends (prefixWord ++ tailWord_6265712) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6265715 : List Nat := [1, 1, 1, 2, 2, 1, 5, 2, 1, 4, 3]
def baseStart_6265715 : Nat := 118140960795 + 6265715 * 2 ^ 59
def prefixEnd_6265715 : Nat := 4983230072969 + 3 ^ 40 * 6265715 * 2
def baseEnd_6265715 : Nat := 3217323439086058094947007

theorem tailTrace_6265715 : CollatzResearch.WordTrace tailWord_6265715 prefixEnd_6265715 3217323439086058094947007 := by
  unfold tailWord_6265715
  simp only [CollatzResearch.WordTrace]
  refine ⟨228529400495392128772182599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152352933663594752514788399 228529400495392128772182599)
  ·
    refine ⟨342794100743088193158273899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 228529400495392128772182599 342794100743088193158273899)
    ·
      refine ⟨514191151114632289737410849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 342794100743088193158273899 514191151114632289737410849)
      ·
        refine ⟨385643363335974217303058137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 514191151114632289737410849 385643363335974217303058137)
        ·
          refine ⟨289232522501980662977293603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 385643363335974217303058137 289232522501980662977293603)
          ·
            refine ⟨433848783752970994465940405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 289232522501980662977293603 433848783752970994465940405)
            ·
              refine ⟨40673323476841030731181913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 433848783752970994465940405 40673323476841030731181913)
              ·
                refine ⟨30504992607630773048386435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 40673323476841030731181913 30504992607630773048386435)
                ·
                  refine ⟨45757488911446159572579653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30504992607630773048386435 45757488911446159572579653)
                  ·
                    refine ⟨8579529170896154919858685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 45757488911446159572579653 8579529170896154919858685)
                    ·
                      refine ⟨3217323439086058094947007, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8579529170896154919858685 3217323439086058094947007)
                      ·
                        rfl

theorem cell23_6265715_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 5, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 5, 2, 1, 4, 3].length) (baseStart_6265715 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6265715 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6265715 prefixEnd_6265715 := by exact prefixLift 6265715
  have htrace : WordTrace (prefixWord ++ tailWord_6265715) baseStart_6265715 baseEnd_6265715 := by
    simpa [prefixWord, tailWord_6265715, baseEnd_6265715] using wordTrace_append hprefix tailTrace_6265715
  have hstable : (prefixWord ++ tailWord_6265715).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6265715).length < 2 ^ (prefixWord ++ tailWord_6265715).sum := by decide
  have hdescent : baseEnd_6265715 < baseStart_6265715 := by decide
  rcases family_descends (prefixWord ++ tailWord_6265715) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6265730 : List Nat := [3, 4, 2, 2, 2, 1, 1, 3, 5]
def baseStart_6265730 : Nat := 118140960795 + 6265730 * 2 ^ 59
def prefixEnd_6265730 : Nat := 4983230072969 + 3 ^ 40 * 6265730 * 2
def baseEnd_6265730 : Nat := 357481237921763948473271

theorem tailTrace_6265730 : CollatzResearch.WordTrace tailWord_6265730 prefixEnd_6265730 357481237921763948473271 := by
  unfold tailWord_6265730
  simp only [CollatzResearch.WordTrace]
  refine ⟨57132486897584446583494661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 152353298393558524222652429 57132486897584446583494661)
  ·
    refine ⟨10712341293297083734405249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 57132486897584446583494661 10712341293297083734405249)
    ·
      refine ⟨8034255969972812800803937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10712341293297083734405249 8034255969972812800803937)
      ·
        refine ⟨6025691977479609600602953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8034255969972812800803937 6025691977479609600602953)
        ·
          refine ⟨4519268983109707200452215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6025691977479609600602953 4519268983109707200452215)
          ·
            refine ⟨6778903474664560800678323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4519268983109707200452215 6778903474664560800678323)
            ·
              refine ⟨10168355211996841201017485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6778903474664560800678323 10168355211996841201017485)
              ·
                refine ⟨3813133204498815450381557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10168355211996841201017485 3813133204498815450381557)
                ·
                  refine ⟨357481237921763948473271, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3813133204498815450381557 357481237921763948473271)
                  ·
                    rfl

theorem cell23_6265730_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 2, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 2, 2, 1, 1, 3, 5].length) (baseStart_6265730 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6265730 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6265730 prefixEnd_6265730 := by exact prefixLift 6265730
  have htrace : WordTrace (prefixWord ++ tailWord_6265730) baseStart_6265730 baseEnd_6265730 := by
    simpa [prefixWord, tailWord_6265730, baseEnd_6265730] using wordTrace_append hprefix tailTrace_6265730
  have hstable : (prefixWord ++ tailWord_6265730).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6265730).length < 2 ^ (prefixWord ++ tailWord_6265730).sum := by decide
  have hdescent : baseEnd_6265730 < baseStart_6265730 := by decide
  rcases family_descends (prefixWord ++ tailWord_6265730) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6265732 : List Nat := [2, 3, 2, 1, 1, 1, 1, 5, 2, 2, 3]
def baseStart_6265732 : Nat := 118140960795 + 6265732 * 2 ^ 59
def prefixEnd_6265732 : Nat := 4983230072969 + 3 ^ 40 * 6265732 * 2
def baseEnd_6265732 : Nat := 3217332168257184528434429

theorem tailTrace_6265732 : CollatzResearch.WordTrace tailWord_6265732 prefixEnd_6265732 3217332168257184528434429 := by
  unfold tailWord_6265732
  simp only [CollatzResearch.WordTrace]
  refine ⟨114265010268165270337775725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 152353347024220360450367633 114265010268165270337775725)
  ·
    refine ⟨42849378850561976376665897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 114265010268165270337775725 42849378850561976376665897)
    ·
      refine ⟨32137034137921482282499423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42849378850561976376665897 32137034137921482282499423)
      ·
        refine ⟨48205551206882223423749135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32137034137921482282499423 48205551206882223423749135)
        ·
          refine ⟨72308326810323335135623703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48205551206882223423749135 72308326810323335135623703)
          ·
            refine ⟨108462490215485002703435555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 72308326810323335135623703 108462490215485002703435555)
            ·
              refine ⟨162693735323227504055153333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 108462490215485002703435555 162693735323227504055153333)
              ·
                refine ⟨15252537686552578505170625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 162693735323227504055153333 15252537686552578505170625)
                ·
                  refine ⟨11439403264914433878877969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15252537686552578505170625 11439403264914433878877969)
                  ·
                    refine ⟨8579552448685825409158477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11439403264914433878877969 8579552448685825409158477)
                    ·
                      refine ⟨3217332168257184528434429, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8579552448685825409158477 3217332168257184528434429)
                      ·
                        rfl

theorem cell23_6265732_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 1, 5, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 1, 5, 2, 2, 3].length) (baseStart_6265732 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6265732 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6265732 prefixEnd_6265732 := by exact prefixLift 6265732
  have htrace : WordTrace (prefixWord ++ tailWord_6265732) baseStart_6265732 baseEnd_6265732 := by
    simpa [prefixWord, tailWord_6265732, baseEnd_6265732] using wordTrace_append hprefix tailTrace_6265732
  have hstable : (prefixWord ++ tailWord_6265732).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6265732).length < 2 ^ (prefixWord ++ tailWord_6265732).sum := by decide
  have hdescent : baseEnd_6265732 < baseStart_6265732 := by decide
  rcases family_descends (prefixWord ++ tailWord_6265732) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6265735 : List Nat := [1, 1, 4, 2, 3, 1, 1, 2, 8]
def baseStart_6265735 : Nat := 118140960795 + 6265735 * 2 ^ 59
def prefixEnd_6265735 : Nat := 4983230072969 + 3 ^ 40 * 6265735 * 2
def baseEnd_6265735 : Nat := 357481523188794224077435

theorem tailTrace_6265735 : CollatzResearch.WordTrace tailWord_6265735 prefixEnd_6265735 357481523188794224077435 := by
  unfold tailWord_6265735
  simp only [CollatzResearch.WordTrace]
  refine ⟨228530129955319672187910659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152353419970213114791940439 228530129955319672187910659)
  ·
    refine ⟨342795194932979508281865989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 228530129955319672187910659 342795194932979508281865989)
    ·
      refine ⟨64274099049933657802849873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 342795194932979508281865989 64274099049933657802849873)
      ·
        refine ⟨48205574287450243352137405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 64274099049933657802849873 48205574287450243352137405)
        ·
          refine ⟨18077090357793841257051527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 48205574287450243352137405 18077090357793841257051527)
          ·
            refine ⟨27115635536690761885577291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18077090357793841257051527 27115635536690761885577291)
            ·
              refine ⟨40673453305036142828365937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27115635536690761885577291 40673453305036142828365937)
              ·
                refine ⟨30505089978777107121274453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 40673453305036142828365937 30505089978777107121274453)
                ·
                  refine ⟨357481523188794224077435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 30505089978777107121274453 357481523188794224077435)
                  ·
                    rfl

theorem cell23_6265735_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 1, 1, 2, 8].length) (baseStart_6265735 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6265735 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6265735 prefixEnd_6265735 := by exact prefixLift 6265735
  have htrace : WordTrace (prefixWord ++ tailWord_6265735) baseStart_6265735 baseEnd_6265735 := by
    simpa [prefixWord, tailWord_6265735, baseEnd_6265735] using wordTrace_append hprefix tailTrace_6265735
  have hstable : (prefixWord ++ tailWord_6265735).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6265735).length < 2 ^ (prefixWord ++ tailWord_6265735).sum := by decide
  have hdescent : baseEnd_6265735 < baseStart_6265735 := by decide
  rcases family_descends (prefixWord ++ tailWord_6265735) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6265739 : List Nat := [1, 1, 1, 1, 4, 2, 5, 3, 1, 4]
def baseStart_6265739 : Nat := 118140960795 + 6265739 * 2 ^ 59
def prefixEnd_6265739 : Nat := 4983230072969 + 3 ^ 40 * 6265739 * 2
def baseEnd_6265739 : Nat := 1072445254207255333682299

theorem tailTrace_6265739 : CollatzResearch.WordTrace tailWord_6265739 prefixEnd_6265739 1072445254207255333682299 := by
  unfold tailWord_6265739
  simp only [CollatzResearch.WordTrace]
  refine ⟨228530275847305180871056271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152353517231536787247370847 228530275847305180871056271)
  ·
    refine ⟨342795413770957771306584407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 228530275847305180871056271 342795413770957771306584407)
    ·
      refine ⟨514193120656436656959876611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 342795413770957771306584407 514193120656436656959876611)
      ·
        refine ⟨771289680984654985439814917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 514193120656436656959876611 771289680984654985439814917)
        ·
          refine ⟨144616815184622809769965297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 771289680984654985439814917 144616815184622809769965297)
          ·
            refine ⟨108462611388467107327473973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 144616815184622809769965297 108462611388467107327473973)
            ·
              refine ⟨10168369817668791311950685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 108462611388467107327473973 10168369817668791311950685)
              ·
                refine ⟨3813138681625796741981507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10168369817668791311950685 3813138681625796741981507)
                ·
                  refine ⟨5719708022438695112972261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3813138681625796741981507 5719708022438695112972261)
                  ·
                    refine ⟨1072445254207255333682299, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5719708022438695112972261 1072445254207255333682299)
                    ·
                      rfl

theorem cell23_6265739_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 5, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 5, 3, 1, 4].length) (baseStart_6265739 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6265739 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6265739 prefixEnd_6265739 := by exact prefixLift 6265739
  have htrace : WordTrace (prefixWord ++ tailWord_6265739) baseStart_6265739 baseEnd_6265739 := by
    simpa [prefixWord, tailWord_6265739, baseEnd_6265739] using wordTrace_append hprefix tailTrace_6265739
  have hstable : (prefixWord ++ tailWord_6265739).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6265739).length < 2 ^ (prefixWord ++ tailWord_6265739).sum := by decide
  have hdescent : baseEnd_6265739 < baseStart_6265739 := by decide
  rcases family_descends (prefixWord ++ tailWord_6265739) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6265756 : List Nat := [2, 2, 3, 3, 2, 2, 1, 1, 3, 4]
def baseStart_6265756 : Nat := 118140960795 + 6265756 * 2 ^ 59
def prefixEnd_6265756 : Nat := 4983230072969 + 3 ^ 40 * 6265756 * 2
def baseEnd_6265756 : Nat := 1072448163930964144844773

theorem tailTrace_6265756 : CollatzResearch.WordTrace tailWord_6265756 prefixEnd_6265756 1072448163930964144844773 := by
  unfold tailWord_6265756
  simp only [CollatzResearch.WordTrace]
  refine ⟨114265447944121796387212561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 152353930592162395182950081 114265447944121796387212561)
  ·
    refine ⟨85699085958091347290409421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 114265447944121796387212561 85699085958091347290409421)
    ·
      refine ⟨32137157234284255233903533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 85699085958091347290409421 32137157234284255233903533)
      ·
        refine ⟨12051433962856595712713825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 32137157234284255233903533 12051433962856595712713825)
        ·
          refine ⟨9038575472142446784535369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12051433962856595712713825 9038575472142446784535369)
          ·
            refine ⟨6778931604106835088401527, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9038575472142446784535369 6778931604106835088401527)
            ·
              refine ⟨10168397406160252632602291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6778931604106835088401527 10168397406160252632602291)
              ·
                refine ⟨15252596109240378948903437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10168397406160252632602291 15252596109240378948903437)
                ·
                  refine ⟨5719723540965142105838789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15252596109240378948903437 5719723540965142105838789)
                  ·
                    refine ⟨1072448163930964144844773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5719723540965142105838789 1072448163930964144844773)
                    ·
                      rfl

theorem cell23_6265756_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 2, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 2, 2, 1, 1, 3, 4].length) (baseStart_6265756 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6265756 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6265756 prefixEnd_6265756 := by exact prefixLift 6265756
  have htrace : WordTrace (prefixWord ++ tailWord_6265756) baseStart_6265756 baseEnd_6265756 := by
    simpa [prefixWord, tailWord_6265756, baseEnd_6265756] using wordTrace_append hprefix tailTrace_6265756
  have hstable : (prefixWord ++ tailWord_6265756).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6265756).length < 2 ^ (prefixWord ++ tailWord_6265756).sum := by decide
  have hdescent : baseEnd_6265756 < baseStart_6265756 := by decide
  rcases family_descends (prefixWord ++ tailWord_6265756) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6265795 : List Nat := [1, 1, 1, 3, 1, 1, 2, 6, 1, 6]
def baseStart_6265795 : Nat := 118140960795 + 6265795 * 2 ^ 59
def prefixEnd_6265795 : Nat := 4983230072969 + 3 ^ 40 * 6265795 * 2
def baseEnd_6265795 : Nat := 1072454839179472593982213

theorem tailTrace_6265795 : CollatzResearch.WordTrace tailWord_6265795 prefixEnd_6265795 1072454839179472593982213 := by
  unfold tailWord_6265795
  simp only [CollatzResearch.WordTrace]
  refine ⟨228532318335102302435094839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152354878890068201623396559 228532318335102302435094839)
  ·
    refine ⟨342798477502653453652642259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 228532318335102302435094839 342798477502653453652642259)
    ·
      refine ⟨514197716253980180478963389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 342798477502653453652642259 514197716253980180478963389)
      ·
        refine ⟨192824143595242567679611271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 514197716253980180478963389 192824143595242567679611271)
        ·
          refine ⟨289236215392863851519416907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 192824143595242567679611271 289236215392863851519416907)
          ·
            refine ⟨433854323089295777279125361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 289236215392863851519416907 433854323089295777279125361)
            ·
              refine ⟨325390742316971832959344021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 433854323089295777279125361 325390742316971832959344021)
              ·
                refine ⟨15252691046108054669969251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 325390742316971832959344021 15252691046108054669969251)
                ·
                  refine ⟨22879036569162082004953877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15252691046108054669969251 22879036569162082004953877)
                  ·
                    refine ⟨1072454839179472593982213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 22879036569162082004953877 1072454839179472593982213)
                    ·
                      rfl

theorem cell23_6265795_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 6, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 6, 1, 6].length) (baseStart_6265795 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6265795 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6265795 prefixEnd_6265795 := by exact prefixLift 6265795
  have htrace : WordTrace (prefixWord ++ tailWord_6265795) baseStart_6265795 baseEnd_6265795 := by
    simpa [prefixWord, tailWord_6265795, baseEnd_6265795] using wordTrace_append hprefix tailTrace_6265795
  have hstable : (prefixWord ++ tailWord_6265795).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6265795).length < 2 ^ (prefixWord ++ tailWord_6265795).sum := by decide
  have hdescent : baseEnd_6265795 < baseStart_6265795 := by decide
  rcases family_descends (prefixWord ++ tailWord_6265795) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6265813 : List Nat := [1, 3, 2, 3, 3, 1, 1, 4, 1, 1, 3]
def baseStart_6265813 : Nat := 118140960795 + 6265813 * 2 ^ 59
def prefixEnd_6265813 : Nat := 4983230072969 + 3 ^ 40 * 6265813 * 2
def baseEnd_6265813 : Nat := 3217373760190198711521557

theorem tailTrace_6265813 : CollatzResearch.WordTrace tailWord_6265813 prefixEnd_6265813 3217373760190198711521557 := by
  unfold tailWord_6265813
  simp only [CollatzResearch.WordTrace]
  refine ⟨228532974849037091509250093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152355316566024727672833395 228532974849037091509250093)
  ·
    refine ⟨85699865568388909315968785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 228532974849037091509250093 85699865568388909315968785)
    ·
      refine ⟨64274899176291681986976589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 85699865568388909315968785 64274899176291681986976589)
      ·
        refine ⟨24103087191109380745116221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 64274899176291681986976589 24103087191109380745116221)
        ·
          refine ⟨9038657696666017779418583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24103087191109380745116221 9038657696666017779418583)
          ·
            refine ⟨13557986544999026669127875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9038657696666017779418583 13557986544999026669127875)
            ·
              refine ⟨20336979817498540003691813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13557986544999026669127875 20336979817498540003691813)
              ·
                refine ⟨3813183715780976250692215, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 20336979817498540003691813 3813183715780976250692215)
                ·
                  refine ⟨5719775573671464376038323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3813183715780976250692215 5719775573671464376038323)
                  ·
                    refine ⟨8579663360507196564057485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5719775573671464376038323 8579663360507196564057485)
                    ·
                      refine ⟨3217373760190198711521557, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8579663360507196564057485 3217373760190198711521557)
                      ·
                        rfl

theorem cell23_6265813_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 3, 1, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 3, 1, 1, 4, 1, 1, 3].length) (baseStart_6265813 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6265813 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6265813 prefixEnd_6265813 := by exact prefixLift 6265813
  have htrace : WordTrace (prefixWord ++ tailWord_6265813) baseStart_6265813 baseEnd_6265813 := by
    simpa [prefixWord, tailWord_6265813, baseEnd_6265813] using wordTrace_append hprefix tailTrace_6265813
  have hstable : (prefixWord ++ tailWord_6265813).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6265813).length < 2 ^ (prefixWord ++ tailWord_6265813).sum := by decide
  have hdescent : baseEnd_6265813 < baseStart_6265813 := by decide
  rcases family_descends (prefixWord ++ tailWord_6265813) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6265815 : List Nat := [1, 1, 3, 2, 1, 1, 2, 4, 1, 1, 6]
def baseStart_6265815 : Nat := 118140960795 + 6265815 * 2 ^ 59
def prefixEnd_6265815 : Nat := 4983230072969 + 3 ^ 40 * 6265815 * 2
def baseEnd_6265815 : Nat := 3217374787151507703696547

theorem tailTrace_6265815 : CollatzResearch.WordTrace tailWord_6265815 prefixEnd_6265815 3217374787151507703696547 := by
  unfold tailWord_6265815
  simp only [CollatzResearch.WordTrace]
  refine ⟨228533047795029845850822899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152355365196686563900548599 228533047795029845850822899)
  ·
    refine ⟨342799571692544768776234349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 228533047795029845850822899 342799571692544768776234349)
    ·
      refine ⟨128549839384704288291087881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 342799571692544768776234349 128549839384704288291087881)
      ·
        refine ⟨96412379538528216218315911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 128549839384704288291087881 96412379538528216218315911)
        ·
          refine ⟨144618569307792324327473867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 96412379538528216218315911 144618569307792324327473867)
          ·
            refine ⟨216927853961688486491210801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 144618569307792324327473867 216927853961688486491210801)
            ·
              refine ⟨162695890471266364868408101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 216927853961688486491210801 162695890471266364868408101)
              ·
                refine ⟨30505479463362443412826519, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 162695890471266364868408101 30505479463362443412826519)
                ·
                  refine ⟨45758219195043665119239779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30505479463362443412826519 45758219195043665119239779)
                  ·
                    refine ⟨68637328792565497678859669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 45758219195043665119239779 68637328792565497678859669)
                    ·
                      refine ⟨3217374787151507703696547, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 68637328792565497678859669 3217374787151507703696547)
                      ·
                        rfl

theorem cell23_6265815_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 2, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 2, 4, 1, 1, 6].length) (baseStart_6265815 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6265815 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6265815 prefixEnd_6265815 := by exact prefixLift 6265815
  have htrace : WordTrace (prefixWord ++ tailWord_6265815) baseStart_6265815 baseEnd_6265815 := by
    simpa [prefixWord, tailWord_6265815, baseEnd_6265815] using wordTrace_append hprefix tailTrace_6265815
  have hstable : (prefixWord ++ tailWord_6265815).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6265815).length < 2 ^ (prefixWord ++ tailWord_6265815).sum := by decide
  have hdescent : baseEnd_6265815 < baseStart_6265815 := by decide
  rcases family_descends (prefixWord ++ tailWord_6265815) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6265832 : List Nat := [2, 1, 4, 1, 1, 1, 3, 3, 1, 2, 4]
def baseStart_6265832 : Nat := 118140960795 + 6265832 * 2 ^ 59
def prefixEnd_6265832 : Nat := 4983230072969 + 3 ^ 40 * 6265832 * 2
def baseEnd_6265832 : Nat := 3217383516322634137183969

theorem tailTrace_6265832 : CollatzResearch.WordTrace tailWord_6265832 prefixEnd_6265832 3217383516322634137183969 := by
  unfold tailWord_6265832
  simp only [CollatzResearch.WordTrace]
  refine ⟨114266833917984128877095875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 152355778557312171836127833 114266833917984128877095875)
  ·
    refine ⟨171400250876976193315643813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114266833917984128877095875 171400250876976193315643813)
    ·
      refine ⟨32137547039433036246683215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 171400250876976193315643813 32137547039433036246683215)
      ·
        refine ⟨48206320559149554370024823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32137547039433036246683215 48206320559149554370024823)
        ·
          refine ⟨72309480838724331555037235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48206320559149554370024823 72309480838724331555037235)
          ·
            refine ⟨108464221258086497332555853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 72309480838724331555037235 108464221258086497332555853)
            ·
              refine ⟨40674082971782436499708445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 108464221258086497332555853 40674082971782436499708445)
              ·
                refine ⟨15252781114418413687390667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 40674082971782436499708445 15252781114418413687390667)
                ·
                  refine ⟨22879171671627620531086001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15252781114418413687390667 22879171671627620531086001)
                  ·
                    refine ⟨17159378753720715398314501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 22879171671627620531086001 17159378753720715398314501)
                    ·
                      refine ⟨3217383516322634137183969, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17159378753720715398314501 3217383516322634137183969)
                      ·
                        rfl

theorem cell23_6265832_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 3, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 3, 3, 1, 2, 4].length) (baseStart_6265832 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6265832 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6265832 prefixEnd_6265832 := by exact prefixLift 6265832
  have htrace : WordTrace (prefixWord ++ tailWord_6265832) baseStart_6265832 baseEnd_6265832 := by
    simpa [prefixWord, tailWord_6265832, baseEnd_6265832] using wordTrace_append hprefix tailTrace_6265832
  have hstable : (prefixWord ++ tailWord_6265832).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6265832).length < 2 ^ (prefixWord ++ tailWord_6265832).sum := by decide
  have hdescent : baseEnd_6265832 < baseStart_6265832 := by decide
  rcases family_descends (prefixWord ++ tailWord_6265832) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6265909 : List Nat := [1, 3, 3, 1, 1, 1, 1, 3, 3, 4, 2]
def baseStart_6265909 : Nat := 118140960795 + 6265909 * 2 ^ 59
def prefixEnd_6265909 : Nat := 4983230072969 + 3 ^ 40 * 6265909 * 2
def baseEnd_6265909 : Nat := 3217423054333030335921115

theorem tailTrace_6265909 : CollatzResearch.WordTrace tailWord_6265909 prefixEnd_6265909 3217423054333030335921115 := by
  unfold tailWord_6265909
  simp only [CollatzResearch.WordTrace]
  refine ⟨228536476256689299904744781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152357650837792866603163187 228536476256689299904744781)
  ·
    refine ⟨85701178596258487464279293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 228536476256689299904744781 85701178596258487464279293)
    ·
      refine ⟨32137941973596932799104735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 85701178596258487464279293 32137941973596932799104735)
      ·
        refine ⟨48206912960395399198657103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32137941973596932799104735 48206912960395399198657103)
        ·
          refine ⟨72310369440593098797985655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48206912960395399198657103 72310369440593098797985655)
          ·
            refine ⟨108465554160889648196978483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 72310369440593098797985655 108465554160889648196978483)
            ·
              refine ⟨162698331241334472295467725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 108465554160889648196978483 162698331241334472295467725)
              ·
                refine ⟨61011874215500427110800397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 162698331241334472295467725 61011874215500427110800397)
                ·
                  refine ⟨22879452830812660166550149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 61011874215500427110800397 22879452830812660166550149)
                  ·
                    refine ⟨4289897405777373781228153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 22879452830812660166550149 4289897405777373781228153)
                    ·
                      refine ⟨3217423054333030335921115, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4289897405777373781228153 3217423054333030335921115)
                      ·
                        rfl

theorem cell23_6265909_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 1, 3, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 1, 3, 3, 4, 2].length) (baseStart_6265909 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6265909 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6265909 prefixEnd_6265909 := by exact prefixLift 6265909
  have htrace : WordTrace (prefixWord ++ tailWord_6265909) baseStart_6265909 baseEnd_6265909 := by
    simpa [prefixWord, tailWord_6265909, baseEnd_6265909] using wordTrace_append hprefix tailTrace_6265909
  have hstable : (prefixWord ++ tailWord_6265909).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6265909).length < 2 ^ (prefixWord ++ tailWord_6265909).sum := by decide
  have hdescent : baseEnd_6265909 < baseStart_6265909 := by decide
  rcases family_descends (prefixWord ++ tailWord_6265909) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6265912 : List Nat := [2, 1, 2, 1, 5, 1, 1, 1, 1, 3, 5]
def baseStart_6265912 : Nat := 118140960795 + 6265912 * 2 ^ 59
def prefixEnd_6265912 : Nat := 4983230072969 + 3 ^ 40 * 6265912 * 2
def baseEnd_6265912 : Nat := 3217424594774993824183601

theorem tailTrace_6265912 : CollatzResearch.WordTrace tailWord_6265912 prefixEnd_6265912 3217424594774993824183601 := by
  unfold tailWord_6265912
  simp only [CollatzResearch.WordTrace]
  refine ⟨114268292837839215708551995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 152357723783785620944735993 114268292837839215708551995)
  ·
    refine ⟨171402439256758823562827993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114268292837839215708551995 171402439256758823562827993)
    ·
      refine ⟨128551829442569117672120995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 171402439256758823562827993 128551829442569117672120995)
      ·
        refine ⟨192827744163853676508181493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 128551829442569117672120995 192827744163853676508181493)
        ·
          refine ⟨18077601015361282172642015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 192827744163853676508181493 18077601015361282172642015)
          ·
            refine ⟨27116401523041923258963023, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18077601015361282172642015 27116401523041923258963023)
            ·
              refine ⟨40674602284562884888444535, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27116401523041923258963023 40674602284562884888444535)
              ·
                refine ⟨61011903426844327332666803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40674602284562884888444535 61011903426844327332666803)
                ·
                  refine ⟨91517855140266490999000205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 61011903426844327332666803 91517855140266490999000205)
                  ·
                    refine ⟨34319195677599934124625077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 91517855140266490999000205 34319195677599934124625077)
                    ·
                      refine ⟨3217424594774993824183601, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 34319195677599934124625077 3217424594774993824183601)
                      ·
                        rfl

theorem cell23_6265912_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 1, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 1, 1, 1, 1, 3, 5].length) (baseStart_6265912 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6265912 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6265912 prefixEnd_6265912 := by exact prefixLift 6265912
  have htrace : WordTrace (prefixWord ++ tailWord_6265912) baseStart_6265912 baseEnd_6265912 := by
    simpa [prefixWord, tailWord_6265912, baseEnd_6265912] using wordTrace_append hprefix tailTrace_6265912
  have hstable : (prefixWord ++ tailWord_6265912).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6265912).length < 2 ^ (prefixWord ++ tailWord_6265912).sum := by decide
  have hdescent : baseEnd_6265912 < baseStart_6265912 := by decide
  rcases family_descends (prefixWord ++ tailWord_6265912) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6266077 : List Nat := [1, 4, 3, 2, 2, 2, 1, 3, 1, 4]
def baseStart_6266077 : Nat := 118140960795 + 6266077 * 2 ^ 59
def prefixEnd_6266077 : Nat := 4983230072969 + 3 ^ 40 * 6266077 * 2
def baseEnd_6266077 : Nat := 1072503106360995226206781

theorem tailTrace_6266077 : CollatzResearch.WordTrace tailWord_6266077 prefixEnd_6266077 1072503106360995226206781 := by
  unfold tailWord_6266077
  simp only [CollatzResearch.WordTrace]
  refine ⟨228542603720080664596860485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152361735813387109731240323 228542603720080664596860485)
  ·
    refine ⟨42851738197515124611911341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 228542603720080664596860485 42851738197515124611911341)
    ·
      refine ⟨16069401824068171729466753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 42851738197515124611911341 16069401824068171729466753)
      ·
        refine ⟨12052051368051128797100065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16069401824068171729466753 12052051368051128797100065)
        ·
          refine ⟨9039038526038346597825049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12052051368051128797100065 9039038526038346597825049)
          ·
            refine ⟨6779278894528759948368787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9039038526038346597825049 6779278894528759948368787)
            ·
              refine ⟨10168918341793139922553181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6779278894528759948368787 10168918341793139922553181)
              ·
                refine ⟨3813344378172427470957443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10168918341793139922553181 3813344378172427470957443)
                ·
                  refine ⟨5720016567258641206436165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3813344378172427470957443 5720016567258641206436165)
                  ·
                    refine ⟨1072503106360995226206781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5720016567258641206436165 1072503106360995226206781)
                    ·
                      rfl

theorem cell23_6266077_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 2, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 2, 2, 1, 3, 1, 4].length) (baseStart_6266077 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6266077 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6266077 prefixEnd_6266077 := by exact prefixLift 6266077
  have htrace : WordTrace (prefixWord ++ tailWord_6266077) baseStart_6266077 baseEnd_6266077 := by
    simpa [prefixWord, tailWord_6266077, baseEnd_6266077] using wordTrace_append hprefix tailTrace_6266077
  have hstable : (prefixWord ++ tailWord_6266077).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6266077).length < 2 ^ (prefixWord ++ tailWord_6266077).sum := by decide
  have hdescent : baseEnd_6266077 < baseStart_6266077 := by decide
  rcases family_descends (prefixWord ++ tailWord_6266077) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6266093 : List Nat := [1, 5, 1, 2, 2, 1, 1, 1, 4, 3, 2]
def baseStart_6266093 : Nat := 118140960795 + 6266093 * 2 ^ 59
def prefixEnd_6266093 : Nat := 4983230072969 + 3 ^ 40 * 6266093 * 2
def baseEnd_6266093 : Nat := 3217517534773457616020269

theorem tailTrace_6266093 : CollatzResearch.WordTrace tailWord_6266093 prefixEnd_6266093 3217517534773457616020269 := by
  unfold tailWord_6266093
  simp only [CollatzResearch.WordTrace]
  refine ⟨228543187288022699329442933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152362124858681799552961955 228543187288022699329442933)
  ·
    refine ⟨21425923808252128062135275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 228543187288022699329442933 21425923808252128062135275)
    ·
      refine ⟨32138885712378192093202913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21425923808252128062135275 32138885712378192093202913)
      ·
        refine ⟨24104164284283644069902185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32138885712378192093202913 24104164284283644069902185)
        ·
          refine ⟨18078123213212733052426639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24104164284283644069902185 18078123213212733052426639)
          ·
            refine ⟨27117184819819099578639959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18078123213212733052426639 27117184819819099578639959)
            ·
              refine ⟨40675777229728649367959939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27117184819819099578639959 40675777229728649367959939)
              ·
                refine ⟨61013665844592974051939909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40675777229728649367959939 61013665844592974051939909)
                ·
                  refine ⟨11440062345861182634738733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 61013665844592974051939909 11440062345861182634738733)
                  ·
                    refine ⟨4290023379697943488027025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11440062345861182634738733 4290023379697943488027025)
                    ·
                      refine ⟨3217517534773457616020269, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4290023379697943488027025 3217517534773457616020269)
                      ·
                        rfl

theorem cell23_6266093_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 1, 1, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 1, 1, 1, 4, 3, 2].length) (baseStart_6266093 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6266093 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6266093 prefixEnd_6266093 := by exact prefixLift 6266093
  have htrace : WordTrace (prefixWord ++ tailWord_6266093) baseStart_6266093 baseEnd_6266093 := by
    simpa [prefixWord, tailWord_6266093, baseEnd_6266093] using wordTrace_append hprefix tailTrace_6266093
  have hstable : (prefixWord ++ tailWord_6266093).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6266093).length < 2 ^ (prefixWord ++ tailWord_6266093).sum := by decide
  have hdescent : baseEnd_6266093 < baseStart_6266093 := by decide
  rcases family_descends (prefixWord ++ tailWord_6266093) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6266109 : List Nat := [1, 4, 1, 1, 1, 1, 1, 1, 1, 8, 3]
def baseStart_6266109 : Nat := 118140960795 + 6266109 * 2 ^ 59
def prefixEnd_6266109 : Nat := 4983230072969 + 3 ^ 40 * 6266109 * 2
def baseEnd_6266109 : Nat := 3217525750463929553420195

theorem tailTrace_6266109 : CollatzResearch.WordTrace tailWord_6266109 prefixEnd_6266109 3217525750463929553420195 := by
  unfold tailWord_6266109
  simp only [CollatzResearch.WordTrace]
  refine ⟨228543770855964734062025381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152362513903976489374683587 228543770855964734062025381)
  ·
    refine ⟨42851957035493387636629759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 228543770855964734062025381 42851957035493387636629759)
    ·
      refine ⟨64277935553240081454944639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42851957035493387636629759 64277935553240081454944639)
      ·
        refine ⟨96416903329860122182416959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64277935553240081454944639 96416903329860122182416959)
        ·
          refine ⟨144625354994790183273625439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 96416903329860122182416959 144625354994790183273625439)
          ·
            refine ⟨216938032492185274910438159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 144625354994790183273625439 216938032492185274910438159)
            ·
              refine ⟨325407048738277912365657239, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 216938032492185274910438159 325407048738277912365657239)
              ·
                refine ⟨488110573107416868548485859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 325407048738277912365657239 488110573107416868548485859)
                ·
                  refine ⟨732165859661125302822728789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 488110573107416868548485859 732165859661125302822728789)
                  ·
                    refine ⟨8580068667903812142453853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 732165859661125302822728789 8580068667903812142453853)
                    ·
                      refine ⟨3217525750463929553420195, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8580068667903812142453853 3217525750463929553420195)
                      ·
                        rfl

theorem cell23_6266109_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 1, 1, 1, 8, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 1, 1, 1, 8, 3].length) (baseStart_6266109 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6266109 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6266109 prefixEnd_6266109 := by exact prefixLift 6266109
  have htrace : WordTrace (prefixWord ++ tailWord_6266109) baseStart_6266109 baseEnd_6266109 := by
    simpa [prefixWord, tailWord_6266109, baseEnd_6266109] using wordTrace_append hprefix tailTrace_6266109
  have hstable : (prefixWord ++ tailWord_6266109).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6266109).length < 2 ^ (prefixWord ++ tailWord_6266109).sum := by decide
  have hdescent : baseEnd_6266109 < baseStart_6266109 := by decide
  rcases family_descends (prefixWord ++ tailWord_6266109) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6266120 : List Nat := [2, 1, 3, 2, 5, 1, 1, 2, 1, 5]
def baseStart_6266120 : Nat := 118140960795 + 6266120 * 2 ^ 59
def prefixEnd_6266120 : Nat := 4983230072969 + 3 ^ 40 * 6266120 * 2
def baseEnd_6266120 : Nat := 1072510466250376336794215

theorem tailTrace_6266120 : CollatzResearch.WordTrace tailWord_6266120 prefixEnd_6266120 1072510466250376336794215 := by
  unfold tailWord_6266120
  simp only [CollatzResearch.WordTrace]
  refine ⟨114272086029462441470337907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 152362781372616588627117209 114272086029462441470337907)
  ·
    refine ⟨171408129044193662205506861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114272086029462441470337907 171408129044193662205506861)
    ·
      refine ⟨64278048391572623327065073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 171408129044193662205506861 64278048391572623327065073)
      ·
        refine ⟨48208536293679467495298805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 64278048391572623327065073 48208536293679467495298805)
        ·
          refine ⟨4519550277532450077684263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 48208536293679467495298805 4519550277532450077684263)
          ·
            refine ⟨6779325416298675116526395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4519550277532450077684263 6779325416298675116526395)
            ·
              refine ⟨10168988124448012674789593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6779325416298675116526395 10168988124448012674789593)
              ·
                refine ⟨7626741093336009506092195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10168988124448012674789593 7626741093336009506092195)
                ·
                  refine ⟨11440111640004014259138293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7626741093336009506092195 11440111640004014259138293)
                  ·
                    refine ⟨1072510466250376336794215, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11440111640004014259138293 1072510466250376336794215)
                    ·
                      rfl

theorem cell23_6266120_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 5, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 5, 1, 1, 2, 1, 5].length) (baseStart_6266120 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6266120 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6266120 prefixEnd_6266120 := by exact prefixLift 6266120
  have htrace : WordTrace (prefixWord ++ tailWord_6266120) baseStart_6266120 baseEnd_6266120 := by
    simpa [prefixWord, tailWord_6266120, baseEnd_6266120] using wordTrace_append hprefix tailTrace_6266120
  have hstable : (prefixWord ++ tailWord_6266120).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6266120).length < 2 ^ (prefixWord ++ tailWord_6266120).sum := by decide
  have hdescent : baseEnd_6266120 < baseStart_6266120 := by decide
  rcases family_descends (prefixWord ++ tailWord_6266120) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6266123 : List Nat := [1, 1, 1, 1, 5, 5, 1, 2, 1, 1, 4]
def baseStart_6266123 : Nat := 118140960795 + 6266123 * 2 ^ 59
def prefixEnd_6266123 : Nat := 4983230072969 + 3 ^ 40 * 6266123 * 2
def baseEnd_6266123 : Nat := 3217532939193092498645131

theorem tailTrace_6266123 : CollatzResearch.WordTrace tailWord_6266123 prefixEnd_6266123 3217532939193092498645131 := by
  unfold tailWord_6266123
  simp only [CollatzResearch.WordTrace]
  refine ⟨228544281477914014453035023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152362854318609342968690015 228544281477914014453035023)
  ·
    refine ⟨342816422216871021679552535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 228544281477914014453035023 342816422216871021679552535)
    ·
      refine ⟨514224633325306532519328803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 342816422216871021679552535 514224633325306532519328803)
      ·
        refine ⟨771336949987959798778993205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 514224633325306532519328803 771336949987959798778993205)
        ·
          refine ⟨72312839061371231135530613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 771336949987959798778993205 72312839061371231135530613)
          ·
            refine ⟨6779328662003552918955995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 72312839061371231135530613 6779328662003552918955995)
            ·
              refine ⟨10168992993005329378433993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6779328662003552918955995 10168992993005329378433993)
              ·
                refine ⟨7626744744753997033825495, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10168992993005329378433993 7626744744753997033825495)
                ·
                  refine ⟨11440117117130995550738243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7626744744753997033825495 11440117117130995550738243)
                  ·
                    refine ⟨17160175675696493326107365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11440117117130995550738243 17160175675696493326107365)
                    ·
                      refine ⟨3217532939193092498645131, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17160175675696493326107365 3217532939193092498645131)
                      ·
                        rfl

theorem cell23_6266123_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 5, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 5, 1, 2, 1, 1, 4].length) (baseStart_6266123 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6266123 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6266123 prefixEnd_6266123 := by exact prefixLift 6266123
  have htrace : WordTrace (prefixWord ++ tailWord_6266123) baseStart_6266123 baseEnd_6266123 := by
    simpa [prefixWord, tailWord_6266123, baseEnd_6266123] using wordTrace_append hprefix tailTrace_6266123
  have hstable : (prefixWord ++ tailWord_6266123).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6266123).length < 2 ^ (prefixWord ++ tailWord_6266123).sum := by decide
  have hdescent : baseEnd_6266123 < baseStart_6266123 := by decide
  rcases family_descends (prefixWord ++ tailWord_6266123) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6266136 : List Nat := [2, 1, 2, 3, 1, 4, 1, 2, 1, 2, 4]
def baseStart_6266136 : Nat := 118140960795 + 6266136 * 2 ^ 59
def prefixEnd_6266136 : Nat := 4983230072969 + 3 ^ 40 * 6266136 * 2
def baseEnd_6266136 : Nat := 3217539614441600947782571

theorem tailTrace_6266136 : CollatzResearch.WordTrace tailWord_6266136 prefixEnd_6266136 3217539614441600947782571 := by
  unfold tailWord_6266136
  simp only [CollatzResearch.WordTrace]
  refine ⟨114272377813433458836629131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 152363170417911278448838841 114272377813433458836629131)
  ·
    refine ⟨171408566720150188254943697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114272377813433458836629131 171408566720150188254943697)
    ·
      refine ⟨128556425040112641191207773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 171408566720150188254943697 128556425040112641191207773)
      ·
        refine ⟨48208659390042240446702915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 128556425040112641191207773 48208659390042240446702915)
        ·
          refine ⟨72312989085063360670054373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48208659390042240446702915 72312989085063360670054373)
          ·
            refine ⟨13558685453449380125635195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 72312989085063360670054373 13558685453449380125635195)
            ·
              refine ⟨20338028180174070188452793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13558685453449380125635195 20338028180174070188452793)
              ·
                refine ⟨15253521135130552641339595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20338028180174070188452793 15253521135130552641339595)
                ·
                  refine ⟨22880281702695828962009393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15253521135130552641339595 22880281702695828962009393)
                  ·
                    refine ⟨17160211277021871721507045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 22880281702695828962009393 17160211277021871721507045)
                    ·
                      refine ⟨3217539614441600947782571, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17160211277021871721507045 3217539614441600947782571)
                      ·
                        rfl

theorem cell23_6266136_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 4, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 4, 1, 2, 1, 2, 4].length) (baseStart_6266136 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6266136 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6266136 prefixEnd_6266136 := by exact prefixLift 6266136
  have htrace : WordTrace (prefixWord ++ tailWord_6266136) baseStart_6266136 baseEnd_6266136 := by
    simpa [prefixWord, tailWord_6266136, baseEnd_6266136] using wordTrace_append hprefix tailTrace_6266136
  have hstable : (prefixWord ++ tailWord_6266136).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6266136).length < 2 ^ (prefixWord ++ tailWord_6266136).sum := by decide
  have hdescent : baseEnd_6266136 < baseStart_6266136 := by decide
  rcases family_descends (prefixWord ++ tailWord_6266136) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6266143 : List Nat := [1, 1, 2, 4, 4, 2, 1, 1, 1, 1, 5]
def baseStart_6266143 : Nat := 118140960795 + 6266143 * 2 ^ 59
def prefixEnd_6266143 : Nat := 4983230072969 + 3 ^ 40 * 6266143 * 2
def baseEnd_6266143 : Nat := 3217543208806182420395039

theorem tailTrace_6266143 : CollatzResearch.WordTrace tailWord_6266143 prefixEnd_6266143 3217543208806182420395039 := by
  unfold tailWord_6266143
  simp only [CollatzResearch.WordTrace]
  refine ⟨228545010937841557868763083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152363340625227705245842055 228545010937841557868763083)
  ·
    refine ⟨342817516406762336803144625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 228545010937841557868763083 342817516406762336803144625)
    ·
      refine ⟨257113137305071752602358469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 342817516406762336803144625 257113137305071752602358469)
      ·
        refine ⟨48208713244700953612942213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 257113137305071752602358469 48208713244700953612942213)
        ·
          refine ⟨9039133733381428802426665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 48208713244700953612942213 9039133733381428802426665)
          ·
            refine ⟨6779350300036071601819999, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9039133733381428802426665 6779350300036071601819999)
            ·
              refine ⟨10169025450054107402729999, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6779350300036071601819999 10169025450054107402729999)
              ·
                refine ⟨15253538175081161104094999, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10169025450054107402729999 15253538175081161104094999)
                ·
                  refine ⟨22880307262621741656142499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15253538175081161104094999 22880307262621741656142499)
                  ·
                    refine ⟨34320460893932612484213749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 22880307262621741656142499 34320460893932612484213749)
                    ·
                      refine ⟨3217543208806182420395039, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 34320460893932612484213749 3217543208806182420395039)
                      ·
                        rfl

theorem cell23_6266143_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 4, 2, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 4, 2, 1, 1, 1, 1, 5].length) (baseStart_6266143 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6266143 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6266143 prefixEnd_6266143 := by exact prefixLift 6266143
  have htrace : WordTrace (prefixWord ++ tailWord_6266143) baseStart_6266143 baseEnd_6266143 := by
    simpa [prefixWord, tailWord_6266143, baseEnd_6266143] using wordTrace_append hprefix tailTrace_6266143
  have hstable : (prefixWord ++ tailWord_6266143).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6266143).length < 2 ^ (prefixWord ++ tailWord_6266143).sum := by decide
  have hdescent : baseEnd_6266143 < baseStart_6266143 := by decide
  rcases family_descends (prefixWord ++ tailWord_6266143) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6266146 : List Nat := [3, 3, 1, 1, 5, 10]
def baseStart_6266146 : Nat := 118140960795 + 6266146 * 2 ^ 59
def prefixEnd_6266146 : Nat := 4983230072969 + 3 ^ 40 * 6266146 * 2
def baseEnd_6266146 : Nat := 13240924894025291805175

theorem tailTrace_6266146 : CollatzResearch.WordTrace tailWord_6266146 prefixEnd_6266146 13240924894025291805175 := by
  unfold tailWord_6266146
  simp only [CollatzResearch.WordTrace]
  refine ⟨57136280089207672345280573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 152363413571220459587414861 57136280089207672345280573)
  ·
    refine ⟨21426105033452877129480215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 57136280089207672345280573 21426105033452877129480215)
    ·
      refine ⟨32139157550179315694220323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21426105033452877129480215 32139157550179315694220323)
      ·
        refine ⟨48208736325268973541330485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32139157550179315694220323 48208736325268973541330485)
        ·
          refine ⟨4519569030493966269499733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 48208736325268973541330485 4519569030493966269499733)
          ·
            refine ⟨13240924894025291805175, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 4519569030493966269499733 13240924894025291805175)
            ·
              rfl

theorem cell23_6266146_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 5, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 5, 10].length) (baseStart_6266146 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6266146 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6266146 prefixEnd_6266146 := by exact prefixLift 6266146
  have htrace : WordTrace (prefixWord ++ tailWord_6266146) baseStart_6266146 baseEnd_6266146 := by
    simpa [prefixWord, tailWord_6266146, baseEnd_6266146] using wordTrace_append hprefix tailTrace_6266146
  have hstable : (prefixWord ++ tailWord_6266146).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6266146).length < 2 ^ (prefixWord ++ tailWord_6266146).sum := by decide
  have hdescent : baseEnd_6266146 < baseStart_6266146 := by decide
  rcases family_descends (prefixWord ++ tailWord_6266146) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6266179 : List Nat := [1, 1, 1, 3, 1, 3, 1, 1, 4, 3, 4]
def baseStart_6266179 : Nat := 118140960795 + 6266179 * 2 ^ 59
def prefixEnd_6266179 : Nat := 4983230072969 + 3 ^ 40 * 6266179 * 2
def baseEnd_6266179 : Nat := 3217561694109744279544873

theorem tailTrace_6266179 : CollatzResearch.WordTrace tailWord_6266179 prefixEnd_6266179 3217561694109744279544873 := by
  unfold tailWord_6266179
  simp only [CollatzResearch.WordTrace]
  refine ⟨228546323965711136017073591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152364215977140757344715727 228546323965711136017073591)
  ·
    refine ⟨342819485948566704025610387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 228546323965711136017073591 342819485948566704025610387)
    ·
      refine ⟨514229228922850056038415581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 342819485948566704025610387 514229228922850056038415581)
      ·
        refine ⟨192835960846068771014405843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 514229228922850056038415581 192835960846068771014405843)
        ·
          refine ⟨289253941269103156521608765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 192835960846068771014405843 289253941269103156521608765)
          ·
            refine ⟨108470227975913683695603287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 289253941269103156521608765 108470227975913683695603287)
            ·
              refine ⟨162705341963870525543404931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 108470227975913683695603287 162705341963870525543404931)
              ·
                refine ⟨244058012945805788315107397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 162705341963870525543404931 244058012945805788315107397)
                ·
                  refine ⟨45760877427338585309082637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 244058012945805788315107397 45760877427338585309082637)
                  ·
                    refine ⟨17160329035251969490905989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 45760877427338585309082637 17160329035251969490905989)
                    ·
                      refine ⟨3217561694109744279544873, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17160329035251969490905989 3217561694109744279544873)
                      ·
                        rfl

theorem cell23_6266179_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 1, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 1, 1, 4, 3, 4].length) (baseStart_6266179 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6266179 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6266179 prefixEnd_6266179 := by exact prefixLift 6266179
  have htrace : WordTrace (prefixWord ++ tailWord_6266179) baseStart_6266179 baseEnd_6266179 := by
    simpa [prefixWord, tailWord_6266179, baseEnd_6266179] using wordTrace_append hprefix tailTrace_6266179
  have hstable : (prefixWord ++ tailWord_6266179).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6266179).length < 2 ^ (prefixWord ++ tailWord_6266179).sum := by decide
  have hdescent : baseEnd_6266179 < baseStart_6266179 := by decide
  rcases family_descends (prefixWord ++ tailWord_6266179) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6266183 : List Nat := [1, 1, 4, 1, 2, 3, 2, 1, 3, 3, 2]
def baseStart_6266183 : Nat := 118140960795 + 6266183 * 2 ^ 59
def prefixEnd_6266183 : Nat := 4983230072969 + 3 ^ 40 * 6266183 * 2
def baseEnd_6266183 : Nat := 3217563748032362263894855

theorem tailTrace_6266183 : CollatzResearch.WordTrace tailWord_6266183 prefixEnd_6266183 3217563748032362263894855 := by
  unfold tailWord_6266183
  simp only [CollatzResearch.WordTrace]
  refine ⟨228546469857696644700219203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152364313238464429800146135 228546469857696644700219203)
  ·
    refine ⟨342819704786544967050328805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 228546469857696644700219203 342819704786544967050328805)
    ·
      refine ⟨64278694647477181321936651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 342819704786544967050328805 64278694647477181321936651)
      ·
        refine ⟨96418041971215771982904977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64278694647477181321936651 96418041971215771982904977)
        ·
          refine ⟨72313531478411828987178733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 96418041971215771982904977 72313531478411828987178733)
          ·
            refine ⟨27117574304404435870192025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 72313531478411828987178733 27117574304404435870192025)
            ·
              refine ⟨20338180728303326902644019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27117574304404435870192025 20338180728303326902644019)
              ·
                refine ⟨30507271092454990353966029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20338180728303326902644019 30507271092454990353966029)
                ·
                  refine ⟨11440226659670621382737261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 30507271092454990353966029 11440226659670621382737261)
                  ·
                    refine ⟨4290084997376483018526473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11440226659670621382737261 4290084997376483018526473)
                    ·
                      refine ⟨3217563748032362263894855, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4290084997376483018526473 3217563748032362263894855)
                      ·
                        rfl

theorem cell23_6266183_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 3, 2, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 3, 2, 1, 3, 3, 2].length) (baseStart_6266183 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6266183 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6266183 prefixEnd_6266183 := by exact prefixLift 6266183
  have htrace : WordTrace (prefixWord ++ tailWord_6266183) baseStart_6266183 baseEnd_6266183 := by
    simpa [prefixWord, tailWord_6266183, baseEnd_6266183] using wordTrace_append hprefix tailTrace_6266183
  have hstable : (prefixWord ++ tailWord_6266183).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6266183).length < 2 ^ (prefixWord ++ tailWord_6266183).sum := by decide
  have hdescent : baseEnd_6266183 < baseStart_6266183 := by decide
  rcases family_descends (prefixWord ++ tailWord_6266183) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6266226 : List Nat := [3, 2, 1, 2, 1, 2, 1, 3, 2, 2, 4]
def baseStart_6266226 : Nat := 118140960795 + 6266226 * 2 ^ 59
def prefixEnd_6266226 : Nat := 4983230072969 + 3 ^ 40 * 6266226 * 2
def baseEnd_6266226 : Nat := 3217585827700505595657157

theorem tailTrace_6266226 : CollatzResearch.WordTrace tailWord_6266226 prefixEnd_6266226 3217585827700505595657157 := by
  unfold tailWord_6266226
  simp only [CollatzResearch.WordTrace]
  refine ⟨57137009549135215761008633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 152365358797693908696023021 57137009549135215761008633)
  ·
    refine ⟨42852757161851411820756475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57137009549135215761008633 42852757161851411820756475)
    ·
      refine ⟨64279135742777117731134713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42852757161851411820756475 64279135742777117731134713)
      ·
        refine ⟨48209351807082838298351035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 64279135742777117731134713 48209351807082838298351035)
        ·
          refine ⟨72314027710624257447526553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48209351807082838298351035 72314027710624257447526553)
          ·
            refine ⟨54235520782968193085644915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 72314027710624257447526553 54235520782968193085644915)
            ·
              refine ⟨81353281174452289628467373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 54235520782968193085644915 81353281174452289628467373)
              ·
                refine ⟨30507480440419608610675265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 81353281174452289628467373 30507480440419608610675265)
                ·
                  refine ⟨22880610330314706458006449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 30507480440419608610675265 22880610330314706458006449)
                  ·
                    refine ⟨17160457747736029843504837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 22880610330314706458006449 17160457747736029843504837)
                    ·
                      refine ⟨3217585827700505595657157, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17160457747736029843504837 3217585827700505595657157)
                      ·
                        rfl

theorem cell23_6266226_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 1, 3, 2, 2, 4].length) (baseStart_6266226 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6266226 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6266226 prefixEnd_6266226 := by exact prefixLift 6266226
  have htrace : WordTrace (prefixWord ++ tailWord_6266226) baseStart_6266226 baseEnd_6266226 := by
    simpa [prefixWord, tailWord_6266226, baseEnd_6266226] using wordTrace_append hprefix tailTrace_6266226
  have hstable : (prefixWord ++ tailWord_6266226).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6266226).length < 2 ^ (prefixWord ++ tailWord_6266226).sum := by decide
  have hdescent : baseEnd_6266226 < baseStart_6266226 := by decide
  rcases family_descends (prefixWord ++ tailWord_6266226) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6266259 : List Nat := [1, 1, 1, 2, 1, 2, 1, 1, 5, 1, 7]
def baseStart_6266259 : Nat := 118140960795 + 6266259 * 2 ^ 59
def prefixEnd_6266259 : Nat := 4983230072969 + 3 ^ 40 * 6266259 * 2
def baseEnd_6266259 : Nat := 3217602772562103966544505

theorem tailTrace_6266259 : CollatzResearch.WordTrace tailWord_6266259 prefixEnd_6266259 3217602772562103966544505 := by
  unfold tailWord_6266259
  simp only [CollatzResearch.WordTrace]
  refine ⟨228549241805421309679985831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152366161203614206453323887 228549241805421309679985831)
  ·
    refine ⟨342823862708131964519978747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 228549241805421309679985831 342823862708131964519978747)
    ·
      refine ⟨514235794062197946779968121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 342823862708131964519978747 514235794062197946779968121)
      ·
        refine ⟨385676845546648460084976091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 514235794062197946779968121 385676845546648460084976091)
        ·
          refine ⟨578515268319972690127464137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 385676845546648460084976091 578515268319972690127464137)
          ·
            refine ⟨433886451239979517595598103, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 578515268319972690127464137 433886451239979517595598103)
            ·
              refine ⟨650829676859969276393397155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 433886451239979517595598103 650829676859969276393397155)
              ·
                refine ⟨976244515289953914590095733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 650829676859969276393397155 976244515289953914590095733)
                ·
                  refine ⟨91522923308433179492821475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 976244515289953914590095733 91522923308433179492821475)
                  ·
                    refine ⟨137284384962649769239232213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 91522923308433179492821475 137284384962649769239232213)
                    ·
                      refine ⟨3217602772562103966544505, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 137284384962649769239232213 3217602772562103966544505)
                      ·
                        rfl

theorem cell23_6266259_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 1, 5, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 1, 5, 1, 7].length) (baseStart_6266259 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6266259 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6266259 prefixEnd_6266259 := by exact prefixLift 6266259
  have htrace : WordTrace (prefixWord ++ tailWord_6266259) baseStart_6266259 baseEnd_6266259 := by
    simpa [prefixWord, tailWord_6266259, baseEnd_6266259] using wordTrace_append hprefix tailTrace_6266259
  have hstable : (prefixWord ++ tailWord_6266259).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6266259).length < 2 ^ (prefixWord ++ tailWord_6266259).sum := by decide
  have hdescent : baseEnd_6266259 < baseStart_6266259 := by decide
  rcases family_descends (prefixWord ++ tailWord_6266259) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6266300 : List Nat := [2, 2, 2, 4, 2, 1, 2, 1, 2, 5]
def baseStart_6266300 : Nat := 118140960795 + 6266300 * 2 ^ 59
def prefixEnd_6266300 : Nat := 4983230072969 + 3 ^ 40 * 6266300 * 2
def baseEnd_6266300 : Nat := 1072541275089646102043939

theorem tailTrace_6266300 : CollatzResearch.WordTrace tailWord_6266300 prefixEnd_6266300 1072541275089646102043939 := by
  unfold tailWord_6266300
  simp only [CollatzResearch.WordTrace]
  refine ⟨114275368599136386841114177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 152367158132181849121485569 114275368599136386841114177)
  ·
    refine ⟨85706526449352290130835633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 114275368599136386841114177 85706526449352290130835633)
    ·
      refine ⟨64279894837014217598126725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 85706526449352290130835633 64279894837014217598126725)
      ·
        refine ⟨12052480281940165799648761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 64279894837014217598126725 12052480281940165799648761)
        ·
          refine ⟨9039360211455124349736571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12052480281940165799648761 9039360211455124349736571)
          ·
            refine ⟨13559040317182686524604857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9039360211455124349736571 13559040317182686524604857)
            ·
              refine ⟨10169280237887014893453643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13559040317182686524604857 10169280237887014893453643)
              ·
                refine ⟨15253920356830522340180465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10169280237887014893453643 15253920356830522340180465)
                ·
                  refine ⟨11440440267622891755135349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15253920356830522340180465 11440440267622891755135349)
                  ·
                    refine ⟨1072541275089646102043939, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11440440267622891755135349 1072541275089646102043939)
                    ·
                      rfl

theorem cell23_6266300_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 2, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 2, 1, 2, 1, 2, 5].length) (baseStart_6266300 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6266300 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6266300 prefixEnd_6266300 := by exact prefixLift 6266300
  have htrace : WordTrace (prefixWord ++ tailWord_6266300) baseStart_6266300 baseEnd_6266300 := by
    simpa [prefixWord, tailWord_6266300, baseEnd_6266300] using wordTrace_append hprefix tailTrace_6266300
  have hstable : (prefixWord ++ tailWord_6266300).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6266300).length < 2 ^ (prefixWord ++ tailWord_6266300).sum := by decide
  have hdescent : baseEnd_6266300 < baseStart_6266300 := by decide
  rcases family_descends (prefixWord ++ tailWord_6266300) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6266343 : List Nat := [1, 1, 5, 2, 1, 2, 2, 3, 6]
def baseStart_6266343 : Nat := 118140960795 + 6266343 * 2 ^ 59
def prefixEnd_6266343 : Nat := 4983230072969 + 3 ^ 40 * 6266343 * 2
def baseEnd_6266343 : Nat := 357516211659675737543791

theorem tailTrace_6266343 : CollatzResearch.WordTrace tailWord_6266343 prefixEnd_6266343 357516211659675737543791 := by
  unfold tailWord_6266343
  simp only [CollatzResearch.WordTrace]
  refine ⟨228552305537116992026043683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152368203691411328017362455 228552305537116992026043683)
  ·
    refine ⟨342828458305675488039065525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 228552305537116992026043683 342828458305675488039065525)
    ·
      refine ⟨32140167966157077003662393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 342828458305675488039065525 32140167966157077003662393)
      ·
        refine ⟨24105125974617807752746795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32140167966157077003662393 24105125974617807752746795)
        ·
          refine ⟨36157688961926711629120193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24105125974617807752746795 36157688961926711629120193)
          ·
            refine ⟨27118266721445033721840145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36157688961926711629120193 27118266721445033721840145)
            ·
              refine ⟨20338700041083775291380109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27118266721445033721840145 20338700041083775291380109)
              ·
                refine ⟨7627012515406415734267541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20338700041083775291380109 7627012515406415734267541)
                ·
                  refine ⟨357516211659675737543791, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7627012515406415734267541 357516211659675737543791)
                  ·
                    rfl

theorem cell23_6266343_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 2, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 2, 2, 3, 6].length) (baseStart_6266343 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6266343 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6266343 prefixEnd_6266343 := by exact prefixLift 6266343
  have htrace : WordTrace (prefixWord ++ tailWord_6266343) baseStart_6266343 baseEnd_6266343 := by
    simpa [prefixWord, tailWord_6266343, baseEnd_6266343] using wordTrace_append hprefix tailTrace_6266343
  have hstable : (prefixWord ++ tailWord_6266343).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6266343).length < 2 ^ (prefixWord ++ tailWord_6266343).sum := by decide
  have hdescent : baseEnd_6266343 < baseStart_6266343 := by decide
  rcases family_descends (prefixWord ++ tailWord_6266343) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6266357 : List Nat := [1, 3, 5, 1, 1, 1, 3, 1, 2, 2, 3]
def baseStart_6266357 : Nat := 118140960795 + 6266357 * 2 ^ 59
def prefixEnd_6266357 : Nat := 4983230072969 + 3 ^ 40 * 6266357 * 2
def baseEnd_6266357 : Nat := 3217653093666244583119055

theorem tailTrace_6266357 : CollatzResearch.WordTrace tailWord_6266357 prefixEnd_6266357 3217653093666244583119055 := by
  unfold tailWord_6266357
  simp only [CollatzResearch.WordTrace]
  refine ⟨228552816159066272417053325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152368544106044181611368883 228552816159066272417053325)
  ·
    refine ⟨85707306059649852156394997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 228552816159066272417053325 85707306059649852156394997)
    ·
      refine ⟨8035059943092173639662031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 85707306059649852156394997 8035059943092173639662031)
      ·
        refine ⟨12052589914638260459493047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8035059943092173639662031 12052589914638260459493047)
        ·
          refine ⟨18078884871957390689239571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12052589914638260459493047 18078884871957390689239571)
          ·
            refine ⟨27118327307936086033859357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18078884871957390689239571 27118327307936086033859357)
            ·
              refine ⟨10169372740476032262697259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27118327307936086033859357 10169372740476032262697259)
              ·
                refine ⟨15254059110714048394045889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10169372740476032262697259 15254059110714048394045889)
                ·
                  refine ⟨11440544333035536295534417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15254059110714048394045889 11440544333035536295534417)
                  ·
                    refine ⟨8580408249776652221650813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11440544333035536295534417 8580408249776652221650813)
                    ·
                      refine ⟨3217653093666244583119055, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8580408249776652221650813 3217653093666244583119055)
                      ·
                        rfl

theorem cell23_6266357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 1, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 1, 3, 1, 2, 2, 3].length) (baseStart_6266357 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6266357 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6266357 prefixEnd_6266357 := by exact prefixLift 6266357
  have htrace : WordTrace (prefixWord ++ tailWord_6266357) baseStart_6266357 baseEnd_6266357 := by
    simpa [prefixWord, tailWord_6266357, baseEnd_6266357] using wordTrace_append hprefix tailTrace_6266357
  have hstable : (prefixWord ++ tailWord_6266357).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6266357).length < 2 ^ (prefixWord ++ tailWord_6266357).sum := by decide
  have hdescent : baseEnd_6266357 < baseStart_6266357 := by decide
  rcases family_descends (prefixWord ++ tailWord_6266357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6266363 : List Nat := [1, 1, 1, 1, 1, 3, 2, 5, 1, 5, 2]
def baseStart_6266363 : Nat := 118140960795 + 6266363 * 2 ^ 59
def prefixEnd_6266363 : Nat := 4983230072969 + 3 ^ 40 * 6266363 * 2
def baseEnd_6266363 : Nat := 3217656174550171559644027

theorem tailTrace_6266363 : CollatzResearch.WordTrace tailWord_6266363 prefixEnd_6266363 3217656174550171559644027 := by
  unfold tailWord_6266363
  simp only [CollatzResearch.WordTrace]
  refine ⟨228553034997044535441771743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152368689998029690294514495 228553034997044535441771743)
  ·
    refine ⟨342829552495566803162657615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 228553034997044535441771743 342829552495566803162657615)
    ·
      refine ⟨514244328743350204743986423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 342829552495566803162657615 514244328743350204743986423)
      ·
        refine ⟨771366493115025307115979635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 514244328743350204743986423 771366493115025307115979635)
        ·
          refine ⟨1157049739672537960673969453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 771366493115025307115979635 1157049739672537960673969453)
          ·
            refine ⟨433893652377201735252738545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1157049739672537960673969453 433893652377201735252738545)
            ·
              refine ⟨325420239282901301439553909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 433893652377201735252738545 325420239282901301439553909)
              ·
                refine ⟨30508147432771997009958179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 325420239282901301439553909 30508147432771997009958179)
                ·
                  refine ⟨45762221149157995514937269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30508147432771997009958179 45762221149157995514937269)
                  ·
                    refine ⟨4290208232733562079525369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 45762221149157995514937269 4290208232733562079525369)
                    ·
                      refine ⟨3217656174550171559644027, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4290208232733562079525369 3217656174550171559644027)
                      ·
                        rfl

theorem cell23_6266363_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 2, 5, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 2, 5, 1, 5, 2].length) (baseStart_6266363 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6266363 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6266363 prefixEnd_6266363 := by exact prefixLift 6266363
  have htrace : WordTrace (prefixWord ++ tailWord_6266363) baseStart_6266363 baseEnd_6266363 := by
    simpa [prefixWord, tailWord_6266363, baseEnd_6266363] using wordTrace_append hprefix tailTrace_6266363
  have hstable : (prefixWord ++ tailWord_6266363).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6266363).length < 2 ^ (prefixWord ++ tailWord_6266363).sum := by decide
  have hdescent : baseEnd_6266363 < baseStart_6266363 := by decide
  rcases family_descends (prefixWord ++ tailWord_6266363) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6266387 : List Nat := [1, 1, 1, 2, 1, 6, 2, 4, 1, 1, 3]
def baseStart_6266387 : Nat := 118140960795 + 6266387 * 2 ^ 59
def prefixEnd_6266387 : Nat := 4983230072969 + 3 ^ 40 * 6266387 * 2
def baseEnd_6266387 : Nat := 3217668498085879465743917

theorem tailTrace_6266387 : CollatzResearch.WordTrace tailWord_6266387 prefixEnd_6266387 3217668498085879465743917 := by
  unfold tailWord_6266387
  simp only [CollatzResearch.WordTrace]
  refine ⟨228553910348957587540645415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152369273565971725027096943 228553910348957587540645415)
  ·
    refine ⟨342830865523436381310968123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 228553910348957587540645415 342830865523436381310968123)
    ·
      refine ⟨514246298285154571966452185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 342830865523436381310968123 514246298285154571966452185)
      ·
        refine ⟨385684723713865928974839139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 514246298285154571966452185 385684723713865928974839139)
        ·
          refine ⟨578527085570798893462258709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 385684723713865928974839139 578527085570798893462258709)
          ·
            refine ⟨27118457136131198131043377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 578527085570798893462258709 27118457136131198131043377)
            ·
              refine ⟨20338842852098398598282533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27118457136131198131043377 20338842852098398598282533)
              ·
                refine ⟨3813533034768449737177975, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 20338842852098398598282533 3813533034768449737177975)
                ·
                  refine ⟨5720299552152674605766963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3813533034768449737177975 5720299552152674605766963)
                  ·
                    refine ⟨8580449328229011908650445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5720299552152674605766963 8580449328229011908650445)
                    ·
                      refine ⟨3217668498085879465743917, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8580449328229011908650445 3217668498085879465743917)
                      ·
                        rfl

theorem cell23_6266387_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 6, 2, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 6, 2, 4, 1, 1, 3].length) (baseStart_6266387 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6266387 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6266387 prefixEnd_6266387 := by exact prefixLift 6266387
  have htrace : WordTrace (prefixWord ++ tailWord_6266387) baseStart_6266387 baseEnd_6266387 := by
    simpa [prefixWord, tailWord_6266387, baseEnd_6266387] using wordTrace_append hprefix tailTrace_6266387
  have hstable : (prefixWord ++ tailWord_6266387).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6266387).length < 2 ^ (prefixWord ++ tailWord_6266387).sum := by decide
  have hdescent : baseEnd_6266387 < baseStart_6266387 := by decide
  rcases family_descends (prefixWord ++ tailWord_6266387) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6266393 : List Nat := [1, 2, 1, 2, 1, 1, 2, 1, 4, 6, 2]
def baseStart_6266393 : Nat := 118140960795 + 6266393 * 2 ^ 59
def prefixEnd_6266393 : Nat := 4983230072969 + 3 ^ 40 * 6266393 * 2
def baseEnd_6266393 : Nat := 3217671578969806442268889

theorem tailTrace_6266393 : CollatzResearch.WordTrace tailWord_6266393 prefixEnd_6266393 3217671578969806442268889 := by
  unfold tailWord_6266393
  simp only [CollatzResearch.WordTrace]
  refine ⟨228554129186935850565363833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152369419457957233710242555 228554129186935850565363833)
  ·
    refine ⟨171415596890201887924022875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 228554129186935850565363833 171415596890201887924022875)
    ·
      refine ⟨257123395335302831886034313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 171415596890201887924022875 257123395335302831886034313)
      ·
        refine ⟨192842546501477123914525735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 257123395335302831886034313 192842546501477123914525735)
        ·
          refine ⟨289263819752215685871788603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 192842546501477123914525735 289263819752215685871788603)
          ·
            refine ⟨433895729628323528807682905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 289263819752215685871788603 433895729628323528807682905)
            ·
              refine ⟨325421797221242646605762179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 433895729628323528807682905 325421797221242646605762179)
              ·
                refine ⟨488132695831863969908643269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 325421797221242646605762179 488132695831863969908643269)
                ·
                  refine ⟨91524880468474494357870613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 488132695831863969908643269 91524880468474494357870613)
                  ·
                    refine ⟨4290228771959741923025185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 91524880468474494357870613 4290228771959741923025185)
                    ·
                      refine ⟨3217671578969806442268889, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4290228771959741923025185 3217671578969806442268889)
                      ·
                        rfl

theorem cell23_6266393_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 2, 1, 4, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 2, 1, 4, 6, 2].length) (baseStart_6266393 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6266393 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6266393 prefixEnd_6266393 := by exact prefixLift 6266393
  have htrace : WordTrace (prefixWord ++ tailWord_6266393) baseStart_6266393 baseEnd_6266393 := by
    simpa [prefixWord, tailWord_6266393, baseEnd_6266393] using wordTrace_append hprefix tailTrace_6266393
  have hstable : (prefixWord ++ tailWord_6266393).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6266393).length < 2 ^ (prefixWord ++ tailWord_6266393).sum := by decide
  have hdescent : baseEnd_6266393 < baseStart_6266393 := by decide
  rcases family_descends (prefixWord ++ tailWord_6266393) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6266410 : List Nat := [3, 1, 4, 1, 1, 1, 1, 1, 2, 6, 2]
def baseStart_6266410 : Nat := 118140960795 + 6266410 * 2 ^ 59
def prefixEnd_6266410 : Nat := 4983230072969 + 3 ^ 40 * 6266410 * 2
def baseEnd_6266410 : Nat := 3217680308140932875756311

theorem tailTrace_6266410 : CollatzResearch.WordTrace tailWord_6266410 prefixEnd_6266410 3217680308140932875756311 := by
  unfold tailWord_6266410
  simp only [CollatzResearch.WordTrace]
  refine ⟨57138687306968565617183171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 152369832818582841645821789 57138687306968565617183171)
  ·
    refine ⟨85708030960452848425774757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57138687306968565617183171 85708030960452848425774757)
    ·
      refine ⟨16070255805084909079832767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 85708030960452848425774757 16070255805084909079832767)
      ·
        refine ⟨24105383707627363619749151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16070255805084909079832767 24105383707627363619749151)
        ·
          refine ⟨36158075561441045429623727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24105383707627363619749151 36158075561441045429623727)
          ·
            refine ⟨54237113342161568144435591, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36158075561441045429623727 54237113342161568144435591)
            ·
              refine ⟨81355670013242352216653387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 54237113342161568144435591 81355670013242352216653387)
              ·
                refine ⟨122033505019863528324980081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 81355670013242352216653387 122033505019863528324980081)
                ·
                  refine ⟨91525128764897646243735061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 122033505019863528324980081 91525128764897646243735061)
                  ·
                    refine ⟨4290240410854577167675081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 91525128764897646243735061 4290240410854577167675081)
                    ·
                      refine ⟨3217680308140932875756311, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4290240410854577167675081 3217680308140932875756311)
                      ·
                        rfl

theorem cell23_6266410_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 1, 1, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 1, 1, 2, 6, 2].length) (baseStart_6266410 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6266410 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6266410 prefixEnd_6266410 := by exact prefixLift 6266410
  have htrace : WordTrace (prefixWord ++ tailWord_6266410) baseStart_6266410 baseEnd_6266410 := by
    simpa [prefixWord, tailWord_6266410, baseEnd_6266410] using wordTrace_append hprefix tailTrace_6266410
  have hstable : (prefixWord ++ tailWord_6266410).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6266410).length < 2 ^ (prefixWord ++ tailWord_6266410).sum := by decide
  have hdescent : baseEnd_6266410 < baseStart_6266410 := by decide
  rcases family_descends (prefixWord ++ tailWord_6266410) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6266438 : List Nat := [6, 1, 1, 1, 4, 1, 1, 1, 3, 1, 3]
def baseStart_6266438 : Nat := 118140960795 + 6266438 * 2 ^ 59
def prefixEnd_6266438 : Nat := 4983230072969 + 3 ^ 40 * 6266438 * 2
def baseEnd_6266438 : Nat := 3217694685599258766206183

theorem tailTrace_6266438 : CollatzResearch.WordTrace tailWord_6266438 prefixEnd_6266438 3217694685599258766206183 := by
  unfold tailWord_6266438
  simp only [CollatzResearch.WordTrace]
  refine ⟨7142367827242900726585999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 152370513647848548833834645 7142367827242900726585999)
  ·
    refine ⟨10713551740864351089878999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7142367827242900726585999 10713551740864351089878999)
    ·
      refine ⟨16070327611296526634818499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10713551740864351089878999 16070327611296526634818499)
      ·
        refine ⟨24105491416944789952227749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16070327611296526634818499 24105491416944789952227749)
        ·
          refine ⟨4519779640677148116042703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 24105491416944789952227749 4519779640677148116042703)
          ·
            refine ⟨6779669461015722174064055, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4519779640677148116042703 6779669461015722174064055)
            ·
              refine ⟨10169504191523583261096083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6779669461015722174064055 10169504191523583261096083)
              ·
                refine ⟨15254256287285374891644125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10169504191523583261096083 15254256287285374891644125)
                ·
                  refine ⟨5720346107732015584366547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15254256287285374891644125 5720346107732015584366547)
                  ·
                    refine ⟨8580519161598023376549821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5720346107732015584366547 8580519161598023376549821)
                    ·
                      refine ⟨3217694685599258766206183, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8580519161598023376549821 3217694685599258766206183)
                      ·
                        rfl

theorem cell23_6266438_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 4, 1, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 4, 1, 1, 1, 3, 1, 3].length) (baseStart_6266438 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6266438 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6266438 prefixEnd_6266438 := by exact prefixLift 6266438
  have htrace : WordTrace (prefixWord ++ tailWord_6266438) baseStart_6266438 baseEnd_6266438 := by
    simpa [prefixWord, tailWord_6266438, baseEnd_6266438] using wordTrace_append hprefix tailTrace_6266438
  have hstable : (prefixWord ++ tailWord_6266438).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6266438).length < 2 ^ (prefixWord ++ tailWord_6266438).sum := by decide
  have hdescent : baseEnd_6266438 < baseStart_6266438 := by decide
  rcases family_descends (prefixWord ++ tailWord_6266438) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6266444 : List Nat := [2, 2, 1, 3, 1, 5, 1, 1, 3, 2, 2]
def baseStart_6266444 : Nat := 118140960795 + 6266444 * 2 ^ 59
def prefixEnd_6266444 : Nat := 4983230072969 + 3 ^ 40 * 6266444 * 2
def baseEnd_6266444 : Nat := 3217697766483185742731155

theorem tailTrace_6266444 : CollatzResearch.WordTrace tailWord_6266444 prefixEnd_6266444 3217697766483185742731155 := by
  unfold tailWord_6266444
  simp only [CollatzResearch.WordTrace]
  refine ⟨114277994654875543137735193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 152370659539834057516980257 114277994654875543137735193)
  ·
    refine ⟨85708495991156657353301395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 114277994654875543137735193 85708495991156657353301395)
    ·
      refine ⟨128562743986734986029952093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85708495991156657353301395 128562743986734986029952093)
      ·
        refine ⟨48211028995025619761232035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 128562743986734986029952093 48211028995025619761232035)
        ·
          refine ⟨72316543492538429641848053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48211028995025619761232035 72316543492538429641848053)
          ·
            refine ⟨6779675952425477778923255, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 72316543492538429641848053 6779675952425477778923255)
            ·
              refine ⟨10169513928638216668384883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6779675952425477778923255 10169513928638216668384883)
              ·
                refine ⟨15254270892957325002577325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10169513928638216668384883 15254270892957325002577325)
                ·
                  refine ⟨5720351584858996875966497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15254270892957325002577325 5720351584858996875966497)
                  ·
                    refine ⟨4290263688644247656974873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5720351584858996875966497 4290263688644247656974873)
                    ·
                      refine ⟨3217697766483185742731155, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4290263688644247656974873 3217697766483185742731155)
                      ·
                        rfl

theorem cell23_6266444_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 5, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 5, 1, 1, 3, 2, 2].length) (baseStart_6266444 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6266444 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6266444 prefixEnd_6266444 := by exact prefixLift 6266444
  have htrace : WordTrace (prefixWord ++ tailWord_6266444) baseStart_6266444 baseEnd_6266444 := by
    simpa [prefixWord, tailWord_6266444, baseEnd_6266444] using wordTrace_append hprefix tailTrace_6266444
  have hstable : (prefixWord ++ tailWord_6266444).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6266444).length < 2 ^ (prefixWord ++ tailWord_6266444).sum := by decide
  have hdescent : baseEnd_6266444 < baseStart_6266444 := by decide
  rcases family_descends (prefixWord ++ tailWord_6266444) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6266461 : List Nat := [1, 4, 4, 2, 1, 2, 1, 2, 1, 1, 4]
def baseStart_6266461 : Nat := 118140960795 + 6266461 * 2 ^ 59
def prefixEnd_6266461 : Nat := 4983230072969 + 3 ^ 40 * 6266461 * 2
def baseEnd_6266461 : Nat := 3217706495654312176218577

theorem tailTrace_6266461 : CollatzResearch.WordTrace tailWord_6266461 prefixEnd_6266461 3217706495654312176218577 := by
  unfold tailWord_6266461
  simp only [CollatzResearch.WordTrace]
  refine ⟨228556609350689498178839237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152371072900459665452559491 228556609350689498178839237)
  ·
    refine ⟨42854364253254280908532357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 228556609350689498178839237 42854364253254280908532357)
    ·
      refine ⟨8035193297485177670349817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 42854364253254280908532357 8035193297485177670349817)
      ·
        refine ⟨6026394973113883252762363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8035193297485177670349817 6026394973113883252762363)
        ·
          refine ⟨9039592459670824879143545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6026394973113883252762363 9039592459670824879143545)
          ·
            refine ⟨6779694344753118659357659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9039592459670824879143545 6779694344753118659357659)
            ·
              refine ⟨10169541517129677989036489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6779694344753118659357659 10169541517129677989036489)
              ·
                refine ⟨7627156137847258491777367, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10169541517129677989036489 7627156137847258491777367)
                ·
                  refine ⟨11440734206770887737666051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7627156137847258491777367 11440734206770887737666051)
                  ·
                    refine ⟨17161101310156331606499077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11440734206770887737666051 17161101310156331606499077)
                    ·
                      refine ⟨3217706495654312176218577, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17161101310156331606499077 3217706495654312176218577)
                      ·
                        rfl

theorem cell23_6266461_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 2, 1, 2, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 2, 1, 2, 1, 2, 1, 1, 4].length) (baseStart_6266461 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6266461 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6266461 prefixEnd_6266461 := by exact prefixLift 6266461
  have htrace : WordTrace (prefixWord ++ tailWord_6266461) baseStart_6266461 baseEnd_6266461 := by
    simpa [prefixWord, tailWord_6266461, baseEnd_6266461] using wordTrace_append hprefix tailTrace_6266461
  have hstable : (prefixWord ++ tailWord_6266461).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6266461).length < 2 ^ (prefixWord ++ tailWord_6266461).sum := by decide
  have hdescent : baseEnd_6266461 < baseStart_6266461 := by decide
  rcases family_descends (prefixWord ++ tailWord_6266461) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6266477 : List Nat := [1, 5, 1, 1, 4, 1, 1, 2, 1, 3, 3]
def baseStart_6266477 : Nat := 118140960795 + 6266477 * 2 ^ 59
def prefixEnd_6266477 : Nat := 4983230072969 + 3 ^ 40 * 6266477 * 2
def baseEnd_6266477 : Nat := 3217714711344784113618503

theorem tailTrace_6266477 : CollatzResearch.WordTrace tailWord_6266477 prefixEnd_6266477 3217714711344784113618503 := by
  unfold tailWord_6266477
  simp only [CollatzResearch.WordTrace]
  refine ⟨228557192918631532911421685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152371461945754355274281123 228557192918631532911421685)
  ·
    refine ⟨21427236836121706210445783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 228557192918631532911421685 21427236836121706210445783)
    ·
      refine ⟨32140855254182559315668675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21427236836121706210445783 32140855254182559315668675)
      ·
        refine ⟨48211282881273838973503013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32140855254182559315668675 48211282881273838973503013)
        ·
          refine ⟨9039615540238844807531815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 48211282881273838973503013 9039615540238844807531815)
          ·
            refine ⟨13559423310358267211297723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9039615540238844807531815 13559423310358267211297723)
            ·
              refine ⟨20339134965537400816946585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13559423310358267211297723 20339134965537400816946585)
              ·
                refine ⟨15254351224153050612709939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20339134965537400816946585 15254351224153050612709939)
                ·
                  refine ⟨22881526836229575919064909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15254351224153050612709939 22881526836229575919064909)
                  ·
                    refine ⟨8580572563586090969649341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 22881526836229575919064909 8580572563586090969649341)
                    ·
                      refine ⟨3217714711344784113618503, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8580572563586090969649341 3217714711344784113618503)
                      ·
                        rfl

theorem cell23_6266477_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 4, 1, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 4, 1, 1, 2, 1, 3, 3].length) (baseStart_6266477 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6266477 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6266477 prefixEnd_6266477 := by exact prefixLift 6266477
  have htrace : WordTrace (prefixWord ++ tailWord_6266477) baseStart_6266477 baseEnd_6266477 := by
    simpa [prefixWord, tailWord_6266477, baseEnd_6266477] using wordTrace_append hprefix tailTrace_6266477
  have hstable : (prefixWord ++ tailWord_6266477).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6266477).length < 2 ^ (prefixWord ++ tailWord_6266477).sum := by decide
  have hdescent : baseEnd_6266477 < baseStart_6266477 := by decide
  rcases family_descends (prefixWord ++ tailWord_6266477) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6266510 : List Nat := [4, 1, 1, 3, 1, 3, 1, 1, 2, 6]
def baseStart_6266510 : Nat := 118140960795 + 6266510 * 2 ^ 59
def prefixEnd_6266510 : Nat := 4983230072969 + 3 ^ 40 * 6266510 * 2
def baseEnd_6266510 : Nat := 1072577218735460828168617

theorem tailTrace_6266510 : CollatzResearch.WordTrace tailWord_6266510 prefixEnd_6266510 1072577218735460828168617 := by
  unfold tailWord_6266510
  simp only [CollatzResearch.WordTrace]
  refine ⟨28569799565938997443421623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 152372264351674653031581989 28569799565938997443421623)
  ·
    refine ⟨42854699348908496165132435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28569799565938997443421623 42854699348908496165132435)
    ·
      refine ⟨64282049023362744247698653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42854699348908496165132435 64282049023362744247698653)
      ·
        refine ⟨24105768383761029092886995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 64282049023362744247698653 24105768383761029092886995)
        ·
          refine ⟨36158652575641543639330493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24105768383761029092886995 36158652575641543639330493)
          ·
            refine ⟨13559494715865578864748935, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 36158652575641543639330493 13559494715865578864748935)
            ·
              refine ⟨20339242073798368297123403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13559494715865578864748935 20339242073798368297123403)
              ·
                refine ⟨30508863110697552445685105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20339242073798368297123403 30508863110697552445685105)
                ·
                  refine ⟨22881647333023164334263829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 30508863110697552445685105 22881647333023164334263829)
                  ·
                    refine ⟨1072577218735460828168617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 22881647333023164334263829 1072577218735460828168617)
                    ·
                      rfl

theorem cell23_6266510_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 3, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 3, 1, 1, 2, 6].length) (baseStart_6266510 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6266510 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6266510 prefixEnd_6266510 := by exact prefixLift 6266510
  have htrace : WordTrace (prefixWord ++ tailWord_6266510) baseStart_6266510 baseEnd_6266510 := by
    simpa [prefixWord, tailWord_6266510, baseEnd_6266510] using wordTrace_append hprefix tailTrace_6266510
  have hstable : (prefixWord ++ tailWord_6266510).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6266510).length < 2 ^ (prefixWord ++ tailWord_6266510).sum := by decide
  have hdescent : baseEnd_6266510 < baseStart_6266510 := by decide
  rcases family_descends (prefixWord ++ tailWord_6266510) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6266551 : List Nat := [1, 1, 3, 1, 5, 3, 1, 2, 2, 2, 2]
def baseStart_6266551 : Nat := 118140960795 + 6266551 * 2 ^ 59
def prefixEnd_6266551 : Nat := 4983230072969 + 3 ^ 40 * 6266551 * 2
def baseEnd_6266551 : Nat := 3217752708913216824093163

theorem tailTrace_6266551 : CollatzResearch.WordTrace tailWord_6266551 prefixEnd_6266551 3217752708913216824093163 := by
  unfold tailWord_6266551
  simp only [CollatzResearch.WordTrace]
  refine ⟨228559891920363443549615507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152373261280242295699743671 228559891920363443549615507)
  ·
    refine ⟨342839837880545165324423261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 228559891920363443549615507 342839837880545165324423261)
    ·
      refine ⟨128564939205204436996658723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 342839837880545165324423261 128564939205204436996658723)
      ·
        refine ⟨192847408807806655494988085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 128564939205204436996658723 192847408807806655494988085)
        ·
          refine ⟨18079444575731873952655133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 192847408807806655494988085 18079444575731873952655133)
          ·
            refine ⟨6779791715899452732245675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18079444575731873952655133 6779791715899452732245675)
            ·
              refine ⟨10169687573849179098368513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6779791715899452732245675 10169687573849179098368513)
              ·
                refine ⟨7627265680386884323776385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10169687573849179098368513 7627265680386884323776385)
                ·
                  refine ⟨5720449260290163242832289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7627265680386884323776385 5720449260290163242832289)
                  ·
                    refine ⟨4290336945217622432124217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5720449260290163242832289 4290336945217622432124217)
                    ·
                      refine ⟨3217752708913216824093163, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4290336945217622432124217 3217752708913216824093163)
                      ·
                        rfl

theorem cell23_6266551_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 3, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 3, 1, 2, 2, 2, 2].length) (baseStart_6266551 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6266551 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6266551 prefixEnd_6266551 := by exact prefixLift 6266551
  have htrace : WordTrace (prefixWord ++ tailWord_6266551) baseStart_6266551 baseEnd_6266551 := by
    simpa [prefixWord, tailWord_6266551, baseEnd_6266551] using wordTrace_append hprefix tailTrace_6266551
  have hstable : (prefixWord ++ tailWord_6266551).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6266551).length < 2 ^ (prefixWord ++ tailWord_6266551).sum := by decide
  have hdescent : baseEnd_6266551 < baseStart_6266551 := by decide
  rcases family_descends (prefixWord ++ tailWord_6266551) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6266583 : List Nat := [1, 1, 3, 2, 1, 3, 1, 1, 2, 8]
def baseStart_6266583 : Nat := 118140960795 + 6266583 * 2 ^ 59
def prefixEnd_6266583 : Nat := 4983230072969 + 3 ^ 40 * 6266583 * 2
def baseEnd_6266583 : Nat := 1072589713431386899631005

theorem tailTrace_6266583 : CollatzResearch.WordTrace tailWord_6266583 prefixEnd_6266583 1072589713431386899631005 := by
  unfold tailWord_6266583
  simp only [CollatzResearch.WordTrace]
  refine ⟨228561059056247513014780403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152374039370831675343186935 228561059056247513014780403)
  ·
    refine ⟨342841588584371269522170605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 228561059056247513014780403 342841588584371269522170605)
    ·
      refine ⟨128565595719139226070813977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 342841588584371269522170605 128565595719139226070813977)
      ·
        refine ⟨96424196789354419553110483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 128565595719139226070813977 96424196789354419553110483)
        ·
          refine ⟨144636295184031629329665725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 96424196789354419553110483 144636295184031629329665725)
          ·
            refine ⟨54238610694011860998624647, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 144636295184031629329665725 54238610694011860998624647)
            ·
              refine ⟨81357916041017791497936971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 54238610694011860998624647 81357916041017791497936971)
              ·
                refine ⟨122036874061526687246905457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 81357916041017791497936971 122036874061526687246905457)
                ·
                  refine ⟨91527655546145015435179093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 122036874061526687246905457 91527655546145015435179093)
                  ·
                    refine ⟨1072589713431386899631005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 91527655546145015435179093 1072589713431386899631005)
                    ·
                      rfl

theorem cell23_6266583_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 1, 1, 2, 8].length) (baseStart_6266583 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6266583 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6266583 prefixEnd_6266583 := by exact prefixLift 6266583
  have htrace : WordTrace (prefixWord ++ tailWord_6266583) baseStart_6266583 baseEnd_6266583 := by
    simpa [prefixWord, tailWord_6266583, baseEnd_6266583] using wordTrace_append hprefix tailTrace_6266583
  have hstable : (prefixWord ++ tailWord_6266583).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6266583).length < 2 ^ (prefixWord ++ tailWord_6266583).sum := by decide
  have hdescent : baseEnd_6266583 < baseStart_6266583 := by decide
  rcases family_descends (prefixWord ++ tailWord_6266583) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6266603 : List Nat := [1, 1, 1, 1, 2, 4, 2, 1, 1, 3, 6]
def baseStart_6266603 : Nat := 118140960795 + 6266603 * 2 ^ 59
def prefixEnd_6266603 : Nat := 4983230072969 + 3 ^ 40 * 6266603 * 2
def baseEnd_6266603 : Nat := 3217779409907250620642923

theorem tailTrace_6266603 : CollatzResearch.WordTrace tailWord_6266603 prefixEnd_6266603 3217779409907250620642923 := by
  unfold tailWord_6266603
  simp only [CollatzResearch.WordTrace]
  refine ⟨228561788516175056430508463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152374525677450037620338975 228561788516175056430508463)
  ·
    refine ⟨342842682774262584645762695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 228561788516175056430508463 342842682774262584645762695)
    ·
      refine ⟨514264024161393876968644043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 342842682774262584645762695 514264024161393876968644043)
      ·
        refine ⟨771396036242090815452966065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 514264024161393876968644043 771396036242090815452966065)
        ·
          refine ⟨578547027181568111589724549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 771396036242090815452966065 578547027181568111589724549)
          ·
            refine ⟨108477567596544020923073353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 578547027181568111589724549 108477567596544020923073353)
            ·
              refine ⟨81358175697408015692305015, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 108477567596544020923073353 81358175697408015692305015)
              ·
                refine ⟨122037263546112023538457523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 81358175697408015692305015 122037263546112023538457523)
                ·
                  refine ⟨183055895319168035307686285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 122037263546112023538457523 183055895319168035307686285)
                  ·
                    refine ⟨68645960744688013240382357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 183055895319168035307686285 68645960744688013240382357)
                    ·
                      refine ⟨3217779409907250620642923, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 68645960744688013240382357 3217779409907250620642923)
                      ·
                        rfl

theorem cell23_6266603_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 2, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 2, 1, 1, 3, 6].length) (baseStart_6266603 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6266603 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6266603 prefixEnd_6266603 := by exact prefixLift 6266603
  have htrace : WordTrace (prefixWord ++ tailWord_6266603) baseStart_6266603 baseEnd_6266603 := by
    simpa [prefixWord, tailWord_6266603, baseEnd_6266603] using wordTrace_append hprefix tailTrace_6266603
  have hstable : (prefixWord ++ tailWord_6266603).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6266603).length < 2 ^ (prefixWord ++ tailWord_6266603).sum := by decide
  have hdescent : baseEnd_6266603 < baseStart_6266603 := by decide
  rcases family_descends (prefixWord ++ tailWord_6266603) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6266697 : List Nat := [1, 2, 1, 1, 2, 4, 2, 4, 1, 1, 4]
def baseStart_6266697 : Nat := 118140960795 + 6266697 * 2 ^ 59
def prefixEnd_6266697 : Nat := 4983230072969 + 3 ^ 40 * 6266697 * 2
def baseEnd_6266697 : Nat := 3217827677088773252867491

theorem tailTrace_6266697 : CollatzResearch.WordTrace tailWord_6266697 prefixEnd_6266697 3217827677088773252867491 := by
  unfold tailWord_6266697
  simp only [CollatzResearch.WordTrace]
  refine ⟨228565216977834510484430345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152376811318556340322953563 228565216977834510484430345)
  ·
    refine ⟨171423912733375882863322759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 228565216977834510484430345 171423912733375882863322759)
    ·
      refine ⟨257135869100063824294984139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 171423912733375882863322759 257135869100063824294984139)
      ·
        refine ⟨385703803650095736442476209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 257135869100063824294984139 385703803650095736442476209)
        ·
          refine ⟨289277852737571802331857157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 385703803650095736442476209 289277852737571802331857157)
          ·
            refine ⟨54239597388294712937223217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 289277852737571802331857157 54239597388294712937223217)
            ·
              refine ⟨40679698041221034702917413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 54239597388294712937223217 40679698041221034702917413)
              ·
                refine ⟨7627443382728944006797015, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 40679698041221034702917413 7627443382728944006797015)
                ·
                  refine ⟨11441165074093416010195523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7627443382728944006797015 11441165074093416010195523)
                  ·
                    refine ⟨17161747611140124015293285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11441165074093416010195523 17161747611140124015293285)
                    ·
                      refine ⟨3217827677088773252867491, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17161747611140124015293285 3217827677088773252867491)
                      ·
                        rfl

theorem cell23_6266697_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 2, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 2, 4, 1, 1, 4].length) (baseStart_6266697 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6266697 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6266697 prefixEnd_6266697 := by exact prefixLift 6266697
  have htrace : WordTrace (prefixWord ++ tailWord_6266697) baseStart_6266697 baseEnd_6266697 := by
    simpa [prefixWord, tailWord_6266697, baseEnd_6266697] using wordTrace_append hprefix tailTrace_6266697
  have hstable : (prefixWord ++ tailWord_6266697).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6266697).length < 2 ^ (prefixWord ++ tailWord_6266697).sum := by decide
  have hdescent : baseEnd_6266697 < baseStart_6266697 := by decide
  rcases family_descends (prefixWord ++ tailWord_6266697) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6266701 : List Nat := [1, 6, 1, 2, 1, 2, 1, 1, 1, 5, 2]
def baseStart_6266701 : Nat := 118140960795 + 6266701 * 2 ^ 59
def prefixEnd_6266701 : Nat := 4983230072969 + 3 ^ 40 * 6266701 * 2
def baseEnd_6266701 : Nat := 3217829731011391237217473

theorem tailTrace_6266701 : CollatzResearch.WordTrace tailWord_6266701 prefixEnd_6266701 3217829731011391237217473 := by
  unfold tailWord_6266701
  simp only [CollatzResearch.WordTrace]
  refine ⟨228565362869820019167575957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152376908579880012778383971 228565362869820019167575957)
  ·
    refine ⟨10714001384522813398480123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 228565362869820019167575957 10714001384522813398480123)
    ·
      refine ⟨16071002076784220097720185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10714001384522813398480123 16071002076784220097720185)
      ·
        refine ⟨12053251557588165073290139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16071002076784220097720185 12053251557588165073290139)
        ·
          refine ⟨18079877336382247609935209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12053251557588165073290139 18079877336382247609935209)
          ·
            refine ⟨13559908002286685707451407, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18079877336382247609935209 13559908002286685707451407)
            ·
              refine ⟨20339862003430028561177111, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13559908002286685707451407 20339862003430028561177111)
              ·
                refine ⟨30509793005145042841765667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20339862003430028561177111 30509793005145042841765667)
                ·
                  refine ⟨45764689507717564262648501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30509793005145042841765667 45764689507717564262648501)
                  ·
                    refine ⟨4290439641348521649623297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 45764689507717564262648501 4290439641348521649623297)
                    ·
                      refine ⟨3217829731011391237217473, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4290439641348521649623297 3217829731011391237217473)
                      ·
                        rfl

theorem cell23_6266701_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 2, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 2, 1, 1, 1, 5, 2].length) (baseStart_6266701 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6266701 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6266701 prefixEnd_6266701 := by exact prefixLift 6266701
  have htrace : WordTrace (prefixWord ++ tailWord_6266701) baseStart_6266701 baseEnd_6266701 := by
    simpa [prefixWord, tailWord_6266701, baseEnd_6266701] using wordTrace_append hprefix tailTrace_6266701
  have hstable : (prefixWord ++ tailWord_6266701).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6266701).length < 2 ^ (prefixWord ++ tailWord_6266701).sum := by decide
  have hdescent : baseEnd_6266701 < baseStart_6266701 := by decide
  rcases family_descends (prefixWord ++ tailWord_6266701) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6266708 : List Nat := [2, 4, 1, 1, 3, 2, 2, 3, 1, 1, 3]
def baseStart_6266708 : Nat := 118140960795 + 6266708 * 2 ^ 59
def prefixEnd_6266708 : Nat := 4983230072969 + 3 ^ 40 * 6266708 * 2
def baseEnd_6266708 : Nat := 3217833325375972709829941

theorem tailTrace_6266708 : CollatzResearch.WordTrace tailWord_6266708 prefixEnd_6266708 3217833325375972709829941 := by
  unfold tailWord_6266708
  simp only [CollatzResearch.WordTrace]
  refine ⟨114282809090397329681540389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 152377078787196439575387185 114282809090397329681540389)
  ·
    refine ⟨21428026704449499315288823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 114282809090397329681540389 21428026704449499315288823)
    ·
      refine ⟨32142040056674248972933235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21428026704449499315288823 32142040056674248972933235)
      ·
        refine ⟨48213060085011373459399853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32142040056674248972933235 48213060085011373459399853)
        ·
          refine ⟨18079897531879265047274945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 48213060085011373459399853 18079897531879265047274945)
          ·
            refine ⟨13559923148909448785456209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18079897531879265047274945 13559923148909448785456209)
            ·
              refine ⟨10169942361682086589092157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13559923148909448785456209 10169942361682086589092157)
              ·
                refine ⟨3813728385630782470909559, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10169942361682086589092157 3813728385630782470909559)
                ·
                  refine ⟨5720592578446173706364339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3813728385630782470909559 5720592578446173706364339)
                  ·
                    refine ⟨8580888867669260559546509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5720592578446173706364339 8580888867669260559546509)
                    ·
                      refine ⟨3217833325375972709829941, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8580888867669260559546509 3217833325375972709829941)
                      ·
                        rfl

theorem cell23_6266708_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 2, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 2, 2, 3, 1, 1, 3].length) (baseStart_6266708 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6266708 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6266708 prefixEnd_6266708 := by exact prefixLift 6266708
  have htrace : WordTrace (prefixWord ++ tailWord_6266708) baseStart_6266708 baseEnd_6266708 := by
    simpa [prefixWord, tailWord_6266708, baseEnd_6266708] using wordTrace_append hprefix tailTrace_6266708
  have hstable : (prefixWord ++ tailWord_6266708).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6266708).length < 2 ^ (prefixWord ++ tailWord_6266708).sum := by decide
  have hdescent : baseEnd_6266708 < baseStart_6266708 := by decide
  rcases family_descends (prefixWord ++ tailWord_6266708) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6266711 : List Nat := [1, 1, 3, 2, 5, 2, 2, 1, 1, 5]
def baseStart_6266711 : Nat := 118140960795 + 6266711 * 2 ^ 59
def prefixEnd_6266711 : Nat := 4983230072969 + 3 ^ 40 * 6266711 * 2
def baseEnd_6266711 : Nat := 1072611621939312066030809

theorem tailTrace_6266711 : CollatzResearch.WordTrace tailWord_6266711 prefixEnd_6266711 1072611621939312066030809 := by
  unfold tailWord_6266711
  simp only [CollatzResearch.WordTrace]
  refine ⟨228565727599783790875439987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152377151733189193916959991 228565727599783790875439987)
  ·
    refine ⟨342848591399675686313159981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 228565727599783790875439987 342848591399675686313159981)
    ·
      refine ⟨128568221774878382367434993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 342848591399675686313159981 128568221774878382367434993)
      ·
        refine ⟨96426166331158786775576245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 128568221774878382367434993 96426166331158786775576245)
        ·
          refine ⟨9039953093546136260210273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 96426166331158786775576245 9039953093546136260210273)
          ·
            refine ⟨6779964820159602195157705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9039953093546136260210273 6779964820159602195157705)
            ·
              refine ⟨5084973615119701646368279, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6779964820159602195157705 5084973615119701646368279)
              ·
                refine ⟨7627460422679552469552419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5084973615119701646368279 7627460422679552469552419)
                ·
                  refine ⟨11441190634019328704328629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7627460422679552469552419 11441190634019328704328629)
                  ·
                    refine ⟨1072611621939312066030809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11441190634019328704328629 1072611621939312066030809)
                    ·
                      rfl

theorem cell23_6266711_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 5, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 5, 2, 2, 1, 1, 5].length) (baseStart_6266711 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6266711 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6266711 prefixEnd_6266711 := by exact prefixLift 6266711
  have htrace : WordTrace (prefixWord ++ tailWord_6266711) baseStart_6266711 baseEnd_6266711 := by
    simpa [prefixWord, tailWord_6266711, baseEnd_6266711] using wordTrace_append hprefix tailTrace_6266711
  have hstable : (prefixWord ++ tailWord_6266711).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6266711).length < 2 ^ (prefixWord ++ tailWord_6266711).sum := by decide
  have hdescent : baseEnd_6266711 < baseStart_6266711 := by decide
  rcases family_descends (prefixWord ++ tailWord_6266711) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6266714 : List Nat := [3, 1, 1, 2, 1, 3, 1, 2, 5, 2, 2]
def baseStart_6266714 : Nat := 118140960795 + 6266714 * 2 ^ 59
def prefixEnd_6266714 : Nat := 4983230072969 + 3 ^ 40 * 6266714 * 2
def baseEnd_6266714 : Nat := 3217836406259899686354913

theorem tailTrace_6266714 : CollatzResearch.WordTrace tailWord_6266714 prefixEnd_6266714 3217836406259899686354913 := by
  unfold tailWord_6266714
  simp only [CollatzResearch.WordTrace]
  refine ⟨57141459254693230596949799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 152377224679181948258532797 57141459254693230596949799)
  ·
    refine ⟨85712188882039845895424699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57141459254693230596949799 85712188882039845895424699)
    ·
      refine ⟨128568283323059768843137049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85712188882039845895424699 128568283323059768843137049)
      ·
        refine ⟨96426212492294826632352787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 128568283323059768843137049 96426212492294826632352787)
        ·
          refine ⟨144639318738442239948529181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 96426212492294826632352787 144639318738442239948529181)
          ·
            refine ⟨54239744526915839980698443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 144639318738442239948529181 54239744526915839980698443)
            ·
              refine ⟨81359616790373759971047665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 54239744526915839980698443 81359616790373759971047665)
              ·
                refine ⟨61019712592780319978285749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 81359616790373759971047665 61019712592780319978285749)
                ·
                  refine ⟨5720598055573154997964289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 61019712592780319978285749 5720598055573154997964289)
                  ·
                    refine ⟨4290448541679866248473217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5720598055573154997964289 4290448541679866248473217)
                    ·
                      refine ⟨3217836406259899686354913, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4290448541679866248473217 3217836406259899686354913)
                      ·
                        rfl

theorem cell23_6266714_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 1, 2, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 1, 2, 5, 2, 2].length) (baseStart_6266714 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6266714 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6266714 prefixEnd_6266714 := by exact prefixLift 6266714
  have htrace : WordTrace (prefixWord ++ tailWord_6266714) baseStart_6266714 baseEnd_6266714 := by
    simpa [prefixWord, tailWord_6266714, baseEnd_6266714] using wordTrace_append hprefix tailTrace_6266714
  have hstable : (prefixWord ++ tailWord_6266714).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6266714).length < 2 ^ (prefixWord ++ tailWord_6266714).sum := by decide
  have hdescent : baseEnd_6266714 < baseStart_6266714 := by decide
  rcases family_descends (prefixWord ++ tailWord_6266714) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6266720 : List Nat := [2, 1, 1, 3, 3, 3, 10]
def baseStart_6266720 : Nat := 118140960795 + 6266720 * 2 ^ 59
def prefixEnd_6266720 : Nat := 4983230072969 + 3 ^ 40 * 6266720 * 2
def baseEnd_6266720 : Nat := 39726413421528724233085

theorem tailTrace_6266720 : CollatzResearch.WordTrace tailWord_6266720 prefixEnd_6266720 39726413421528724233085 := by
  unfold tailWord_6266720
  simp only [CollatzResearch.WordTrace]
  refine ⟨114283027928375592706258807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 152377370571167456941678409 114283027928375592706258807)
  ·
    refine ⟨171424541892563389059388211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114283027928375592706258807 171424541892563389059388211)
    ·
      refine ⟨257136812838845083589082317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 171424541892563389059388211 257136812838845083589082317)
      ·
        refine ⟨96426304814566906345905869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 257136812838845083589082317 96426304814566906345905869)
        ·
          refine ⟨36159864305462589879714701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 96426304814566906345905869 36159864305462589879714701)
          ·
            refine ⟨13559949114548471204893013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 36159864305462589879714701 13559949114548471204893013)
            ·
              refine ⟨39726413421528724233085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 13559949114548471204893013 39726413421528724233085)
              ·
                rfl

theorem cell23_6266720_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 3, 10].length) (baseStart_6266720 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6266720 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6266720 prefixEnd_6266720 := by exact prefixLift 6266720
  have htrace : WordTrace (prefixWord ++ tailWord_6266720) baseStart_6266720 baseEnd_6266720 := by
    simpa [prefixWord, tailWord_6266720, baseEnd_6266720] using wordTrace_append hprefix tailTrace_6266720
  have hstable : (prefixWord ++ tailWord_6266720).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6266720).length < 2 ^ (prefixWord ++ tailWord_6266720).sum := by decide
  have hdescent : baseEnd_6266720 < baseStart_6266720 := by decide
  rcases family_descends (prefixWord ++ tailWord_6266720) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6266724 : List Nat := [2, 3, 1, 1, 5, 1, 1, 1, 4, 4]
def baseStart_6266724 : Nat := 118140960795 + 6266724 * 2 ^ 59
def prefixEnd_6266724 : Nat := 4983230072969 + 3 ^ 40 * 6266724 * 2
def baseEnd_6266724 : Nat := 1072613847022148215743289

theorem tailTrace_6266724 : CollatzResearch.WordTrace tailWord_6266724 prefixEnd_6266724 1072613847022148215743289 := by
  unfold tailWord_6266724
  simp only [CollatzResearch.WordTrace]
  refine ⟨114283100874368347047831613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 152377467832491129397108817 114283100874368347047831613)
  ·
    refine ⟨42856162827888130142936855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 114283100874368347047831613 42856162827888130142936855)
    ·
      refine ⟨64284244241832195214405283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42856162827888130142936855 64284244241832195214405283)
      ·
        refine ⟨96426366362748292821607925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64284244241832195214405283 96426366362748292821607925)
        ·
          refine ⟨9039971846507652452025743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 96426366362748292821607925 9039971846507652452025743)
          ·
            refine ⟨13559957769761478678038615, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9039971846507652452025743 13559957769761478678038615)
            ·
              refine ⟨20339936654642218017057923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13559957769761478678038615 20339936654642218017057923)
              ·
                refine ⟨30509904981963327025586885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20339936654642218017057923 30509904981963327025586885)
                ·
                  refine ⟨5720607184118123817297541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 30509904981963327025586885 5720607184118123817297541)
                  ·
                    refine ⟨1072613847022148215743289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5720607184118123817297541 1072613847022148215743289)
                    ·
                      rfl

theorem cell23_6266724_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 5, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 5, 1, 1, 1, 4, 4].length) (baseStart_6266724 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6266724 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6266724 prefixEnd_6266724 := by exact prefixLift 6266724
  have htrace : WordTrace (prefixWord ++ tailWord_6266724) baseStart_6266724 baseEnd_6266724 := by
    simpa [prefixWord, tailWord_6266724, baseEnd_6266724] using wordTrace_append hprefix tailTrace_6266724
  have hstable : (prefixWord ++ tailWord_6266724).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6266724).length < 2 ^ (prefixWord ++ tailWord_6266724).sum := by decide
  have hdescent : baseEnd_6266724 < baseStart_6266724 := by decide
  rcases family_descends (prefixWord ++ tailWord_6266724) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6266734 : List Nat := [4, 1, 2, 3, 1, 2, 1, 2, 1, 1, 5]
def baseStart_6266734 : Nat := 118140960795 + 6266734 * 2 ^ 59
def prefixEnd_6266734 : Nat := 4983230072969 + 3 ^ 40 * 6266734 * 2
def baseEnd_6266734 : Nat := 3217846675872989608104821

theorem tailTrace_6266734 : CollatzResearch.WordTrace tailWord_6266734 prefixEnd_6266734 3217846675872989608104821 := by
  unfold tailWord_6266734
  simp only [CollatzResearch.WordTrace]
  refine ⟨28570820809837558225440907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 152377710985800310535684837 28570820809837558225440907)
  ·
    refine ⟨42856231214756337338161361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28570820809837558225440907 42856231214756337338161361)
    ·
      refine ⟨32142173411067253003621021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42856231214756337338161361 32142173411067253003621021)
      ·
        refine ⟨12053315029150219876357883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 32142173411067253003621021 12053315029150219876357883)
        ·
          refine ⟨18079972543725329814536825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12053315029150219876357883 18079972543725329814536825)
          ·
            refine ⟨13559979407793997360902619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18079972543725329814536825 13559979407793997360902619)
            ·
              refine ⟨20339969111690996041353929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13559979407793997360902619 20339969111690996041353929)
              ·
                refine ⟨15254976833768247031015447, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20339969111690996041353929 15254976833768247031015447)
                ·
                  refine ⟨22882465250652370546523171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15254976833768247031015447 22882465250652370546523171)
                  ·
                    refine ⟨34323697875978555819784757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 22882465250652370546523171 34323697875978555819784757)
                    ·
                      refine ⟨3217846675872989608104821, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 34323697875978555819784757 3217846675872989608104821)
                      ·
                        rfl

theorem cell23_6266734_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 2, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 2, 1, 2, 1, 1, 5].length) (baseStart_6266734 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6266734 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6266734 prefixEnd_6266734 := by exact prefixLift 6266734
  have htrace : WordTrace (prefixWord ++ tailWord_6266734) baseStart_6266734 baseEnd_6266734 := by
    simpa [prefixWord, tailWord_6266734, baseEnd_6266734] using wordTrace_append hprefix tailTrace_6266734
  have hstable : (prefixWord ++ tailWord_6266734).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6266734).length < 2 ^ (prefixWord ++ tailWord_6266734).sum := by decide
  have hdescent : baseEnd_6266734 < baseStart_6266734 := by decide
  rcases family_descends (prefixWord ++ tailWord_6266734) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6266741 : List Nat := [1, 3, 4, 1, 1, 1, 5, 1, 2, 4]
def baseStart_6266741 : Nat := 118140960795 + 6266741 * 2 ^ 59
def prefixEnd_6266741 : Nat := 4983230072969 + 3 ^ 40 * 6266741 * 2
def baseEnd_6266741 : Nat := 1072616756745857026905763

theorem tailTrace_6266741 : CollatzResearch.WordTrace tailWord_6266741 prefixEnd_6266741 1072616756745857026905763 := by
  unfold tailWord_6266741
  simp only [CollatzResearch.WordTrace]
  refine ⟨228566821789675105999032077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152377881193116737332688051 228566821789675105999032077)
  ·
    refine ⟨85712558171128164749637029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 228566821789675105999032077 85712558171128164749637029)
    ·
      refine ⟨16071104657086530890556943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 85712558171128164749637029 16071104657086530890556943)
      ·
        refine ⟨24106656985629796335835415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16071104657086530890556943 24106656985629796335835415)
        ·
          refine ⟨36159985478444694503753123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24106656985629796335835415 36159985478444694503753123)
          ·
            refine ⟨54239978217667041755629685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36159985478444694503753123 54239978217667041755629685)
            ·
              refine ⟨5084997957906285164590283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 54239978217667041755629685 5084997957906285164590283)
              ·
                refine ⟨7627496936859427746885425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5084997957906285164590283 7627496936859427746885425)
                ·
                  refine ⟨5720622702644570810164069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7627496936859427746885425 5720622702644570810164069)
                  ·
                    refine ⟨1072616756745857026905763, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5720622702644570810164069 1072616756745857026905763)
                    ·
                      rfl

theorem cell23_6266741_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 5, 1, 2, 4].length) (baseStart_6266741 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6266741 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6266741 prefixEnd_6266741 := by exact prefixLift 6266741
  have htrace : WordTrace (prefixWord ++ tailWord_6266741) baseStart_6266741 baseEnd_6266741 := by
    simpa [prefixWord, tailWord_6266741, baseEnd_6266741] using wordTrace_append hprefix tailTrace_6266741
  have hstable : (prefixWord ++ tailWord_6266741).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6266741).length < 2 ^ (prefixWord ++ tailWord_6266741).sum := by decide
  have hdescent : baseEnd_6266741 < baseStart_6266741 := by decide
  rcases family_descends (prefixWord ++ tailWord_6266741) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6266782 : List Nat := [4, 3, 1, 3, 1, 2, 1, 1, 3, 2, 2]
def baseStart_6266782 : Nat := 118140960795 + 6266782 * 2 ^ 59
def prefixEnd_6266782 : Nat := 4983230072969 + 3 ^ 40 * 6266782 * 2
def baseEnd_6266782 : Nat := 3217871322944405420304601

theorem tailTrace_6266782 : CollatzResearch.WordTrace tailWord_6266782 prefixEnd_6266782 3217871322944405420304601 := by
  unfold tailWord_6266782
  simp only [CollatzResearch.WordTrace]
  refine ⟨28571039647815821250159325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 152378878121684380000849733 28571039647815821250159325)
  ·
    refine ⟨10714139867930932968809747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 28571039647815821250159325 10714139867930932968809747)
    ·
      refine ⟨16071209801896399453214621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10714139867930932968809747 16071209801896399453214621)
      ·
        refine ⟨6026703675711149794955483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16071209801896399453214621 6026703675711149794955483)
        ·
          refine ⟨9040055513566724692433225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6026703675711149794955483 9040055513566724692433225)
          ·
            refine ⟨6780041635175043519324919, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9040055513566724692433225 6780041635175043519324919)
            ·
              refine ⟨10170062452762565278987379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6780041635175043519324919 10170062452762565278987379)
              ·
                refine ⟨15255093679143847918481069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10170062452762565278987379 15255093679143847918481069)
                ·
                  refine ⟨5720660129678942969430401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15255093679143847918481069 5720660129678942969430401)
                  ·
                    refine ⟨4290495097259207227072801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5720660129678942969430401 4290495097259207227072801)
                    ·
                      refine ⟨3217871322944405420304601, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4290495097259207227072801 3217871322944405420304601)
                      ·
                        rfl

theorem cell23_6266782_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 3, 1, 2, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 3, 1, 2, 1, 1, 3, 2, 2].length) (baseStart_6266782 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6266782 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6266782 prefixEnd_6266782 := by exact prefixLift 6266782
  have htrace : WordTrace (prefixWord ++ tailWord_6266782) baseStart_6266782 baseEnd_6266782 := by
    simpa [prefixWord, tailWord_6266782, baseEnd_6266782] using wordTrace_append hprefix tailTrace_6266782
  have hstable : (prefixWord ++ tailWord_6266782).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6266782).length < 2 ^ (prefixWord ++ tailWord_6266782).sum := by decide
  have hdescent : baseEnd_6266782 < baseStart_6266782 := by decide
  rcases family_descends (prefixWord ++ tailWord_6266782) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6266792 : List Nat := [2, 1, 6, 2, 2, 1, 2, 1, 2, 4]
def baseStart_6266792 : Nat := 118140960795 + 6266792 * 2 ^ 59
def prefixEnd_6266792 : Nat := 4983230072969 + 3 ^ 40 * 6266792 * 2
def baseEnd_6266792 : Nat := 1072625485916983460393185

theorem tailTrace_6266792 : CollatzResearch.WordTrace tailWord_6266792 prefixEnd_6266792 1072625485916983460393185 := by
  unfold tailWord_6266792
  simp only [CollatzResearch.WordTrace]
  refine ⟨114284340956245170854569315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 152379121274993561139425753 114284340956245170854569315)
  ·
    refine ⟨171426511434367756281853973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114284340956245170854569315 171426511434367756281853973)
    ·
      refine ⟨8035617723485988575711905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 171426511434367756281853973 8035617723485988575711905)
      ·
        refine ⟨6026713292614491431783929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8035617723485988575711905 6026713292614491431783929)
        ·
          refine ⟨4520034969460868573837947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6026713292614491431783929 4520034969460868573837947)
          ·
            refine ⟨6780052454191302860756921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4520034969460868573837947 6780052454191302860756921)
            ·
              refine ⟨5085039340643477145567691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6780052454191302860756921 5085039340643477145567691)
              ·
                refine ⟨7627559010965215718351537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5085039340643477145567691 7627559010965215718351537)
                ·
                  refine ⟨5720669258223911788763653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7627559010965215718351537 5720669258223911788763653)
                  ·
                    refine ⟨1072625485916983460393185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5720669258223911788763653 1072625485916983460393185)
                    ·
                      rfl

theorem cell23_6266792_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 2, 2, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 2, 2, 1, 2, 1, 2, 4].length) (baseStart_6266792 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6266792 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6266792 prefixEnd_6266792 := by exact prefixLift 6266792
  have htrace : WordTrace (prefixWord ++ tailWord_6266792) baseStart_6266792 baseEnd_6266792 := by
    simpa [prefixWord, tailWord_6266792, baseEnd_6266792] using wordTrace_append hprefix tailTrace_6266792
  have hstable : (prefixWord ++ tailWord_6266792).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6266792).length < 2 ^ (prefixWord ++ tailWord_6266792).sum := by decide
  have hdescent : baseEnd_6266792 < baseStart_6266792 := by decide
  rcases family_descends (prefixWord ++ tailWord_6266792) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6266800 : List Nat := [2, 1, 1, 1, 2, 1, 1, 1, 4, 3, 6]
def baseStart_6266800 : Nat := 118140960795 + 6266800 * 2 ^ 59
def prefixEnd_6266800 : Nat := 4983230072969 + 3 ^ 40 * 6266800 * 2
def baseEnd_6266800 : Nat := 3217880565596186349879517

theorem tailTrace_6266800 : CollatzResearch.WordTrace tailWord_6266800 prefixEnd_6266800 3217880565596186349879517 := by
  unfold tailWord_6266800
  simp only [CollatzResearch.WordTrace]
  refine ⟨114284486848230679537714927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 152379315797640906050286569 114284486848230679537714927)
  ·
    refine ⟨171426730272346019306572391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114284486848230679537714927 171426730272346019306572391)
    ·
      refine ⟨257140095408519028959858587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 171426730272346019306572391 257140095408519028959858587)
      ·
        refine ⟨385710143112778543439787881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 257140095408519028959858587 385710143112778543439787881)
        ·
          refine ⟨289282607334583907579840911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 385710143112778543439787881 289282607334583907579840911)
          ·
            refine ⟨433923911001875861369761367, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 289282607334583907579840911 433923911001875861369761367)
            ·
              refine ⟨650885866502813792054642051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 433923911001875861369761367 650885866502813792054642051)
              ·
                refine ⟨976328799754220688081963077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 650885866502813792054642051 976328799754220688081963077)
                ·
                  refine ⟨183061649953916379015368077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 976328799754220688081963077 183061649953916379015368077)
                  ·
                    refine ⟨68648118732718642130763029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 183061649953916379015368077 68648118732718642130763029)
                    ·
                      refine ⟨3217880565596186349879517, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 68648118732718642130763029 3217880565596186349879517)
                      ·
                        rfl

theorem cell23_6266800_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 1, 4, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 1, 4, 3, 6].length) (baseStart_6266800 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6266800 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6266800 prefixEnd_6266800 := by exact prefixLift 6266800
  have htrace : WordTrace (prefixWord ++ tailWord_6266800) baseStart_6266800 baseEnd_6266800 := by
    simpa [prefixWord, tailWord_6266800, baseEnd_6266800] using wordTrace_append hprefix tailTrace_6266800
  have hstable : (prefixWord ++ tailWord_6266800).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6266800).length < 2 ^ (prefixWord ++ tailWord_6266800).sum := by decide
  have hdescent : baseEnd_6266800 < baseStart_6266800 := by decide
  rcases family_descends (prefixWord ++ tailWord_6266800) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6266861 : List Nat := [1, 5, 1, 4, 1, 1, 1, 2, 7]
def baseStart_6266861 : Nat := 118140960795 + 6266861 * 2 ^ 59
def prefixEnd_6266861 : Nat := 4983230072969 + 3 ^ 40 * 6266861 * 2
def baseEnd_6266861 : Nat := 357545765324012290135193

theorem tailTrace_6266861 : CollatzResearch.WordTrace tailWord_6266861 prefixEnd_6266861 357545765324012290135193 := by
  unfold tailWord_6266861
  simp only [CollatzResearch.WordTrace]
  refine ⟨228571198549240366493400437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152380799032826910995600291 228571198549240366493400437)
  ·
    refine ⟨21428549863991284358756291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 228571198549240366493400437 21428549863991284358756291)
    ·
      refine ⟨32142824795986926538134437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21428549863991284358756291 32142824795986926538134437)
      ·
        refine ⟨6026779649247548725900207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 32142824795986926538134437 6026779649247548725900207)
        ·
          refine ⟨9040169473871323088850311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6026779649247548725900207 9040169473871323088850311)
          ·
            refine ⟨13560254210806984633275467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9040169473871323088850311 13560254210806984633275467)
            ·
              refine ⟨20340381316210476949913201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13560254210806984633275467 20340381316210476949913201)
              ·
                refine ⟨15255285987157857712434901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20340381316210476949913201 15255285987157857712434901)
                ·
                  refine ⟨357545765324012290135193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 15255285987157857712434901 357545765324012290135193)
                  ·
                    rfl

theorem cell23_6266861_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 4, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 4, 1, 1, 1, 2, 7].length) (baseStart_6266861 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6266861 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6266861 prefixEnd_6266861 := by exact prefixLift 6266861
  have htrace : WordTrace (prefixWord ++ tailWord_6266861) baseStart_6266861 baseEnd_6266861 := by
    simpa [prefixWord, tailWord_6266861, baseEnd_6266861] using wordTrace_append hprefix tailTrace_6266861
  have hstable : (prefixWord ++ tailWord_6266861).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6266861).length < 2 ^ (prefixWord ++ tailWord_6266861).sum := by decide
  have hdescent : baseEnd_6266861 < baseStart_6266861 := by decide
  rcases family_descends (prefixWord ++ tailWord_6266861) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6266878 : List Nat := [4, 2, 2, 2, 1, 2, 2, 3, 5]
def baseStart_6266878 : Nat := 118140960795 + 6266878 * 2 ^ 59
def prefixEnd_6266878 : Nat := 4983230072969 + 3 ^ 40 * 6266878 * 2
def baseEnd_6266878 : Nat := 357546735231915227189351

theorem tailTrace_6266878 : CollatzResearch.WordTrace tailWord_6266878 prefixEnd_6266878 357546735231915227189351 := by
  unfold tailWord_6266878
  simp only [CollatzResearch.WordTrace]
  refine ⟨28571477323772347299596161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 152381212393452518931179525 28571477323772347299596161)
  ·
    refine ⟨21428607992829260474697121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28571477323772347299596161 21428607992829260474697121)
    ·
      refine ⟨16071455994621945356022841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21428607992829260474697121 16071455994621945356022841)
      ·
        refine ⟨12053591995966459017017131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16071455994621945356022841 12053591995966459017017131)
        ·
          refine ⟨18080387993949688525525697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12053591995966459017017131 18080387993949688525525697)
          ·
            refine ⟨13560290995462266394144273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18080387993949688525525697 13560290995462266394144273)
            ·
              refine ⟨10170218246596699795608205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13560290995462266394144273 10170218246596699795608205)
              ·
                refine ⟨3813831842473762423353077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10170218246596699795608205 3813831842473762423353077)
                ·
                  refine ⟨357546735231915227189351, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3813831842473762423353077 357546735231915227189351)
                  ·
                    rfl

theorem cell23_6266878_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 2, 2, 3, 5].length) (baseStart_6266878 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6266878 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6266878 prefixEnd_6266878 := by exact prefixLift 6266878
  have htrace : WordTrace (prefixWord ++ tailWord_6266878) baseStart_6266878 baseEnd_6266878 := by
    simpa [prefixWord, tailWord_6266878, baseEnd_6266878] using wordTrace_append hprefix tailTrace_6266878
  have hstable : (prefixWord ++ tailWord_6266878).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6266878).length < 2 ^ (prefixWord ++ tailWord_6266878).sum := by decide
  have hdescent : baseEnd_6266878 < baseStart_6266878 := by decide
  rcases family_descends (prefixWord ++ tailWord_6266878) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6266894 : List Nat := [4, 1, 1, 2, 2, 1, 2, 1, 4, 1, 4]
def baseStart_6266894 : Nat := 118140960795 + 6266894 * 2 ^ 59
def prefixEnd_6266894 : Nat := 4983230072969 + 3 ^ 40 * 6266894 * 2
def baseEnd_6266894 : Nat := 3217928832777708982104085

theorem tailTrace_6266894 : CollatzResearch.WordTrace tailWord_6266894 prefixEnd_6266894 3217928832777708982104085 := by
  unfold tailWord_6266894
  simp only [CollatzResearch.WordTrace]
  refine ⟨28571550269765101641168967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 152381601438747208752901157 28571550269765101641168967)
  ·
    refine ⟨42857325404647652461753451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28571550269765101641168967 42857325404647652461753451)
    ·
      refine ⟨64285988106971478692630177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42857325404647652461753451 64285988106971478692630177)
      ·
        refine ⟨48214491080228609019472633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 64285988106971478692630177 48214491080228609019472633)
        ·
          refine ⟨36160868310171456764604475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48214491080228609019472633 36160868310171456764604475)
          ·
            refine ⟨54241302465257185146906713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36160868310171456764604475 54241302465257185146906713)
            ·
              refine ⟨40680976848942888860180035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 54241302465257185146906713 40680976848942888860180035)
              ·
                refine ⟨61021465273414333290270053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40680976848942888860180035 61021465273414333290270053)
                ·
                  refine ⟨11441524738765187491925635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 61021465273414333290270053 11441524738765187491925635)
                  ·
                    refine ⟨17162287108147781237888453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11441524738765187491925635 17162287108147781237888453)
                    ·
                      refine ⟨3217928832777708982104085, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17162287108147781237888453 3217928832777708982104085)
                      ·
                        rfl

theorem cell23_6266894_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 2, 1, 4, 1, 4].length) (baseStart_6266894 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6266894 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6266894 prefixEnd_6266894 := by exact prefixLift 6266894
  have htrace : WordTrace (prefixWord ++ tailWord_6266894) baseStart_6266894 baseEnd_6266894 := by
    simpa [prefixWord, tailWord_6266894, baseEnd_6266894] using wordTrace_append hprefix tailTrace_6266894
  have hstable : (prefixWord ++ tailWord_6266894).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6266894).length < 2 ^ (prefixWord ++ tailWord_6266894).sum := by decide
  have hdescent : baseEnd_6266894 < baseStart_6266894 := by decide
  rcases family_descends (prefixWord ++ tailWord_6266894) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6266914 : List Nat := [3, 3, 1, 1, 1, 2, 1, 1, 3, 4, 3]
def baseStart_6266914 : Nat := 118140960795 + 6266914 * 2 ^ 59
def prefixEnd_6266914 : Nat := 4983230072969 + 3 ^ 40 * 6266914 * 2
def baseEnd_6266914 : Nat := 3217939102390798903853993

theorem tailTrace_6266914 : CollatzResearch.WordTrace tailWord_6266914 prefixEnd_6266914 3217939102390798903853993 := by
  unfold tailWord_6266914
  simp only [CollatzResearch.WordTrace]
  refine ⟨57143282904512089136269949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 152382087745365571030053197 57143282904512089136269949)
  ·
    refine ⟨21428731089192033426101231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 57143282904512089136269949 21428731089192033426101231)
    ·
      refine ⟨32143096633788050139151847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21428731089192033426101231 32143096633788050139151847)
      ·
        refine ⟨48214644950682075208727771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32143096633788050139151847 48214644950682075208727771)
        ·
          refine ⟨72321967426023112813091657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48214644950682075208727771 72321967426023112813091657)
          ·
            refine ⟨54241475569517334609818743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 72321967426023112813091657 54241475569517334609818743)
            ·
              refine ⟨81362213354276001914728115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 54241475569517334609818743 81362213354276001914728115)
              ·
                refine ⟨122043320031414002872092173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 81362213354276001914728115 122043320031414002872092173)
                ·
                  refine ⟨45766245011780251077034565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 122043320031414002872092173 45766245011780251077034565)
                  ·
                    refine ⟨8581170939708797076943981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 45766245011780251077034565 8581170939708797076943981)
                    ·
                      refine ⟨3217939102390798903853993, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8581170939708797076943981 3217939102390798903853993)
                      ·
                        rfl

theorem cell23_6266914_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 1, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 1, 1, 3, 4, 3].length) (baseStart_6266914 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6266914 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6266914 prefixEnd_6266914 := by exact prefixLift 6266914
  have htrace : WordTrace (prefixWord ++ tailWord_6266914) baseStart_6266914 baseEnd_6266914 := by
    simpa [prefixWord, tailWord_6266914, baseEnd_6266914] using wordTrace_append hprefix tailTrace_6266914
  have hstable : (prefixWord ++ tailWord_6266914).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6266914).length < 2 ^ (prefixWord ++ tailWord_6266914).sum := by decide
  have hdescent : baseEnd_6266914 < baseStart_6266914 := by decide
  rcases family_descends (prefixWord ++ tailWord_6266914) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6266934 : List Nat := [5, 1, 2, 1, 1, 1, 1, 1, 10]
def baseStart_6266934 : Nat := 118140960795 + 6266934 * 2 ^ 59
def prefixEnd_6266934 : Nat := 4983230072969 + 3 ^ 40 * 6266934 * 2
def baseEnd_6266934 : Nat := 357549930222654313955989

theorem tailTrace_6266934 : CollatzResearch.WordTrace tailWord_6266934 prefixEnd_6266934 357549930222654313955989 := by
  unfold tailWord_6266934
  simp only [CollatzResearch.WordTrace]
  refine ⟨14285866317373493747550491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 152382574051983933307205237 14285866317373493747550491)
  ·
    refine ⟨21428799476060240621325737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14285866317373493747550491 21428799476060240621325737)
    ·
      refine ⟨16071599607045180465994303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21428799476060240621325737 16071599607045180465994303)
      ·
        refine ⟨24107399410567770698991455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16071599607045180465994303 24107399410567770698991455)
        ·
          refine ⟨36161099115851656048487183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24107399410567770698991455 36161099115851656048487183)
          ·
            refine ⟨54241648673777484072730775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36161099115851656048487183 54241648673777484072730775)
            ·
              refine ⟨81362473010666226109096163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 54241648673777484072730775 81362473010666226109096163)
              ·
                refine ⟨122043709515999339163644245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 81362473010666226109096163 122043709515999339163644245)
                ·
                  refine ⟨357549930222654313955989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 122043709515999339163644245 357549930222654313955989)
                  ·
                    rfl

theorem cell23_6266934_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 1, 1, 10].length) (baseStart_6266934 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6266934 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6266934 prefixEnd_6266934 := by exact prefixLift 6266934
  have htrace : WordTrace (prefixWord ++ tailWord_6266934) baseStart_6266934 baseEnd_6266934 := by
    simpa [prefixWord, tailWord_6266934, baseEnd_6266934] using wordTrace_append hprefix tailTrace_6266934
  have hstable : (prefixWord ++ tailWord_6266934).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6266934).length < 2 ^ (prefixWord ++ tailWord_6266934).sum := by decide
  have hdescent : baseEnd_6266934 < baseStart_6266934 := by decide
  rcases family_descends (prefixWord ++ tailWord_6266934) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6266964 : List Nat := [2, 4, 1, 1, 1, 1, 1, 4, 3, 5]
def baseStart_6266964 : Nat := 118140960795 + 6266964 * 2 ^ 59
def prefixEnd_6266964 : Nat := 4983230072969 + 3 ^ 40 * 6266964 * 2
def baseEnd_6266964 : Nat := 1072654925474507902742921

theorem tailTrace_6266964 : CollatzResearch.WordTrace tailWord_6266964 prefixEnd_6266964 1072654925474507902742921 := by
  unfold tailWord_6266964
  simp only [CollatzResearch.WordTrace]
  refine ⟨114287477633933607542199973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 152383303511911476722933297 114287477633933607542199973)
  ·
    refine ⟨21428902056362551414162495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 114287477633933607542199973 21428902056362551414162495)
    ·
      refine ⟨32143353084543827121243743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21428902056362551414162495 32143353084543827121243743)
      ·
        refine ⟨48215029626815740681865615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32143353084543827121243743 48215029626815740681865615)
        ·
          refine ⟨72322544440223611022798423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48215029626815740681865615 72322544440223611022798423)
          ·
            refine ⟨108483816660335416534197635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 72322544440223611022798423 108483816660335416534197635)
            ·
              refine ⟨162725724990503124801296453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 108483816660335416534197635 162725724990503124801296453)
              ·
                refine ⟨30511073435719335900243085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 162725724990503124801296453 30511073435719335900243085)
                ·
                  refine ⟨11441652538394750962591157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 30511073435719335900243085 11441652538394750962591157)
                  ·
                    refine ⟨1072654925474507902742921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11441652538394750962591157 1072654925474507902742921)
                    ·
                      rfl

theorem cell23_6266964_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 1, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 1, 4, 3, 5].length) (baseStart_6266964 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6266964 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6266964 prefixEnd_6266964 := by exact prefixLift 6266964
  have htrace : WordTrace (prefixWord ++ tailWord_6266964) baseStart_6266964 baseEnd_6266964 := by
    simpa [prefixWord, tailWord_6266964, baseEnd_6266964] using wordTrace_append hprefix tailTrace_6266964
  have hstable : (prefixWord ++ tailWord_6266964).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6266964).length < 2 ^ (prefixWord ++ tailWord_6266964).sum := by decide
  have hdescent : baseEnd_6266964 < baseStart_6266964 := by decide
  rcases family_descends (prefixWord ++ tailWord_6266964) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6266981 : List Nat := [1, 3, 1, 3, 2, 2, 3, 2, 1, 5]
def baseStart_6266981 : Nat := 118140960795 + 6266981 * 2 ^ 59
def prefixEnd_6266981 : Nat := 4983230072969 + 3 ^ 40 * 6266981 * 2
def baseEnd_6266981 : Nat := 1072657835198216713905395

theorem tailTrace_6266981 : CollatzResearch.WordTrace tailWord_6266981 prefixEnd_6266981 1072657835198216713905395 := by
  unfold tailWord_6266981
  simp only [CollatzResearch.WordTrace]
  refine ⟨228575575308805626987768797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152383716872537084658512531 228575575308805626987768797)
  ·
    refine ⟨85715840740802110120413299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 228575575308805626987768797 85715840740802110120413299)
    ·
      refine ⟨128573761111203165180619949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85715840740802110120413299 128573761111203165180619949)
      ·
        refine ⟨48215160416701186942732481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 128573761111203165180619949 48215160416701186942732481)
        ·
          refine ⟨36161370312525890207049361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48215160416701186942732481 36161370312525890207049361)
          ·
            refine ⟨27121027734394417655287021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36161370312525890207049361 27121027734394417655287021)
            ·
              refine ⟨10170385400397906620732633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27121027734394417655287021 10170385400397906620732633)
              ·
                refine ⟨7627789050298429965549475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10170385400397906620732633 7627789050298429965549475)
                ·
                  refine ⟨11441683575447644948324213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7627789050298429965549475 11441683575447644948324213)
                  ·
                    refine ⟨1072657835198216713905395, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11441683575447644948324213 1072657835198216713905395)
                    ·
                      rfl

theorem cell23_6266981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 2, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 2, 3, 2, 1, 5].length) (baseStart_6266981 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6266981 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6266981 prefixEnd_6266981 := by exact prefixLift 6266981
  have htrace : WordTrace (prefixWord ++ tailWord_6266981) baseStart_6266981 baseEnd_6266981 := by
    simpa [prefixWord, tailWord_6266981, baseEnd_6266981] using wordTrace_append hprefix tailTrace_6266981
  have hstable : (prefixWord ++ tailWord_6266981).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6266981).length < 2 ^ (prefixWord ++ tailWord_6266981).sum := by decide
  have hdescent : baseEnd_6266981 < baseStart_6266981 := by decide
  rcases family_descends (prefixWord ++ tailWord_6266981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6266987 : List Nat := [1, 1, 1, 1, 2, 2, 1, 1, 1, 7, 5]
def baseStart_6266987 : Nat := 118140960795 + 6266987 * 2 ^ 59
def prefixEnd_6266987 : Nat := 4983230072969 + 3 ^ 40 * 6266987 * 2
def baseEnd_6266987 : Nat := 3217976586478577118241157

theorem tailTrace_6266987 : CollatzResearch.WordTrace tailWord_6266987 prefixEnd_6266987 3217976586478577118241157 := by
  unfold tailWord_6266987
  simp only [CollatzResearch.WordTrace]
  refine ⟨228575794146783890012487215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152383862764522593341658143 228575794146783890012487215)
  ·
    refine ⟨342863691220175835018730823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 228575794146783890012487215 342863691220175835018730823)
    ·
      refine ⟨514295536830263752528096235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 342863691220175835018730823 514295536830263752528096235)
      ·
        refine ⟨771443305245395628792144353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 514295536830263752528096235 771443305245395628792144353)
        ·
          refine ⟨578582478934046721594108265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 771443305245395628792144353 578582478934046721594108265)
          ·
            refine ⟨433936859200535041195581199, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 578582478934046721594108265 433936859200535041195581199)
            ·
              refine ⟨650905288800802561793371799, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 433936859200535041195581199 650905288800802561793371799)
              ·
                refine ⟨976357933201203842690057699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 650905288800802561793371799 976357933201203842690057699)
                ·
                  refine ⟨1464536899801805764035086549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 976357933201203842690057699 1464536899801805764035086549)
                  ·
                    refine ⟨34325083589104822594572341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 1464536899801805764035086549 34325083589104822594572341)
                    ·
                      refine ⟨3217976586478577118241157, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 34325083589104822594572341 3217976586478577118241157)
                      ·
                        rfl

theorem cell23_6266987_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 1, 1, 7, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 1, 1, 7, 5].length) (baseStart_6266987 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6266987 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6266987 prefixEnd_6266987 := by exact prefixLift 6266987
  have htrace : WordTrace (prefixWord ++ tailWord_6266987) baseStart_6266987 baseEnd_6266987 := by
    simpa [prefixWord, tailWord_6266987, baseEnd_6266987] using wordTrace_append hprefix tailTrace_6266987
  have hstable : (prefixWord ++ tailWord_6266987).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6266987).length < 2 ^ (prefixWord ++ tailWord_6266987).sum := by decide
  have hdescent : baseEnd_6266987 < baseStart_6266987 := by decide
  rcases family_descends (prefixWord ++ tailWord_6266987) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6266988 : List Nat := [2, 2, 1, 1, 3, 4, 2, 1, 2, 3, 2]
def baseStart_6266988 : Nat := 118140960795 + 6266988 * 2 ^ 59
def prefixEnd_6266988 : Nat := 4983230072969 + 3 ^ 40 * 6266988 * 2
def baseEnd_6266988 : Nat := 3217977099959231614328653

theorem tailTrace_6266988 : CollatzResearch.WordTrace tailWord_6266988 prefixEnd_6266988 3217977099959231614328653 := by
  unfold tailWord_6266988
  simp only [CollatzResearch.WordTrace]
  refine ⟨114287915309890133591636809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 152383887079853511455515745 114287915309890133591636809)
  ·
    refine ⟨85715936482417600193727607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 114287915309890133591636809 85715936482417600193727607)
    ·
      refine ⟨128573904723626400290591411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85715936482417600193727607 128573904723626400290591411)
      ·
        refine ⟨192860857085439600435887117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 128573904723626400290591411 192860857085439600435887117)
        ·
          refine ⟨72322821407039850163457669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 192860857085439600435887117 72322821407039850163457669)
          ·
            refine ⟨13560529013819971905648313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 72322821407039850163457669 13560529013819971905648313)
            ·
              refine ⟨10170396760364978929236235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13560529013819971905648313 10170396760364978929236235)
              ·
                refine ⟨15255595140547468393854353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10170396760364978929236235 15255595140547468393854353)
                ·
                  refine ⟨11441696355410601295390765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15255595140547468393854353 11441696355410601295390765)
                  ·
                    refine ⟨4290636133278975485771537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11441696355410601295390765 4290636133278975485771537)
                    ·
                      refine ⟨3217977099959231614328653, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4290636133278975485771537 3217977099959231614328653)
                      ·
                        rfl

theorem cell23_6266988_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 2, 3, 2].length) (baseStart_6266988 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6266988 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6266988 prefixEnd_6266988 := by exact prefixLift 6266988
  have htrace : WordTrace (prefixWord ++ tailWord_6266988) baseStart_6266988 baseEnd_6266988 := by
    simpa [prefixWord, tailWord_6266988, baseEnd_6266988] using wordTrace_append hprefix tailTrace_6266988
  have hstable : (prefixWord ++ tailWord_6266988).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6266988).length < 2 ^ (prefixWord ++ tailWord_6266988).sum := by decide
  have hdescent : baseEnd_6266988 < baseStart_6266988 := by decide
  rcases family_descends (prefixWord ++ tailWord_6266988) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6266994 : List Nat := [3, 2, 1, 2, 2, 2, 1, 1, 3, 6]
def baseStart_6266994 : Nat := 118140960795 + 6266994 * 2 ^ 59
def prefixEnd_6266994 : Nat := 4983230072969 + 3 ^ 40 * 6266994 * 2
def baseEnd_6266994 : Nat := 1072660060281052863617875

theorem tailTrace_6266994 : CollatzResearch.WordTrace tailWord_6266994 prefixEnd_6266994 1072660060281052863617875 := by
  unfold tailWord_6266994
  simp only [CollatzResearch.WordTrace]
  refine ⟨57144012364439632551998009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 152384032971839020138661357 57144012364439632551998009)
  ·
    refine ⟨42858009273329724413998507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57144012364439632551998009 42858009273329724413998507)
    ·
      refine ⟨64287013909994586620997761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42858009273329724413998507 64287013909994586620997761)
      ·
        refine ⟨48215260432495939965748321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 64287013909994586620997761 48215260432495939965748321)
        ·
          refine ⟨36161445324371954974311241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48215260432495939965748321 36161445324371954974311241)
          ·
            refine ⟨27121083993278966230733431, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36161445324371954974311241 27121083993278966230733431)
            ·
              refine ⟨40681625989918449346100147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27121083993278966230733431 40681625989918449346100147)
              ·
                refine ⟨61022438984877674019150221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40681625989918449346100147 61022438984877674019150221)
                ·
                  refine ⟨22883414619329127757181333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 61022438984877674019150221 22883414619329127757181333)
                  ·
                    refine ⟨1072660060281052863617875, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 22883414619329127757181333 1072660060281052863617875)
                    ·
                      rfl

theorem cell23_6266994_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 2, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 2, 1, 1, 3, 6].length) (baseStart_6266994 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6266994 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6266994 prefixEnd_6266994 := by exact prefixLift 6266994
  have htrace : WordTrace (prefixWord ++ tailWord_6266994) baseStart_6266994 baseEnd_6266994 := by
    simpa [prefixWord, tailWord_6266994, baseEnd_6266994] using wordTrace_append hprefix tailTrace_6266994
  have hstable : (prefixWord ++ tailWord_6266994).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6266994).length < 2 ^ (prefixWord ++ tailWord_6266994).sum := by decide
  have hdescent : baseEnd_6266994 < baseStart_6266994 := by decide
  rcases family_descends (prefixWord ++ tailWord_6266994) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6267011 : List Nat := [1, 1, 1, 3, 3, 3, 1, 4, 2, 4]
def baseStart_6267011 : Nat := 118140960795 + 6267011 * 2 ^ 59
def prefixEnd_6267011 : Nat := 4983230072969 + 3 ^ 40 * 6267011 * 2
def baseEnd_6267011 : Nat := 1072662970004761674780349

theorem tailTrace_6267011 : CollatzResearch.WordTrace tailWord_6267011 prefixEnd_6267011 1072662970004761674780349 := by
  unfold tailWord_6267011
  simp only [CollatzResearch.WordTrace]
  refine ⟨228576669498696942111360887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152384446332464628074240591 228576669498696942111360887)
  ·
    refine ⟨342865004248045413167041331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 228576669498696942111360887 342865004248045413167041331)
    ·
      refine ⟨514297506372068119750561997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 342865004248045413167041331 514297506372068119750561997)
      ·
        refine ⟨192861564889525544906460749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 514297506372068119750561997 192861564889525544906460749)
        ·
          refine ⟨72323086833572079339922781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 192861564889525544906460749 72323086833572079339922781)
          ·
            refine ⟨27121157562589529752471043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 72323086833572079339922781 27121157562589529752471043)
            ·
              refine ⟨40681736343884294628706565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27121157562589529752471043 40681736343884294628706565)
              ·
                refine ⟨7627825564478305242882481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 40681736343884294628706565 7627825564478305242882481)
                ·
                  refine ⟨5720869173358728932161861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7627825564478305242882481 5720869173358728932161861)
                  ·
                    refine ⟨1072662970004761674780349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5720869173358728932161861 1072662970004761674780349)
                    ·
                      rfl

theorem cell23_6267011_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 3, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 3, 1, 4, 2, 4].length) (baseStart_6267011 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6267011 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6267011 prefixEnd_6267011 := by exact prefixLift 6267011
  have htrace : WordTrace (prefixWord ++ tailWord_6267011) baseStart_6267011 baseEnd_6267011 := by
    simpa [prefixWord, tailWord_6267011, baseEnd_6267011] using wordTrace_append hprefix tailTrace_6267011
  have hstable : (prefixWord ++ tailWord_6267011).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6267011).length < 2 ^ (prefixWord ++ tailWord_6267011).sum := by decide
  have hdescent : baseEnd_6267011 < baseStart_6267011 := by decide
  rcases family_descends (prefixWord ++ tailWord_6267011) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6267041 : List Nat := [1, 2, 3, 3, 1, 3, 3, 7]
def baseStart_6267041 : Nat := 118140960795 + 6267041 * 2 ^ 59
def prefixEnd_6267041 : Nat := 4983230072969 + 3 ^ 40 * 6267041 * 2
def baseEnd_6267041 : Nat := 119185344979034070628367

theorem tailTrace_6267041 : CollatzResearch.WordTrace tailWord_6267041 prefixEnd_6267041 119185344979034070628367 := by
  unfold tailWord_6267041
  simp only [CollatzResearch.WordTrace]
  refine ⟨228577763688588257234952977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152385175792392171489968651 228577763688588257234952977)
  ·
    refine ⟨171433322766441192926214733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 228577763688588257234952977 171433322766441192926214733)
    ·
      refine ⟨64287496037415447347330525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 171433322766441192926214733 64287496037415447347330525)
      ·
        refine ⟨24107811014030792755248947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 64287496037415447347330525 24107811014030792755248947)
        ·
          refine ⟨36161716521046189132873421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24107811014030792755248947 36161716521046189132873421)
          ·
            refine ⟨13560643695392320924827533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 36161716521046189132873421 13560643695392320924827533)
            ·
              refine ⟨5085241385772120346810325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13560643695392320924827533 5085241385772120346810325)
              ·
                refine ⟨119185344979034070628367, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5085241385772120346810325 119185344979034070628367)
                ·
                  rfl

theorem cell23_6267041_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 3, 3, 7].length) (baseStart_6267041 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6267041 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6267041 prefixEnd_6267041 := by exact prefixLift 6267041
  have htrace : WordTrace (prefixWord ++ tailWord_6267041) baseStart_6267041 baseEnd_6267041 := by
    simpa [prefixWord, tailWord_6267041, baseEnd_6267041] using wordTrace_append hprefix tailTrace_6267041
  have hstable : (prefixWord ++ tailWord_6267041).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6267041).length < 2 ^ (prefixWord ++ tailWord_6267041).sum := by decide
  have hdescent : baseEnd_6267041 < baseStart_6267041 := by decide
  rcases family_descends (prefixWord ++ tailWord_6267041) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6267111 : List Nat := [1, 1, 5, 3, 1, 1, 1, 1, 1, 3, 5]
def baseStart_6267111 : Nat := 118140960795 + 6267111 * 2 ^ 59
def prefixEnd_6267111 : Nat := 4983230072969 + 3 ^ 40 * 6267111 * 2
def baseEnd_6267111 : Nat := 3218040258079734633090587

theorem tailTrace_6267111 : CollatzResearch.WordTrace tailWord_6267111 prefixEnd_6267111 3218040258079734633090587 := by
  unfold tailWord_6267111
  simp only [CollatzResearch.WordTrace]
  refine ⟨228580316798334659190001187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152386877865556439460000791 228580316798334659190001187)
  ·
    refine ⟨342870475197501988785001781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 228580316798334659190001187 342870475197501988785001781)
    ·
      refine ⟨32144107049765811448593917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 342870475197501988785001781 32144107049765811448593917)
      ·
        refine ⟨12054040143662179293222719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 32144107049765811448593917 12054040143662179293222719)
        ·
          refine ⟨18081060215493268939834079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12054040143662179293222719 18081060215493268939834079)
          ·
            refine ⟨27121590323239903409751119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18081060215493268939834079 27121590323239903409751119)
            ·
              refine ⟨40682385484859855114626679, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27121590323239903409751119 40682385484859855114626679)
              ·
                refine ⟨61023578227289782671940019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40682385484859855114626679 61023578227289782671940019)
                ·
                  refine ⟨91535367340934674007910029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 61023578227289782671940019 91535367340934674007910029)
                  ·
                    refine ⟨34325762752850502752966261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 91535367340934674007910029 34325762752850502752966261)
                    ·
                      refine ⟨3218040258079734633090587, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 34325762752850502752966261 3218040258079734633090587)
                      ·
                        rfl

theorem cell23_6267111_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 1, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 1, 1, 1, 1, 3, 5].length) (baseStart_6267111 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6267111 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6267111 prefixEnd_6267111 := by exact prefixLift 6267111
  have htrace : WordTrace (prefixWord ++ tailWord_6267111) baseStart_6267111 baseEnd_6267111 := by
    simpa [prefixWord, tailWord_6267111, baseEnd_6267111] using wordTrace_append hprefix tailTrace_6267111
  have hstable : (prefixWord ++ tailWord_6267111).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6267111).length < 2 ^ (prefixWord ++ tailWord_6267111).sum := by decide
  have hdescent : baseEnd_6267111 < baseStart_6267111 := by decide
  rcases family_descends (prefixWord ++ tailWord_6267111) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6267182 : List Nat := [4, 1, 3, 3, 1, 1, 1, 4, 5]
def baseStart_6267182 : Nat := 118140960795 + 6267182 * 2 ^ 59
def prefixEnd_6267182 : Nat := 4983230072969 + 3 ^ 40 * 6267182 * 2
def baseEnd_6267182 : Nat := 357564079467355983922529

theorem tailTrace_6267182 : CollatzResearch.WordTrace tailWord_6267182 prefixEnd_6267182 357564079467355983922529 := by
  unfold tailWord_6267182
  simp only [CollatzResearch.WordTrace]
  refine ⟨28572863297634679789479475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 152388604254051625543890533 28572863297634679789479475)
  ·
    refine ⟨42859294946452019684219213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28572863297634679789479475 42859294946452019684219213)
    ·
      refine ⟨16072235604919507381582205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 42859294946452019684219213 16072235604919507381582205)
      ·
        refine ⟨6027088351844815268093327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16072235604919507381582205 6027088351844815268093327)
        ·
          refine ⟨9040632527767222902139991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6027088351844815268093327 9040632527767222902139991)
          ·
            refine ⟨13560948791650834353209987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9040632527767222902139991 13560948791650834353209987)
            ·
              refine ⟨20341423187476251529814981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13560948791650834353209987 20341423187476251529814981)
              ·
                refine ⟨3814016847651797161840309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 20341423187476251529814981 3814016847651797161840309)
                ·
                  refine ⟨357564079467355983922529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3814016847651797161840309 357564079467355983922529)
                  ·
                    rfl

theorem cell23_6267182_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 3, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 3, 1, 1, 1, 4, 5].length) (baseStart_6267182 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6267182 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6267182 prefixEnd_6267182 := by exact prefixLift 6267182
  have htrace : WordTrace (prefixWord ++ tailWord_6267182) baseStart_6267182 baseEnd_6267182 := by
    simpa [prefixWord, tailWord_6267182, baseEnd_6267182] using wordTrace_append hprefix tailTrace_6267182
  have hstable : (prefixWord ++ tailWord_6267182).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6267182).length < 2 ^ (prefixWord ++ tailWord_6267182).sum := by decide
  have hdescent : baseEnd_6267182 < baseStart_6267182 := by decide
  rcases family_descends (prefixWord ++ tailWord_6267182) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6267188 : List Nat := [2, 5, 1, 1, 1, 2, 2, 1, 1, 2, 5]
def baseStart_6267188 : Nat := 118140960795 + 6267188 * 2 ^ 59
def prefixEnd_6267188 : Nat := 4983230072969 + 3 ^ 40 * 6267188 * 2
def baseEnd_6267188 : Nat := 3218079796090130831827733

theorem tailTrace_6267188 : CollatzResearch.WordTrace tailWord_6267188 prefixEnd_6267188 3218079796090130831827733 := by
  unfold tailWord_6267188
  simp only [CollatzResearch.WordTrace]
  refine ⟨114291562609527850670277109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 152388750146037134227036145 114291562609527850670277109)
  ·
    refine ⟨10714833994643236000338479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 114291562609527850670277109 10714833994643236000338479)
    ·
      refine ⟨16072250991964854000507719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10714833994643236000338479 16072250991964854000507719)
      ·
        refine ⟨24108376487947281000761579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16072250991964854000507719 24108376487947281000761579)
        ·
          refine ⟨36162564731920921501142369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24108376487947281000761579 36162564731920921501142369)
          ·
            refine ⟨27121923548940691125856777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36162564731920921501142369 27121923548940691125856777)
            ·
              refine ⟨20341442661705518344392583, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27121923548940691125856777 20341442661705518344392583)
              ·
                refine ⟨30512163992558277516588875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20341442661705518344392583 30512163992558277516588875)
                ·
                  refine ⟨45768245988837416274883313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30512163992558277516588875 45768245988837416274883313)
                  ·
                    refine ⟨34326184491628062206162485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 45768245988837416274883313 34326184491628062206162485)
                    ·
                      refine ⟨3218079796090130831827733, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 34326184491628062206162485 3218079796090130831827733)
                      ·
                        rfl

theorem cell23_6267188_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 2, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 2, 2, 1, 1, 2, 5].length) (baseStart_6267188 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6267188 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6267188 prefixEnd_6267188 := by exact prefixLift 6267188
  have htrace : WordTrace (prefixWord ++ tailWord_6267188) baseStart_6267188 baseEnd_6267188 := by
    simpa [prefixWord, tailWord_6267188, baseEnd_6267188] using wordTrace_append hprefix tailTrace_6267188
  have hstable : (prefixWord ++ tailWord_6267188).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6267188).length < 2 ^ (prefixWord ++ tailWord_6267188).sum := by decide
  have hdescent : baseEnd_6267188 < baseStart_6267188 := by decide
  rcases family_descends (prefixWord ++ tailWord_6267188) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6267191 : List Nat := [1, 1, 3, 1, 2, 1, 1, 2, 7, 4]
def baseStart_6267191 : Nat := 118140960795 + 6267191 * 2 ^ 59
def prefixEnd_6267191 : Nat := 4983230072969 + 3 ^ 40 * 6267191 * 2
def baseEnd_6267191 : Nat := 1072693778844031440030073

theorem tailTrace_6267191 : CollatzResearch.WordTrace tailWord_6267191 prefixEnd_6267191 1072693778844031440030073 := by
  unfold tailWord_6267191
  simp only [CollatzResearch.WordTrace]
  refine ⟨228583234638044832852913427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152388823092029888568608951 228583234638044832852913427)
  ·
    refine ⟨342874851957067249279370141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 228583234638044832852913427 342874851957067249279370141)
    ·
      refine ⟨128578069483900218479763803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 342874851957067249279370141 128578069483900218479763803)
      ·
        refine ⟨192867104225850327719645705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 128578069483900218479763803 192867104225850327719645705)
        ·
          refine ⟨144650328169387745789734279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 192867104225850327719645705 144650328169387745789734279)
          ·
            refine ⟨216975492254081618684601419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 144650328169387745789734279 216975492254081618684601419)
            ·
              refine ⟨325463238381122428026902129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 216975492254081618684601419 325463238381122428026902129)
              ·
                refine ⟨244097428785841821020176597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 325463238381122428026902129 244097428785841821020176597)
                ·
                  refine ⟨5721033487168167680160389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 244097428785841821020176597 5721033487168167680160389)
                  ·
                    refine ⟨1072693778844031440030073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5721033487168167680160389 1072693778844031440030073)
                    ·
                      rfl

theorem cell23_6267191_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 1, 2, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 1, 2, 7, 4].length) (baseStart_6267191 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6267191 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6267191 prefixEnd_6267191 := by exact prefixLift 6267191
  have htrace : WordTrace (prefixWord ++ tailWord_6267191) baseStart_6267191 baseEnd_6267191 := by
    simpa [prefixWord, tailWord_6267191, baseEnd_6267191] using wordTrace_append hprefix tailTrace_6267191
  have hstable : (prefixWord ++ tailWord_6267191).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6267191).length < 2 ^ (prefixWord ++ tailWord_6267191).sum := by decide
  have hdescent : baseEnd_6267191 < baseStart_6267191 := by decide
  rcases family_descends (prefixWord ++ tailWord_6267191) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6267242 : List Nat := [3, 1, 3, 3, 1, 1, 2, 4, 1, 4]
def baseStart_6267242 : Nat := 118140960795 + 6267242 * 2 ^ 59
def prefixEnd_6267242 : Nat := 4983230072969 + 3 ^ 40 * 6267242 * 2
def baseEnd_6267242 : Nat := 1072702508015157873517495

theorem tailTrace_6267242 : CollatzResearch.WordTrace tailWord_6267242 prefixEnd_6267242 1072702508015157873517495 := by
  unfold tailWord_6267242
  simp only [CollatzResearch.WordTrace]
  refine ⟨57146273690215017140754995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 152390063173906712375346653 57146273690215017140754995)
  ·
    refine ⟨85719410535322525711132493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57146273690215017140754995 85719410535322525711132493)
    ·
      refine ⟨32144778950745947141674685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 85719410535322525711132493 32144778950745947141674685)
      ·
        refine ⟨12054292106529730178128007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 32144778950745947141674685 12054292106529730178128007)
        ·
          refine ⟨18081438159794595267192011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12054292106529730178128007 18081438159794595267192011)
          ·
            refine ⟨27122157239691892900788017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18081438159794595267192011 27122157239691892900788017)
            ·
              refine ⟨20341617929768919675591013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27122157239691892900788017 20341617929768919675591013)
              ·
                refine ⟨3814053361831672439173315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 20341617929768919675591013 3814053361831672439173315)
                ·
                  refine ⟨5721080042747508658759973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3814053361831672439173315 5721080042747508658759973)
                  ·
                    refine ⟨1072702508015157873517495, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5721080042747508658759973 1072702508015157873517495)
                    ·
                      rfl

theorem cell23_6267242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 1, 2, 4, 1, 4].length) (baseStart_6267242 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6267242 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6267242 prefixEnd_6267242 := by exact prefixLift 6267242
  have htrace : WordTrace (prefixWord ++ tailWord_6267242) baseStart_6267242 baseEnd_6267242 := by
    simpa [prefixWord, tailWord_6267242, baseEnd_6267242] using wordTrace_append hprefix tailTrace_6267242
  have hstable : (prefixWord ++ tailWord_6267242).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6267242).length < 2 ^ (prefixWord ++ tailWord_6267242).sum := by decide
  have hdescent : baseEnd_6267242 < baseStart_6267242 := by decide
  rcases family_descends (prefixWord ++ tailWord_6267242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6267286 : List Nat := [5, 3, 1, 2, 1, 1, 1, 2, 2, 2, 3]
def baseStart_6267286 : Nat := 118140960795 + 6267286 * 2 ^ 59
def prefixEnd_6267286 : Nat := 4983230072969 + 3 ^ 40 * 6267286 * 2
def baseEnd_6267286 : Nat := 3218130117194271448402283

theorem tailTrace_6267286 : CollatzResearch.WordTrace tailWord_6267286 prefixEnd_6267286 3218130117194271448402283 := by
  unfold tailWord_6267286
  simp only [CollatzResearch.WordTrace]
  refine ⟨14286668723293791504851357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 152391133048467109385081141 14286668723293791504851357)
  ·
    refine ⟨5357500771235171814319259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14286668723293791504851357 5357500771235171814319259)
    ·
      refine ⟨8036251156852757721478889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5357500771235171814319259 8036251156852757721478889)
      ·
        refine ⟨6027188367639568291109167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8036251156852757721478889 6027188367639568291109167)
        ·
          refine ⟨9040782551459352436663751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6027188367639568291109167 9040782551459352436663751)
          ·
            refine ⟨13561173827189028654995627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9040782551459352436663751 13561173827189028654995627)
            ·
              refine ⟨20341760740783542982493441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13561173827189028654995627 20341760740783542982493441)
              ·
                refine ⟨15256320555587657236870081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20341760740783542982493441 15256320555587657236870081)
                ·
                  refine ⟨11442240416690742927652561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15256320555587657236870081 11442240416690742927652561)
                  ·
                    refine ⟨8581680312518057195739421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11442240416690742927652561 8581680312518057195739421)
                    ·
                      refine ⟨3218130117194271448402283, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8581680312518057195739421 3218130117194271448402283)
                      ·
                        rfl

theorem cell23_6267286_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 2, 1, 1, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 2, 1, 1, 1, 2, 2, 2, 3].length) (baseStart_6267286 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6267286 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6267286 prefixEnd_6267286 := by exact prefixLift 6267286
  have htrace : WordTrace (prefixWord ++ tailWord_6267286) baseStart_6267286 baseEnd_6267286 := by
    simpa [prefixWord, tailWord_6267286, baseEnd_6267286] using wordTrace_append hprefix tailTrace_6267286
  have hstable : (prefixWord ++ tailWord_6267286).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6267286).length < 2 ^ (prefixWord ++ tailWord_6267286).sum := by decide
  have hdescent : baseEnd_6267286 < baseStart_6267286 := by decide
  rcases family_descends (prefixWord ++ tailWord_6267286) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6267299 : List Nat := [1, 1, 1, 4, 1, 5, 3, 2, 1, 1, 3]
def baseStart_6267299 : Nat := 118140960795 + 6267299 * 2 ^ 59
def prefixEnd_6267299 : Nat := 4983230072969 + 3 ^ 40 * 6267299 * 2
def baseEnd_6267299 : Nat := 3218136792442779897539723

theorem tailTrace_6267299 : CollatzResearch.WordTrace tailWord_6267299 prefixEnd_6267299 3218136792442779897539723 := by
  unfold tailWord_6267299
  simp only [CollatzResearch.WordTrace]
  refine ⟨228587173721653567297844951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152391449147769044865229967 228587173721653567297844951)
  ·
    refine ⟨342880760582480350946767427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 228587173721653567297844951 342880760582480350946767427)
    ·
      refine ⟨514321140873720526420151141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 342880760582480350946767427 514321140873720526420151141)
      ·
        refine ⟨96435213913822598703778339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 514321140873720526420151141 96435213913822598703778339)
        ·
          refine ⟨144652820870733898055667509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 96435213913822598703778339 144652820870733898055667509)
          ·
            refine ⟨13561201956631302942718829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 144652820870733898055667509 13561201956631302942718829)
            ·
              refine ⟨5085450733736738603519561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13561201956631302942718829 5085450733736738603519561)
              ·
                refine ⟨3814088050302553952639671, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5085450733736738603519561 3814088050302553952639671)
                ·
                  refine ⟨5721132075453830928959507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3814088050302553952639671 5721132075453830928959507)
                  ·
                    refine ⟨8581698113180746393439261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5721132075453830928959507 8581698113180746393439261)
                    ·
                      refine ⟨3218136792442779897539723, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8581698113180746393439261 3218136792442779897539723)
                      ·
                        rfl

theorem cell23_6267299_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 5, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 5, 3, 2, 1, 1, 3].length) (baseStart_6267299 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6267299 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6267299 prefixEnd_6267299 := by exact prefixLift 6267299
  have htrace : WordTrace (prefixWord ++ tailWord_6267299) baseStart_6267299 baseEnd_6267299 := by
    simpa [prefixWord, tailWord_6267299, baseEnd_6267299] using wordTrace_append hprefix tailTrace_6267299
  have hstable : (prefixWord ++ tailWord_6267299).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6267299).length < 2 ^ (prefixWord ++ tailWord_6267299).sum := by decide
  have hdescent : baseEnd_6267299 < baseStart_6267299 := by decide
  rcases family_descends (prefixWord ++ tailWord_6267299) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6267301 : List Nat := [1, 3, 1, 2, 1, 1, 3, 1, 3, 1, 6]
def baseStart_6267301 : Nat := 118140960795 + 6267301 * 2 ^ 59
def prefixEnd_6267301 : Nat := 4983230072969 + 3 ^ 40 * 6267301 * 2
def baseEnd_6267301 : Nat := 3218137819404088889714713

theorem tailTrace_6267301 : CollatzResearch.WordTrace tailWord_6267301 prefixEnd_6267301 3218137819404088889714713 := by
  unfold tailWord_6267301
  simp only [CollatzResearch.WordTrace]
  refine ⟨228587246667646321639417757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152391497778430881092945171 228587246667646321639417757)
  ·
    refine ⟨85720217500367370614781659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 228587246667646321639417757 85720217500367370614781659)
    ·
      refine ⟨128580326250551055922172489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85720217500367370614781659 128580326250551055922172489)
      ·
        refine ⟨96435244687913291941629367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 128580326250551055922172489 96435244687913291941629367)
        ·
          refine ⟨144652867031869937912444051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 96435244687913291941629367 144652867031869937912444051)
          ·
            refine ⟨216979300547804906868666077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 144652867031869937912444051 216979300547804906868666077)
            ·
              refine ⟨81367237705426840075749779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 216979300547804906868666077 81367237705426840075749779)
              ·
                refine ⟨122050856558140260113624669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 81367237705426840075749779 122050856558140260113624669)
                ·
                  refine ⟨45769071209302597542609251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 122050856558140260113624669 45769071209302597542609251)
                  ·
                    refine ⟨68653606813953896313913877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 45769071209302597542609251 68653606813953896313913877)
                    ·
                      refine ⟨3218137819404088889714713, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 68653606813953896313913877 3218137819404088889714713)
                      ·
                        rfl

theorem cell23_6267301_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 3, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 3, 1, 3, 1, 6].length) (baseStart_6267301 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6267301 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6267301 prefixEnd_6267301 := by exact prefixLift 6267301
  have htrace : WordTrace (prefixWord ++ tailWord_6267301) baseStart_6267301 baseEnd_6267301 := by
    simpa [prefixWord, tailWord_6267301, baseEnd_6267301] using wordTrace_append hprefix tailTrace_6267301
  have hstable : (prefixWord ++ tailWord_6267301).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6267301).length < 2 ^ (prefixWord ++ tailWord_6267301).sum := by decide
  have hdescent : baseEnd_6267301 < baseStart_6267301 := by decide
  rcases family_descends (prefixWord ++ tailWord_6267301) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6267306 : List Nat := [3, 1, 6, 1, 1, 2, 2, 1, 6]
def baseStart_6267306 : Nat := 118140960795 + 6267306 * 2 ^ 59
def prefixEnd_6267306 : Nat := 4983230072969 + 3 ^ 40 * 6267306 * 2
def baseEnd_6267306 : Nat := 357571154089706818905799

theorem tailTrace_6267306 : CollatzResearch.WordTrace tailWord_6267306 prefixEnd_6267306 357571154089706818905799 := by
  unfold tailWord_6267306
  simp only [CollatzResearch.WordTrace]
  refine ⟨57146857258157051873337443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 152391619355085471662233181 57146857258157051873337443)
  ·
    refine ⟨85720285887235577810006165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57146857258157051873337443 85720285887235577810006165)
    ·
      refine ⟨4018138400964167709844039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 85720285887235577810006165 4018138400964167709844039)
      ·
        refine ⟨6027207601446251564766059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4018138400964167709844039 6027207601446251564766059)
        ·
          refine ⟨9040811402169377347149089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6027207601446251564766059 9040811402169377347149089)
          ·
            refine ⟨6780608551627033010361817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9040811402169377347149089 6780608551627033010361817)
            ·
              refine ⟨5085456413720274757771363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6780608551627033010361817 5085456413720274757771363)
              ·
                refine ⟨7628184620580412136657045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5085456413720274757771363 7628184620580412136657045)
                ·
                  refine ⟨357571154089706818905799, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7628184620580412136657045 357571154089706818905799)
                  ·
                    rfl

theorem cell23_6267306_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 6, 1, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 6, 1, 1, 2, 2, 1, 6].length) (baseStart_6267306 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6267306 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6267306 prefixEnd_6267306 := by exact prefixLift 6267306
  have htrace : WordTrace (prefixWord ++ tailWord_6267306) baseStart_6267306 baseEnd_6267306 := by
    simpa [prefixWord, tailWord_6267306, baseEnd_6267306] using wordTrace_append hprefix tailTrace_6267306
  have hstable : (prefixWord ++ tailWord_6267306).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6267306).length < 2 ^ (prefixWord ++ tailWord_6267306).sum := by decide
  have hdescent : baseEnd_6267306 < baseStart_6267306 := by decide
  rcases family_descends (prefixWord ++ tailWord_6267306) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6267308 : List Nat := [2, 2, 1, 1, 1, 1, 3, 4, 3, 2, 3]
def baseStart_6267308 : Nat := 118140960795 + 6267308 * 2 ^ 59
def prefixEnd_6267308 : Nat := 4983230072969 + 3 ^ 40 * 6267308 * 2
def baseEnd_6267308 : Nat := 3218141413768670362327181

theorem tailTrace_6267308 : CollatzResearch.WordTrace tailWord_6267308 prefixEnd_6267308 3218141413768670362327181 := by
  unfold tailWord_6267308
  simp only [CollatzResearch.WordTrace]
  refine ⟨114293750989310480917461289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 152391667985747307889948385 114293750989310480917461289)
  ·
    refine ⟨85720313241982860688095967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 114293750989310480917461289 85720313241982860688095967)
    ·
      refine ⟨128580469862974291032143951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85720313241982860688095967 128580469862974291032143951)
      ·
        refine ⟨192870704794461436548215927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 128580469862974291032143951 192870704794461436548215927)
        ·
          refine ⟨289306057191692154822323891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 192870704794461436548215927 289306057191692154822323891)
          ·
            refine ⟨433959085787538232233485837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 289306057191692154822323891 433959085787538232233485837)
            ·
              refine ⟨162734657170326837087557189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 433959085787538232233485837 162734657170326837087557189)
              ·
                refine ⟨30512748219436281953916973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 162734657170326837087557189 30512748219436281953916973)
                ·
                  refine ⟨11442280582288605732718865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 30512748219436281953916973 11442280582288605732718865)
                  ·
                    refine ⟨8581710436716454299539149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11442280582288605732718865 8581710436716454299539149)
                    ·
                      refine ⟨3218141413768670362327181, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8581710436716454299539149 3218141413768670362327181)
                      ·
                        rfl

theorem cell23_6267308_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 3, 2, 3].length) (baseStart_6267308 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6267308 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6267308 prefixEnd_6267308 := by exact prefixLift 6267308
  have htrace : WordTrace (prefixWord ++ tailWord_6267308) baseStart_6267308 baseEnd_6267308 := by
    simpa [prefixWord, tailWord_6267308, baseEnd_6267308] using wordTrace_append hprefix tailTrace_6267308
  have hstable : (prefixWord ++ tailWord_6267308).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6267308).length < 2 ^ (prefixWord ++ tailWord_6267308).sum := by decide
  have hdescent : baseEnd_6267308 < baseStart_6267308 := by decide
  rcases family_descends (prefixWord ++ tailWord_6267308) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6267325 : List Nat := [1, 4, 1, 2, 2, 3, 1, 1, 3, 2, 3]
def baseStart_6267325 : Nat := 118140960795 + 6267325 * 2 ^ 59
def prefixEnd_6267325 : Nat := 4983230072969 + 3 ^ 40 * 6267325 * 2
def baseEnd_6267325 : Nat := 3218150142939796795814603

theorem tailTrace_6267325 : CollatzResearch.WordTrace tailWord_6267325 prefixEnd_6267325 3218150142939796795814603 := by
  unfold tailWord_6267325
  simp only [CollatzResearch.WordTrace]
  refine ⟨228588122019559373738291429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152392081346372915825527619 228588122019559373738291429)
  ·
    refine ⟨42860272878667382575929643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 228588122019559373738291429 42860272878667382575929643)
    ·
      refine ⟨64290409318001073863894465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42860272878667382575929643 64290409318001073863894465)
      ·
        refine ⟨48217806988500805397920849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 64290409318001073863894465 48217806988500805397920849)
        ·
          refine ⟨36163355241375604048440637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48217806988500805397920849 36163355241375604048440637)
          ·
            refine ⟨13561258215515851518165239, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 36163355241375604048440637 13561258215515851518165239)
            ·
              refine ⟨20341887323273777277247859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13561258215515851518165239 20341887323273777277247859)
              ·
                refine ⟨30512830984910665915871789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20341887323273777277247859 30512830984910665915871789)
                ·
                  refine ⟨11442311619341499718451921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 30512830984910665915871789 11442311619341499718451921)
                  ·
                    refine ⟨8581733714506124788838941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11442311619341499718451921 8581733714506124788838941)
                    ·
                      refine ⟨3218150142939796795814603, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8581733714506124788838941 3218150142939796795814603)
                      ·
                        rfl

theorem cell23_6267325_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 3, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 3, 1, 1, 3, 2, 3].length) (baseStart_6267325 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6267325 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6267325 prefixEnd_6267325 := by exact prefixLift 6267325
  have htrace : WordTrace (prefixWord ++ tailWord_6267325) baseStart_6267325 baseEnd_6267325 := by
    simpa [prefixWord, tailWord_6267325, baseEnd_6267325] using wordTrace_append hprefix tailTrace_6267325
  have hstable : (prefixWord ++ tailWord_6267325).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6267325).length < 2 ^ (prefixWord ++ tailWord_6267325).sum := by decide
  have hdescent : baseEnd_6267325 < baseStart_6267325 := by decide
  rcases family_descends (prefixWord ++ tailWord_6267325) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6267351 : List Nat := [1, 1, 3, 2, 1, 1, 1, 1, 2, 3, 7]
def baseStart_6267351 : Nat := 118140960795 + 6267351 * 2 ^ 59
def prefixEnd_6267351 : Nat := 4983230072969 + 3 ^ 40 * 6267351 * 2
def baseEnd_6267351 : Nat := 3218163493436813694089483

theorem tailTrace_6267351 : CollatzResearch.WordTrace tailWord_6267351 prefixEnd_6267351 3218163493436813694089483 := by
  unfold tailWord_6267351
  simp only [CollatzResearch.WordTrace]
  refine ⟨228589070317465180178737907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152392713544976786785825271 228589070317465180178737907)
  ·
    refine ⟨342883605476197770268106861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 228589070317465180178737907 342883605476197770268106861)
    ·
      refine ⟨128581352053574163850540073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 342883605476197770268106861 128581352053574163850540073)
      ·
        refine ⟨96436014040180622887905055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 128581352053574163850540073 96436014040180622887905055)
        ·
          refine ⟨144654021060270934331857583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 96436014040180622887905055 144654021060270934331857583)
          ·
            refine ⟨216981031590406401497786375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 144654021060270934331857583 216981031590406401497786375)
            ·
              refine ⟨325471547385609602246679563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 216981031590406401497786375 325471547385609602246679563)
              ·
                refine ⟨488207321078414403370019345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 325471547385609602246679563 488207321078414403370019345)
                ·
                  refine ⟨366155490808810802527514509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 488207321078414403370019345 366155490808810802527514509)
                  ·
                    refine ⟨137308309053304050947817941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 366155490808810802527514509 137308309053304050947817941)
                    ·
                      refine ⟨3218163493436813694089483, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 137308309053304050947817941 3218163493436813694089483)
                      ·
                        rfl

theorem cell23_6267351_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 1, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 1, 1, 2, 3, 7].length) (baseStart_6267351 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6267351 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6267351 prefixEnd_6267351 := by exact prefixLift 6267351
  have htrace : WordTrace (prefixWord ++ tailWord_6267351) baseStart_6267351 baseEnd_6267351 := by
    simpa [prefixWord, tailWord_6267351, baseEnd_6267351] using wordTrace_append hprefix tailTrace_6267351
  have hstable : (prefixWord ++ tailWord_6267351).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6267351).length < 2 ^ (prefixWord ++ tailWord_6267351).sum := by decide
  have hdescent : baseEnd_6267351 < baseStart_6267351 := by decide
  rcases family_descends (prefixWord ++ tailWord_6267351) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6267382 : List Nat := [5, 1, 1, 1, 2, 1, 1, 3, 3, 3, 2]
def baseStart_6267382 : Nat := 118140960795 + 6267382 * 2 ^ 59
def prefixEnd_6267382 : Nat := 4983230072969 + 3 ^ 40 * 6267382 * 2
def baseEnd_6267382 : Nat := 3218179411337103072801841

theorem tailTrace_6267382 : CollatzResearch.WordTrace tailWord_6267382 prefixEnd_6267382 3218179411337103072801841 := by
  unfold tailWord_6267382
  simp only [CollatzResearch.WordTrace]
  refine ⟨14286887561272054529569775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 152393467320235248315410933 14286887561272054529569775)
  ·
    refine ⟨21430331341908081794354663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14286887561272054529569775 21430331341908081794354663)
    ·
      refine ⟨32145497012862122691531995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21430331341908081794354663 32145497012862122691531995)
      ·
        refine ⟨48218245519293184037297993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32145497012862122691531995 48218245519293184037297993)
        ·
          refine ⟨36163684139469888027973495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48218245519293184037297993 36163684139469888027973495)
          ·
            refine ⟨54245526209204832041960243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36163684139469888027973495 54245526209204832041960243)
            ·
              refine ⟨81368289313807248062940365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 54245526209204832041960243 81368289313807248062940365)
              ·
                refine ⟨30513108492677718023602637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 81368289313807248062940365 30513108492677718023602637)
                ·
                  refine ⟨11442415684754144258850989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 30513108492677718023602637 11442415684754144258850989)
                  ·
                    refine ⟨4290905881782804097069121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11442415684754144258850989 4290905881782804097069121)
                    ·
                      refine ⟨3218179411337103072801841, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4290905881782804097069121 3218179411337103072801841)
                      ·
                        rfl

theorem cell23_6267382_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 1, 3, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 1, 3, 3, 3, 2].length) (baseStart_6267382 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6267382 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6267382 prefixEnd_6267382 := by exact prefixLift 6267382
  have htrace : WordTrace (prefixWord ++ tailWord_6267382) baseStart_6267382 baseEnd_6267382 := by
    simpa [prefixWord, tailWord_6267382, baseEnd_6267382] using wordTrace_append hprefix tailTrace_6267382
  have hstable : (prefixWord ++ tailWord_6267382).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6267382).length < 2 ^ (prefixWord ++ tailWord_6267382).sum := by decide
  have hdescent : baseEnd_6267382 < baseStart_6267382 := by decide
  rcases family_descends (prefixWord ++ tailWord_6267382) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6267395 : List Nat := [1, 1, 1, 3, 2, 1, 3, 4, 1, 4, 2]
def baseStart_6267395 : Nat := 118140960795 + 6267395 * 2 ^ 59
def prefixEnd_6267395 : Nat := 4983230072969 + 3 ^ 40 * 6267395 * 2
def baseEnd_6267395 : Nat := 3218186086585611521939281

theorem tailTrace_6267395 : CollatzResearch.WordTrace tailWord_6267395 prefixEnd_6267395 3218186086585611521939281 := by
  unfold tailWord_6267395
  simp only [CollatzResearch.WordTrace]
  refine ⟨228590675129305775693339639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152393783419537183795559759 228590675129305775693339639)
  ·
    refine ⟨342886012693958663540009459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 228590675129305775693339639 342886012693958663540009459)
    ·
      refine ⟨514329019040937995310014189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 342886012693958663540009459 514329019040937995310014189)
      ·
        refine ⟨192873382140351748241255321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 514329019040937995310014189 192873382140351748241255321)
        ·
          refine ⟨144655036605263811180941491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 192873382140351748241255321 144655036605263811180941491)
          ·
            refine ⟨216982554907895716771412237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 144655036605263811180941491 216982554907895716771412237)
            ·
              refine ⟨81368458090460893789279589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 216982554907895716771412237 81368458090460893789279589)
              ·
                refine ⟨15256585891961417585489923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 81368458090460893789279589 15256585891961417585489923)
                ·
                  refine ⟨22884878837942126378234885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15256585891961417585489923 22884878837942126378234885)
                  ·
                    refine ⟨4290914782114148695919041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 22884878837942126378234885 4290914782114148695919041)
                    ·
                      refine ⟨3218186086585611521939281, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4290914782114148695919041 3218186086585611521939281)
                      ·
                        rfl

theorem cell23_6267395_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 3, 4, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 3, 4, 1, 4, 2].length) (baseStart_6267395 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6267395 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6267395 prefixEnd_6267395 := by exact prefixLift 6267395
  have htrace : WordTrace (prefixWord ++ tailWord_6267395) baseStart_6267395 baseEnd_6267395 := by
    simpa [prefixWord, tailWord_6267395, baseEnd_6267395] using wordTrace_append hprefix tailTrace_6267395
  have hstable : (prefixWord ++ tailWord_6267395).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6267395).length < 2 ^ (prefixWord ++ tailWord_6267395).sum := by decide
  have hdescent : baseEnd_6267395 < baseStart_6267395 := by decide
  rcases family_descends (prefixWord ++ tailWord_6267395) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6267399 : List Nat := [1, 1, 4, 3, 3, 1, 1, 3, 1, 3, 2]
def baseStart_6267399 : Nat := 118140960795 + 6267399 * 2 ^ 59
def prefixEnd_6267399 : Nat := 4983230072969 + 3 ^ 40 * 6267399 * 2
def baseEnd_6267399 : Nat := 3218188140508229506289263

theorem tailTrace_6267399 : CollatzResearch.WordTrace tailWord_6267399 prefixEnd_6267399 3218188140508229506289263 := by
  unfold tailWord_6267399
  simp only [CollatzResearch.WordTrace]
  refine ⟨228590821021291284376485251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152393880680860856250990167 228590821021291284376485251)
  ·
    refine ⟨342886231531936926564727877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 228590821021291284376485251 342886231531936926564727877)
    ·
      refine ⟨64291168412238173730886477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 342886231531936926564727877 64291168412238173730886477)
      ·
        refine ⟨24109188154589315149082429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 64291168412238173730886477 24109188154589315149082429)
        ·
          refine ⟨9040945557970993180905911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24109188154589315149082429 9040945557970993180905911)
          ·
            refine ⟨13561418336956489771358867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9040945557970993180905911 13561418336956489771358867)
            ·
              refine ⟨20342127505434734657038301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13561418336956489771358867 20342127505434734657038301)
              ·
                refine ⟨7628297814538025496389363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20342127505434734657038301 7628297814538025496389363)
                ·
                  refine ⟨11442446721807038244584045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7628297814538025496389363 11442446721807038244584045)
                  ·
                    refine ⟨4290917520677639341719017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11442446721807038244584045 4290917520677639341719017)
                    ·
                      refine ⟨3218188140508229506289263, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4290917520677639341719017 3218188140508229506289263)
                      ·
                        rfl

theorem cell23_6267399_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 3, 1, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 3, 1, 1, 3, 1, 3, 2].length) (baseStart_6267399 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6267399 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6267399 prefixEnd_6267399 := by exact prefixLift 6267399
  have htrace : WordTrace (prefixWord ++ tailWord_6267399) baseStart_6267399 baseEnd_6267399 := by
    simpa [prefixWord, tailWord_6267399, baseEnd_6267399] using wordTrace_append hprefix tailTrace_6267399
  have hstable : (prefixWord ++ tailWord_6267399).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6267399).length < 2 ^ (prefixWord ++ tailWord_6267399).sum := by decide
  have hdescent : baseEnd_6267399 < baseStart_6267399 := by decide
  rcases family_descends (prefixWord ++ tailWord_6267399) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6267418 : List Nat := [3, 1, 1, 3, 1, 1, 3, 3, 7]
def baseStart_6267418 : Nat := 118140960795 + 6267418 * 2 ^ 59
def prefixEnd_6267418 : Nat := 4983230072969 + 3 ^ 40 * 6267418 * 2
def baseEnd_6267418 : Nat := 357577544071184992439075

theorem tailTrace_6267418 : CollatzResearch.WordTrace tailWord_6267418 prefixEnd_6267418 357577544071184992439075 := by
  unfold tailWord_6267418
  simp only [CollatzResearch.WordTrace]
  refine ⟨57147878502055612655356727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 152394342672148300414284605 57147878502055612655356727)
  ·
    refine ⟨85721817753083418983035091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57147878502055612655356727 85721817753083418983035091)
    ·
      refine ⟨128582726629625128474552637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85721817753083418983035091 128582726629625128474552637)
      ·
        refine ⟨48218522486109423177957239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 128582726629625128474552637 48218522486109423177957239)
        ·
          refine ⟨72327783729164134766935859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48218522486109423177957239 72327783729164134766935859)
          ·
            refine ⟨108491675593746202150403789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 72327783729164134766935859 108491675593746202150403789)
            ·
              refine ⟨40684378347654825806401421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 108491675593746202150403789 40684378347654825806401421)
              ·
                refine ⟨15256641880370559677400533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 40684378347654825806401421 15256641880370559677400533)
                ·
                  refine ⟨357577544071184992439075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 15256641880370559677400533 357577544071184992439075)
                  ·
                    rfl

theorem cell23_6267418_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 3, 3, 7].length) (baseStart_6267418 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6267418 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6267418 prefixEnd_6267418 := by exact prefixLift 6267418
  have htrace : WordTrace (prefixWord ++ tailWord_6267418) baseStart_6267418 baseEnd_6267418 := by
    simpa [prefixWord, tailWord_6267418, baseEnd_6267418] using wordTrace_append hprefix tailTrace_6267418
  have hstable : (prefixWord ++ tailWord_6267418).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6267418).length < 2 ^ (prefixWord ++ tailWord_6267418).sum := by decide
  have hdescent : baseEnd_6267418 < baseStart_6267418 := by decide
  rcases family_descends (prefixWord ++ tailWord_6267418) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6267448 : List Nat := [2, 1, 2, 1, 4, 1, 1, 3, 1, 7]
def baseStart_6267448 : Nat := 118140960795 + 6267448 * 2 ^ 59
def prefixEnd_6267448 : Nat := 4983230072969 + 3 ^ 40 * 6267448 * 2
def baseEnd_6267448 : Nat := 1072737767020099938192179

theorem tailTrace_6267448 : CollatzResearch.WordTrace tailWord_6267448 prefixEnd_6267448 1072737767020099938192179 := by
  unfold tailWord_6267448
  simp only [CollatzResearch.WordTrace]
  refine ⟨114296304099056882872509499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 152395072132075843830012665 114296304099056882872509499)
  ·
    refine ⟨171444456148585324308764249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114296304099056882872509499 171444456148585324308764249)
    ·
      refine ⟨128583342111438993231573187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 171444456148585324308764249 128583342111438993231573187)
      ·
        refine ⟨192875013167158489847359781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 128583342111438993231573187 192875013167158489847359781)
        ·
          refine ⟨36164064968842216846379959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 192875013167158489847359781 36164064968842216846379959)
          ·
            refine ⟨54246097453263325269569939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36164064968842216846379959 54246097453263325269569939)
            ·
              refine ⟨81369146179894987904354909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 54246097453263325269569939 81369146179894987904354909)
              ·
                refine ⟨30513429817460620464133091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 81369146179894987904354909 30513429817460620464133091)
                ·
                  refine ⟨45770144726190930696199637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30513429817460620464133091 45770144726190930696199637)
                  ·
                    refine ⟨1072737767020099938192179, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 45770144726190930696199637 1072737767020099938192179)
                    ·
                      rfl

theorem cell23_6267448_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 1, 3, 1, 7].length) (baseStart_6267448 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6267448 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6267448 prefixEnd_6267448 := by exact prefixLift 6267448
  have htrace : WordTrace (prefixWord ++ tailWord_6267448) baseStart_6267448 baseEnd_6267448 := by
    simpa [prefixWord, tailWord_6267448, baseEnd_6267448] using wordTrace_append hprefix tailTrace_6267448
  have hstable : (prefixWord ++ tailWord_6267448).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6267448).length < 2 ^ (prefixWord ++ tailWord_6267448).sum := by decide
  have hdescent : baseEnd_6267448 < baseStart_6267448 := by decide
  rcases family_descends (prefixWord ++ tailWord_6267448) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6267452 : List Nat := [2, 2, 2, 2, 3, 1, 3, 3, 5]
def baseStart_6267452 : Nat := 118140960795 + 6267452 * 2 ^ 59
def prefixEnd_6267452 : Nat := 4983230072969 + 3 ^ 40 * 6267452 * 2
def baseEnd_6267452 : Nat := 357579483886990866547391

theorem tailTrace_6267452 : CollatzResearch.WordTrace tailWord_6267452 prefixEnd_6267452 357579483886990866547391 := by
  unfold tailWord_6267452
  simp only [CollatzResearch.WordTrace]
  refine ⟨114296377045049637214082305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 152395169393399516285443073 114296377045049637214082305)
  ·
    refine ⟨85722282783787227910561729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 114296377045049637214082305 85722282783787227910561729)
    ·
      refine ⟨64291712087840420932921297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 85722282783787227910561729 64291712087840420932921297)
      ·
        refine ⟨48218784065880315699690973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 64291712087840420932921297 48218784065880315699690973)
        ·
          refine ⟨18082044024705118387384115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 48218784065880315699690973 18082044024705118387384115)
          ·
            refine ⟨27123066037057677581076173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18082044024705118387384115 27123066037057677581076173)
            ·
              refine ⟨10171149763896629092903565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27123066037057677581076173 10171149763896629092903565)
              ·
                refine ⟨3814181161461235909838837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10171149763896629092903565 3814181161461235909838837)
                ·
                  refine ⟨357579483886990866547391, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3814181161461235909838837 357579483886990866547391)
                  ·
                    rfl

theorem cell23_6267452_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 1, 3, 3, 5].length) (baseStart_6267452 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6267452 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6267452 prefixEnd_6267452 := by exact prefixLift 6267452
  have htrace : WordTrace (prefixWord ++ tailWord_6267452) baseStart_6267452 baseEnd_6267452 := by
    simpa [prefixWord, tailWord_6267452, baseEnd_6267452] using wordTrace_append hprefix tailTrace_6267452
  have hstable : (prefixWord ++ tailWord_6267452).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6267452).length < 2 ^ (prefixWord ++ tailWord_6267452).sum := by decide
  have hdescent : baseEnd_6267452 < baseStart_6267452 := by decide
  rcases family_descends (prefixWord ++ tailWord_6267452) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6267495 : List Nat := [1, 1, 5, 1, 1, 1, 1, 3, 5, 4]
def baseStart_6267495 : Nat := 118140960795 + 6267495 * 2 ^ 59
def prefixEnd_6267495 : Nat := 4983230072969 + 3 ^ 40 * 6267495 * 2
def baseEnd_6267495 : Nat := 1072745811550353710229607

theorem tailTrace_6267495 : CollatzResearch.WordTrace tailWord_6267495 prefixEnd_6267495 1072745811550353710229607 := by
  unfold tailWord_6267495
  simp only [CollatzResearch.WordTrace]
  refine ⟨228594322428943492771979939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152396214952628995181319959 228594322428943492771979939)
  ·
    refine ⟨342891483643415239157969909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 228594322428943492771979939 342891483643415239157969909)
    ·
      refine ⟨32146076591570178671059679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 342891483643415239157969909 32146076591570178671059679)
      ·
        refine ⟨48219114887355268006589519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32146076591570178671059679 48219114887355268006589519)
        ·
          refine ⟨72328672331032902009884279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48219114887355268006589519 72328672331032902009884279)
          ·
            refine ⟨108493008496549353014826419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 72328672331032902009884279 108493008496549353014826419)
            ·
              refine ⟨162739512744824029522239629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 108493008496549353014826419 162739512744824029522239629)
              ·
                refine ⟨61027317279309011070839861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 162739512744824029522239629 61027317279309011070839861)
                ·
                  refine ⟨5721310994935219787891237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 61027317279309011070839861 5721310994935219787891237)
                  ·
                    refine ⟨1072745811550353710229607, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5721310994935219787891237 1072745811550353710229607)
                    ·
                      rfl

theorem cell23_6267495_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 1, 3, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 1, 3, 5, 4].length) (baseStart_6267495 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6267495 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6267495 prefixEnd_6267495 := by exact prefixLift 6267495
  have htrace : WordTrace (prefixWord ++ tailWord_6267495) baseStart_6267495 baseEnd_6267495 := by
    simpa [prefixWord, tailWord_6267495, baseEnd_6267495] using wordTrace_append hprefix tailTrace_6267495
  have hstable : (prefixWord ++ tailWord_6267495).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6267495).length < 2 ^ (prefixWord ++ tailWord_6267495).sum := by decide
  have hdescent : baseEnd_6267495 < baseStart_6267495 := by decide
  rcases family_descends (prefixWord ++ tailWord_6267495) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6267502 : List Nat := [4, 1, 2, 2, 2, 1, 1, 3, 2, 1, 4]
def baseStart_6267502 : Nat := 118140960795 + 6267502 * 2 ^ 59
def prefixEnd_6267502 : Nat := 4983230072969 + 3 ^ 40 * 6267502 * 2
def baseEnd_6267502 : Nat := 3218241029015642603301289

theorem tailTrace_6267502 : CollatzResearch.WordTrace tailWord_6267502 prefixEnd_6267502 3218241029015642603301289 := by
  unfold tailWord_6267502
  simp only [CollatzResearch.WordTrace]
  refine ⟨28574322217489766620935595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 152396385159945421978323173 28574322217489766620935595)
  ·
    refine ⟨42861483326234649931403393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28574322217489766620935595 42861483326234649931403393)
    ·
      refine ⟨32146112494675987448552545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42861483326234649931403393 32146112494675987448552545)
      ·
        refine ⟨24109584371006990586414409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32146112494675987448552545 24109584371006990586414409)
        ·
          refine ⟨18082188278255242939810807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24109584371006990586414409 18082188278255242939810807)
          ·
            refine ⟨27123282417382864409716211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18082188278255242939810807 27123282417382864409716211)
            ·
              refine ⟨40684923626074296614574317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27123282417382864409716211 40684923626074296614574317)
              ·
                refine ⟨15256846359777861230465369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 40684923626074296614574317 15256846359777861230465369)
                ·
                  refine ⟨11442634769833395922849027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15256846359777861230465369 11442634769833395922849027)
                  ·
                    refine ⟨17163952154750093884273541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11442634769833395922849027 17163952154750093884273541)
                    ·
                      refine ⟨3218241029015642603301289, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17163952154750093884273541 3218241029015642603301289)
                      ·
                        rfl

theorem cell23_6267502_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 1, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 1, 1, 3, 2, 1, 4].length) (baseStart_6267502 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6267502 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6267502 prefixEnd_6267502 := by exact prefixLift 6267502
  have htrace : WordTrace (prefixWord ++ tailWord_6267502) baseStart_6267502 baseEnd_6267502 := by
    simpa [prefixWord, tailWord_6267502, baseEnd_6267502] using wordTrace_append hprefix tailTrace_6267502
  have hstable : (prefixWord ++ tailWord_6267502).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6267502).length < 2 ^ (prefixWord ++ tailWord_6267502).sum := by decide
  have hdescent : baseEnd_6267502 < baseStart_6267502 := by decide
  rcases family_descends (prefixWord ++ tailWord_6267502) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6267525 : List Nat := [1, 3, 1, 1, 4, 2, 1, 4, 6]
def baseStart_6267525 : Nat := 118140960795 + 6267525 * 2 ^ 59
def prefixEnd_6267525 : Nat := 4983230072969 + 3 ^ 40 * 6267525 * 2
def baseEnd_6267525 : Nat := 357583648785632890368187

theorem tailTrace_6267525 : CollatzResearch.WordTrace tailWord_6267525 prefixEnd_6267525 357583648785632890368187 := by
  unfold tailWord_6267525
  simp only [CollatzResearch.WordTrace]
  refine ⟨228595416618834807895572029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152396944412556538597048019 228595416618834807895572029)
  ·
    refine ⟨85723281232063052960839511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 228595416618834807895572029 85723281232063052960839511)
    ·
      refine ⟨128584921848094579441259267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85723281232063052960839511 128584921848094579441259267)
      ·
        refine ⟨192877382772141869161888901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 128584921848094579441259267 192877382772141869161888901)
        ·
          refine ⟨36164509269776600467854169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 192877382772141869161888901 36164509269776600467854169)
          ·
            refine ⟨27123381952332450350890627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36164509269776600467854169 27123381952332450350890627)
            ·
              refine ⟨40685072928498675526335941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27123381952332450350890627 40685072928498675526335941)
              ·
                refine ⟨7628451174093501661187989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 40685072928498675526335941 7628451174093501661187989)
                ·
                  refine ⟨357583648785632890368187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7628451174093501661187989 357583648785632890368187)
                  ·
                    rfl

theorem cell23_6267525_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 2, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 2, 1, 4, 6].length) (baseStart_6267525 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6267525 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6267525 prefixEnd_6267525 := by exact prefixLift 6267525
  have htrace : WordTrace (prefixWord ++ tailWord_6267525) baseStart_6267525 baseEnd_6267525 := by
    simpa [prefixWord, tailWord_6267525, baseEnd_6267525] using wordTrace_append hprefix tailTrace_6267525
  have hstable : (prefixWord ++ tailWord_6267525).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6267525).length < 2 ^ (prefixWord ++ tailWord_6267525).sum := by decide
  have hdescent : baseEnd_6267525 < baseStart_6267525 := by decide
  rcases family_descends (prefixWord ++ tailWord_6267525) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6267609 : List Nat := [1, 2, 1, 2, 3, 2, 1, 4, 3, 2, 2]
def baseStart_6267609 : Nat := 118140960795 + 6267609 * 2 ^ 59
def prefixEnd_6267609 : Nat := 4983230072969 + 3 ^ 40 * 6267609 * 2
def baseEnd_6267609 : Nat := 3218295971445673684663297

theorem tailTrace_6267609 : CollatzResearch.WordTrace tailWord_6267609 prefixEnd_6267609 3218295971445673684663297 := by
  unfold tailWord_6267609
  simp only [CollatzResearch.WordTrace]
  refine ⟨228598480350530490241629881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152398986900353660161086587 228598480350530490241629881)
  ·
    refine ⟨171448860262897867681222411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 228598480350530490241629881 171448860262897867681222411)
    ·
      refine ⟨257173290394346801521833617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 171448860262897867681222411 257173290394346801521833617)
      ·
        refine ⟨192879967795760101141375213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 257173290394346801521833617 192879967795760101141375213)
        ·
          refine ⟨72329987923410037928015705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 192879967795760101141375213 72329987923410037928015705)
          ·
            refine ⟨54247490942557528446011779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 72329987923410037928015705 54247490942557528446011779)
            ·
              refine ⟨81371236413836292669017669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 54247490942557528446011779 81371236413836292669017669)
              ·
                refine ⟨15257106827594304875440813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 81371236413836292669017669 15257106827594304875440813)
                ·
                  refine ⟨5721415060347864328290305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15257106827594304875440813 5721415060347864328290305)
                  ·
                    refine ⟨4291061295260898246217729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5721415060347864328290305 4291061295260898246217729)
                    ·
                      refine ⟨3218295971445673684663297, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4291061295260898246217729 3218295971445673684663297)
                      ·
                        rfl

theorem cell23_6267609_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 1, 4, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 1, 4, 3, 2, 2].length) (baseStart_6267609 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6267609 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6267609 prefixEnd_6267609 := by exact prefixLift 6267609
  have htrace : WordTrace (prefixWord ++ tailWord_6267609) baseStart_6267609 baseEnd_6267609 := by
    simpa [prefixWord, tailWord_6267609, baseEnd_6267609] using wordTrace_append hprefix tailTrace_6267609
  have hstable : (prefixWord ++ tailWord_6267609).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6267609).length < 2 ^ (prefixWord ++ tailWord_6267609).sum := by decide
  have hdescent : baseEnd_6267609 < baseStart_6267609 := by decide
  rcases family_descends (prefixWord ++ tailWord_6267609) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6267615 : List Nat := [1, 1, 2, 3, 2, 4, 1, 9]
def baseStart_6267615 : Nat := 118140960795 + 6267615 * 2 ^ 59
def prefixEnd_6267615 : Nat := 4983230072969 + 3 ^ 40 * 6267615 * 2
def baseEnd_6267615 : Nat := 119196261197392617081047

theorem tailTrace_6267615 : CollatzResearch.WordTrace tailWord_6267615 prefixEnd_6267615 119196261197392617081047 := by
  unfold tailWord_6267615
  simp only [CollatzResearch.WordTrace]
  refine ⟨228598699188508753266348299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152399132792339168844232199 228598699188508753266348299)
  ·
    refine ⟨342898048782763129899522449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 228598699188508753266348299 342898048782763129899522449)
    ·
      refine ⟨257173536587072347424641837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 342898048782763129899522449 257173536587072347424641837)
      ·
        refine ⟨96440076220152130284240689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 257173536587072347424641837 96440076220152130284240689)
        ·
          refine ⟨72330057165114097713180517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 96440076220152130284240689 72330057165114097713180517)
          ·
            refine ⟨13561885718458893321221347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 72330057165114097713180517 13561885718458893321221347)
            ·
              refine ⟨20342828577688339981832021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13561885718458893321221347 20342828577688339981832021)
              ·
                refine ⟨119196261197392617081047, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 20342828577688339981832021 119196261197392617081047)
                ·
                  rfl

theorem cell23_6267615_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 4, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 4, 1, 9].length) (baseStart_6267615 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6267615 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6267615 prefixEnd_6267615 := by exact prefixLift 6267615
  have htrace : WordTrace (prefixWord ++ tailWord_6267615) baseStart_6267615 baseEnd_6267615 := by
    simpa [prefixWord, tailWord_6267615, baseEnd_6267615] using wordTrace_append hprefix tailTrace_6267615
  have hstable : (prefixWord ++ tailWord_6267615).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6267615).length < 2 ^ (prefixWord ++ tailWord_6267615).sum := by decide
  have hdescent : baseEnd_6267615 < baseStart_6267615 := by decide
  rcases family_descends (prefixWord ++ tailWord_6267615) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6267629 : List Nat := [1, 5, 1, 2, 1, 1, 1, 5, 1, 2, 3]
def baseStart_6267629 : Nat := 118140960795 + 6267629 * 2 ^ 59
def prefixEnd_6267629 : Nat := 4983230072969 + 3 ^ 40 * 6267629 * 2
def baseEnd_6267629 : Nat := 3218306241058763606413205

theorem tailTrace_6267629 : CollatzResearch.WordTrace tailWord_6267629 prefixEnd_6267629 3218306241058763606413205 := by
  unfold tailWord_6267629
  simp only [CollatzResearch.WordTrace]
  refine ⟨228599209810458033657357941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152399473206972022438238627 228599209810458033657357941)
  ·
    refine ⟨21431175919730440655377307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 228599209810458033657357941 21431175919730440655377307)
    ·
      refine ⟨32146763879595660983065961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21431175919730440655377307 32146763879595660983065961)
      ·
        refine ⟨24110072909696745737299471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32146763879595660983065961 24110072909696745737299471)
        ·
          refine ⟨36165109364545118605949207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24110072909696745737299471 36165109364545118605949207)
          ·
            refine ⟨54247664046817677908923811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36165109364545118605949207 54247664046817677908923811)
            ·
              refine ⟨81371496070226516863385717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 54247664046817677908923811 81371496070226516863385717)
              ·
                refine ⟨7628577756583735955942411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 81371496070226516863385717 7628577756583735955942411)
                ·
                  refine ⟨11442866634875603933913617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7628577756583735955942411 11442866634875603933913617)
                  ·
                    refine ⟨8582149976156702950435213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11442866634875603933913617 8582149976156702950435213)
                    ·
                      refine ⟨3218306241058763606413205, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8582149976156702950435213 3218306241058763606413205)
                      ·
                        rfl

theorem cell23_6267629_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 1, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 1, 5, 1, 2, 3].length) (baseStart_6267629 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6267629 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6267629 prefixEnd_6267629 := by exact prefixLift 6267629
  have htrace : WordTrace (prefixWord ++ tailWord_6267629) baseStart_6267629 baseEnd_6267629 := by
    simpa [prefixWord, tailWord_6267629, baseEnd_6267629] using wordTrace_append hprefix tailTrace_6267629
  have hstable : (prefixWord ++ tailWord_6267629).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6267629).length < 2 ^ (prefixWord ++ tailWord_6267629).sum := by decide
  have hdescent : baseEnd_6267629 < baseStart_6267629 := by decide
  rcases family_descends (prefixWord ++ tailWord_6267629) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6267637 : List Nat := [1, 3, 6, 1, 2, 1, 1, 1, 3, 1, 3]
def baseStart_6267637 : Nat := 118140960795 + 6267637 * 2 ^ 59
def prefixEnd_6267637 : Nat := 4983230072969 + 3 ^ 40 * 6267637 * 2
def baseEnd_6267637 : Nat := 3218310348903999575113169

theorem tailTrace_6267637 : CollatzResearch.WordTrace tailWord_6267637 prefixEnd_6267637 3218310348903999575113169 := by
  unfold tailWord_6267637
  simp only [CollatzResearch.WordTrace]
  refine ⟨228599501594429051023649165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152399667729619367349099443 228599501594429051023649165)
  ·
    refine ⟨85724813097910894133868437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 228599501594429051023649165 85724813097910894133868437)
    ·
      refine ⟨4018350613964573162525083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 85724813097910894133868437 4018350613964573162525083)
      ·
        refine ⟨6027525920946859743787625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4018350613964573162525083 6027525920946859743787625)
        ·
          refine ⟨4520644440710144807840719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6027525920946859743787625 4520644440710144807840719)
          ·
            refine ⟨6780966661065217211761079, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4520644440710144807840719 6780966661065217211761079)
            ·
              refine ⟨10171449991597825817641619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6780966661065217211761079 10171449991597825817641619)
              ·
                refine ⟨15257174987396738726462429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10171449991597825817641619 15257174987396738726462429)
                ·
                  refine ⟨5721440620273777022423411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15257174987396738726462429 5721440620273777022423411)
                  ·
                    refine ⟨8582160930410665533635117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5721440620273777022423411 8582160930410665533635117)
                    ·
                      refine ⟨3218310348903999575113169, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8582160930410665533635117 3218310348903999575113169)
                      ·
                        rfl

theorem cell23_6267637_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 6, 1, 2, 1, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 6, 1, 2, 1, 1, 1, 3, 1, 3].length) (baseStart_6267637 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6267637 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6267637 prefixEnd_6267637 := by exact prefixLift 6267637
  have htrace : WordTrace (prefixWord ++ tailWord_6267637) baseStart_6267637 baseEnd_6267637 := by
    simpa [prefixWord, tailWord_6267637, baseEnd_6267637] using wordTrace_append hprefix tailTrace_6267637
  have hstable : (prefixWord ++ tailWord_6267637).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6267637).length < 2 ^ (prefixWord ++ tailWord_6267637).sum := by decide
  have hdescent : baseEnd_6267637 < baseStart_6267637 := by decide
  rcases family_descends (prefixWord ++ tailWord_6267637) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6267645 : List Nat := [1, 4, 1, 1, 1, 1, 4, 1, 2, 7]
def baseStart_6267645 : Nat := 118140960795 + 6267645 * 2 ^ 59
def prefixEnd_6267645 : Nat := 4983230072969 + 3 ^ 40 * 6267645 * 2
def baseEnd_6267645 : Nat := 1072771485583078514604377

theorem tailTrace_6267645 : CollatzResearch.WordTrace tailWord_6267645 prefixEnd_6267645 1072771485583078514604377 := by
  unfold tailWord_6267645
  simp only [CollatzResearch.WordTrace]
  refine ⟨228599793378400068389940389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152399862252266712259960259 228599793378400068389940389)
  ·
    refine ⟨42862461258450012823113823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 228599793378400068389940389 42862461258450012823113823)
    ·
      refine ⟨64293691887675019234670735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42862461258450012823113823 64293691887675019234670735)
      ·
        refine ⟨96440537831512528852006103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64293691887675019234670735 96440537831512528852006103)
        ·
          refine ⟨144660806747268793278009155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 96440537831512528852006103 144660806747268793278009155)
          ·
            refine ⟨216991210120903189917013733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 144660806747268793278009155 216991210120903189917013733)
            ·
              refine ⟨40685851897669348109440075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 216991210120903189917013733 40685851897669348109440075)
              ·
                refine ⟨61028777846504022164160113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40685851897669348109440075 61028777846504022164160113)
                ·
                  refine ⟨45771583384878016623120085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 61028777846504022164160113 45771583384878016623120085)
                  ·
                    refine ⟨1072771485583078514604377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 45771583384878016623120085 1072771485583078514604377)
                    ·
                      rfl

theorem cell23_6267645_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 4, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 4, 1, 2, 7].length) (baseStart_6267645 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6267645 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6267645 prefixEnd_6267645 := by exact prefixLift 6267645
  have htrace : WordTrace (prefixWord ++ tailWord_6267645) baseStart_6267645 baseEnd_6267645 := by
    simpa [prefixWord, tailWord_6267645, baseEnd_6267645] using wordTrace_append hprefix tailTrace_6267645
  have hstable : (prefixWord ++ tailWord_6267645).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6267645).length < 2 ^ (prefixWord ++ tailWord_6267645).sum := by decide
  have hdescent : baseEnd_6267645 < baseStart_6267645 := by decide
  rcases family_descends (prefixWord ++ tailWord_6267645) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6267669 : List Nat := [1, 3, 2, 1, 2, 2, 3, 1, 3, 3, 2]
def baseStart_6267669 : Nat := 118140960795 + 6267669 * 2 ^ 59
def prefixEnd_6267669 : Nat := 4983230072969 + 3 ^ 40 * 6267669 * 2
def baseEnd_6267669 : Nat := 3218326780284943449913021

theorem tailTrace_6267669 : CollatzResearch.WordTrace tailWord_6267669 prefixEnd_6267669 3218326780284943449913021 := by
  unfold tailWord_6267669
  simp only [CollatzResearch.WordTrace]
  refine ⟨228600668730313120488814061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152400445820208746992542707 228600668730313120488814061)
  ·
    refine ⟨85725250773867420183305273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 228600668730313120488814061 85725250773867420183305273)
    ·
      refine ⟨64293938080400565137478955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 85725250773867420183305273 64293938080400565137478955)
      ·
        refine ⟨96440907120600847706218433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64293938080400565137478955 96440907120600847706218433)
        ·
          refine ⟨72330680340450635779663825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 96440907120600847706218433 72330680340450635779663825)
          ·
            refine ⟨54248010255337976834747869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 72330680340450635779663825 54248010255337976834747869)
            ·
              refine ⟨20343003845751741313030451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 54248010255337976834747869 20343003845751741313030451)
              ·
                refine ⟨30514505768627611969545677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20343003845751741313030451 30514505768627611969545677)
                ·
                  refine ⟨11442939663235354488579629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 30514505768627611969545677 11442939663235354488579629)
                  ·
                    refine ⟨4291102373713257933217361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11442939663235354488579629 4291102373713257933217361)
                    ·
                      refine ⟨3218326780284943449913021, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4291102373713257933217361 3218326780284943449913021)
                      ·
                        rfl

theorem cell23_6267669_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 3, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 3, 1, 3, 3, 2].length) (baseStart_6267669 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6267669 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6267669 prefixEnd_6267669 := by exact prefixLift 6267669
  have htrace : WordTrace (prefixWord ++ tailWord_6267669) baseStart_6267669 baseEnd_6267669 := by
    simpa [prefixWord, tailWord_6267669, baseEnd_6267669] using wordTrace_append hprefix tailTrace_6267669
  have hstable : (prefixWord ++ tailWord_6267669).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6267669).length < 2 ^ (prefixWord ++ tailWord_6267669).sum := by decide
  have hdescent : baseEnd_6267669 < baseStart_6267669 := by decide
  rcases family_descends (prefixWord ++ tailWord_6267669) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6267709 : List Nat := [1, 4, 1, 4, 2, 1, 1, 1, 2, 6]
def baseStart_6267709 : Nat := 118140960795 + 6267709 * 2 ^ 59
def prefixEnd_6267709 : Nat := 4983230072969 + 3 ^ 40 * 6267709 * 2
def baseEnd_6267709 : Nat := 1072782439837041097804279

theorem tailTrace_6267709 : CollatzResearch.WordTrace tailWord_6267709 prefixEnd_6267709 1072782439837041097804279 := by
  unfold tailWord_6267709
  simp only [CollatzResearch.WordTrace]
  refine ⟨228602127650168207320270181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152401418433445471546846787 228602127650168207320270181)
  ·
    refine ⟨42862898934406538872550659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 228602127650168207320270181 42862898934406538872550659)
    ·
      refine ⟨64294348401609808308825989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42862898934406538872550659 64294348401609808308825989)
      ·
        refine ⟨12055190325301839057904873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 64294348401609808308825989 12055190325301839057904873)
        ·
          refine ⟨9041392743976379293428655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12055190325301839057904873 9041392743976379293428655)
          ·
            refine ⟨13562089115964568940142983, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9041392743976379293428655 13562089115964568940142983)
            ·
              refine ⟨20343133673946853410214475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13562089115964568940142983 20343133673946853410214475)
              ·
                refine ⟨30514700510920280115321713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20343133673946853410214475 30514700510920280115321713)
                ·
                  refine ⟨22886025383190210086491285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 30514700510920280115321713 22886025383190210086491285)
                  ·
                    refine ⟨1072782439837041097804279, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 22886025383190210086491285 1072782439837041097804279)
                    ·
                      rfl

theorem cell23_6267709_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 2, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 2, 1, 1, 1, 2, 6].length) (baseStart_6267709 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6267709 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6267709 prefixEnd_6267709 := by exact prefixLift 6267709
  have htrace : WordTrace (prefixWord ++ tailWord_6267709) baseStart_6267709 baseEnd_6267709 := by
    simpa [prefixWord, tailWord_6267709, baseEnd_6267709] using wordTrace_append hprefix tailTrace_6267709
  have hstable : (prefixWord ++ tailWord_6267709).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6267709).length < 2 ^ (prefixWord ++ tailWord_6267709).sum := by decide
  have hdescent : baseEnd_6267709 < baseStart_6267709 := by decide
  rcases family_descends (prefixWord ++ tailWord_6267709) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6267762 : List Nat := [3, 2, 1, 2, 1, 1, 2, 3, 1, 2, 5]
def baseStart_6267762 : Nat := 118140960795 + 6267762 * 2 ^ 59
def prefixEnd_6267762 : Nat := 4983230072969 + 3 ^ 40 * 6267762 * 2
def baseEnd_6267762 : Nat := 3218374533985811586050093

theorem tailTrace_6267762 : CollatzResearch.WordTrace tailWord_6267762 prefixEnd_6267762 3218374533985811586050093 := by
  unfold tailWord_6267762
  simp only [CollatzResearch.WordTrace]
  refine ⟨57151015179744049342987385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 152402707145984131581299693 57151015179744049342987385)
  ·
    refine ⟨42863261384808037007240539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57151015179744049342987385 42863261384808037007240539)
    ·
      refine ⟨64294892077212055510860809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42863261384808037007240539 64294892077212055510860809)
      ·
        refine ⟨48221169057909041633145607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 64294892077212055510860809 48221169057909041633145607)
        ·
          refine ⟨72331753586863562449718411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48221169057909041633145607 72331753586863562449718411)
          ·
            refine ⟨108497630380295343674577617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 72331753586863562449718411 108497630380295343674577617)
            ·
              refine ⟨81373222785221507755933213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 108497630380295343674577617 81373222785221507755933213)
              ·
                refine ⟨30514958544458065408474955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 81373222785221507755933213 30514958544458065408474955)
                ·
                  refine ⟨45772437816687098112712433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30514958544458065408474955 45772437816687098112712433)
                  ·
                    refine ⟨34329328362515323584534325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 45772437816687098112712433 34329328362515323584534325)
                    ·
                      refine ⟨3218374533985811586050093, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 34329328362515323584534325 3218374533985811586050093)
                      ·
                        rfl

theorem cell23_6267762_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 2, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 2, 3, 1, 2, 5].length) (baseStart_6267762 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6267762 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6267762 prefixEnd_6267762 := by exact prefixLift 6267762
  have htrace : WordTrace (prefixWord ++ tailWord_6267762) baseStart_6267762 baseEnd_6267762 := by
    simpa [prefixWord, tailWord_6267762, baseEnd_6267762] using wordTrace_append hprefix tailTrace_6267762
  have hstable : (prefixWord ++ tailWord_6267762).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6267762).length < 2 ^ (prefixWord ++ tailWord_6267762).sum := by decide
  have hdescent : baseEnd_6267762 < baseStart_6267762 := by decide
  rcases family_descends (prefixWord ++ tailWord_6267762) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6267766 : List Nat := [5, 1, 1, 3, 1, 1, 2, 1, 2, 3, 3]
def baseStart_6267766 : Nat := 118140960795 + 6267766 * 2 ^ 59
def prefixEnd_6267766 : Nat := 4983230072969 + 3 ^ 40 * 6267766 * 2
def baseEnd_6267766 : Nat := 3218376587908429570400075

theorem tailTrace_6267766 : CollatzResearch.WordTrace tailWord_6267766 prefixEnd_6267766 3218376587908429570400075 := by
  unfold tailWord_6267766
  simp only [CollatzResearch.WordTrace]
  refine ⟨14287762913185106628443447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 152402804407307804036730101 14287762913185106628443447)
  ·
    refine ⟨21431644369777659942665171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14287762913185106628443447 21431644369777659942665171)
    ·
      refine ⟨32147466554666489913997757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21431644369777659942665171 32147466554666489913997757)
      ·
        refine ⟨12055299957999933717749159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 32147466554666489913997757 12055299957999933717749159)
        ·
          refine ⟨18082949936999900576623739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12055299957999933717749159 18082949936999900576623739)
          ·
            refine ⟨27124424905499850864935609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18082949936999900576623739 27124424905499850864935609)
            ·
              refine ⟨20343318679124888148701707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27124424905499850864935609 20343318679124888148701707)
              ·
                refine ⟨30514978018687332223052561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20343318679124888148701707 30514978018687332223052561)
                ·
                  refine ⟨22886233514015499167289421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 30514978018687332223052561 22886233514015499167289421)
                  ·
                    refine ⟨8582337567755812187733533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 22886233514015499167289421 8582337567755812187733533)
                    ·
                      refine ⟨3218376587908429570400075, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8582337567755812187733533 3218376587908429570400075)
                      ·
                        rfl

theorem cell23_6267766_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 1, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 1, 2, 1, 2, 3, 3].length) (baseStart_6267766 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6267766 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6267766 prefixEnd_6267766 := by exact prefixLift 6267766
  have htrace : WordTrace (prefixWord ++ tailWord_6267766) baseStart_6267766 baseEnd_6267766 := by
    simpa [prefixWord, tailWord_6267766, baseEnd_6267766] using wordTrace_append hprefix tailTrace_6267766
  have hstable : (prefixWord ++ tailWord_6267766).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6267766).length < 2 ^ (prefixWord ++ tailWord_6267766).sum := by decide
  have hdescent : baseEnd_6267766 < baseStart_6267766 := by decide
  rcases family_descends (prefixWord ++ tailWord_6267766) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6267792 : List Nat := [2, 1, 1, 1, 1, 1, 2, 2, 5, 4, 3]
def baseStart_6267792 : Nat := 118140960795 + 6267792 * 2 ^ 59
def prefixEnd_6267792 : Nat := 4983230072969 + 3 ^ 40 * 6267792 * 2
def baseEnd_6267792 : Nat := 3218389938405446468674955

theorem tailTrace_6267792 : CollatzResearch.WordTrace tailWord_6267792 prefixEnd_6267792 3218389938405446468674955 := by
  unfold tailWord_6267792
  simp only [CollatzResearch.WordTrace]
  refine ⟨114302577454433756247770815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 152403436605911674997027753 114302577454433756247770815)
  ·
    refine ⟨171453866181650634371656223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114302577454433756247770815 171453866181650634371656223)
    ·
      refine ⟨257180799272475951557484335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 171453866181650634371656223 257180799272475951557484335)
      ·
        refine ⟨385771198908713927336226503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 257180799272475951557484335 385771198908713927336226503)
        ·
          refine ⟨578656798363070891004339755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 385771198908713927336226503 578656798363070891004339755)
          ·
            refine ⟨867985197544606336506509633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 578656798363070891004339755 867985197544606336506509633)
            ·
              refine ⟨650988898158454752379882225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 867985197544606336506509633 650988898158454752379882225)
              ·
                refine ⟨488241673618841064284911669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 650988898158454752379882225 488241673618841064284911669)
                ·
                  refine ⟨45772656901766349776710469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 488241673618841064284911669 45772656901766349776710469)
                  ·
                    refine ⟨8582373169081190583133213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 45772656901766349776710469 8582373169081190583133213)
                    ·
                      refine ⟨3218389938405446468674955, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8582373169081190583133213 3218389938405446468674955)
                      ·
                        rfl

theorem cell23_6267792_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 2, 5, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 2, 5, 4, 3].length) (baseStart_6267792 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6267792 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6267792 prefixEnd_6267792 := by exact prefixLift 6267792
  have htrace : WordTrace (prefixWord ++ tailWord_6267792) baseStart_6267792 baseEnd_6267792 := by
    simpa [prefixWord, tailWord_6267792, baseEnd_6267792] using wordTrace_append hprefix tailTrace_6267792
  have hstable : (prefixWord ++ tailWord_6267792).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6267792).length < 2 ^ (prefixWord ++ tailWord_6267792).sum := by decide
  have hdescent : baseEnd_6267792 < baseStart_6267792 := by decide
  rcases family_descends (prefixWord ++ tailWord_6267792) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6267812 : List Nat := [2, 3, 1, 2, 1, 2, 1, 3, 8]
def baseStart_6267812 : Nat := 118140960795 + 6267812 * 2 ^ 59
def prefixEnd_6267812 : Nat := 4983230072969 + 3 ^ 40 * 6267812 * 2
def baseEnd_6267812 : Nat := 357600023113170710047207

theorem tailTrace_6267812 : CollatzResearch.WordTrace tailWord_6267812 prefixEnd_6267812 357600023113170710047207 := by
  unfold tailWord_6267812
  simp only [CollatzResearch.WordTrace]
  refine ⟨114302942184397527955634845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 152403922912530037274179793 114302942184397527955634845)
  ·
    refine ⟨42863603319149072983363067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 114302942184397527955634845 42863603319149072983363067)
    ·
      refine ⟨64295404978723609475044601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42863603319149072983363067 64295404978723609475044601)
      ·
        refine ⟨48221553734042707106283451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 64295404978723609475044601 48221553734042707106283451)
        ·
          refine ⟨72332330601064060659425177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48221553734042707106283451 72332330601064060659425177)
          ·
            refine ⟨54249247950798045494568883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 72332330601064060659425177 54249247950798045494568883)
            ·
              refine ⟨81373871926197068241853325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 54249247950798045494568883 81373871926197068241853325)
              ·
                refine ⟨30515201972323900590694997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 81373871926197068241853325 30515201972323900590694997)
                ·
                  refine ⟨357600023113170710047207, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 30515201972323900590694997 357600023113170710047207)
                  ·
                    rfl

theorem cell23_6267812_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 1, 3, 8].length) (baseStart_6267812 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6267812 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6267812 prefixEnd_6267812 := by exact prefixLift 6267812
  have htrace : WordTrace (prefixWord ++ tailWord_6267812) baseStart_6267812 baseEnd_6267812 := by
    simpa [prefixWord, tailWord_6267812, baseEnd_6267812] using wordTrace_append hprefix tailTrace_6267812
  have hstable : (prefixWord ++ tailWord_6267812).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6267812).length < 2 ^ (prefixWord ++ tailWord_6267812).sum := by decide
  have hdescent : baseEnd_6267812 < baseStart_6267812 := by decide
  rcases family_descends (prefixWord ++ tailWord_6267812) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6267829 : List Nat := [1, 3, 3, 2, 1, 1, 3, 3, 6]
def baseStart_6267829 : Nat := 118140960795 + 6267829 * 2 ^ 59
def prefixEnd_6267829 : Nat := 4983230072969 + 3 ^ 40 * 6267829 * 2
def baseEnd_6267829 : Nat := 357600993021073647101365

theorem tailTrace_6267829 : CollatzResearch.WordTrace tailWord_6267829 prefixEnd_6267829 357600993021073647101365 := by
  unfold tailWord_6267829
  simp only [CollatzResearch.WordTrace]
  refine ⟨228606504409733467814638541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152404336273155645209759027 228606504409733467814638541)
  ·
    refine ⟨85727439153650050430489453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 228606504409733467814638541 85727439153650050430489453)
    ·
      refine ⟨32147789682618768911433545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 85727439153650050430489453 32147789682618768911433545)
      ·
        refine ⟨24110842261964076683575159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32147789682618768911433545 24110842261964076683575159)
        ·
          refine ⟨36166263392946115025362739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24110842261964076683575159 36166263392946115025362739)
          ·
            refine ⟨54249395089419172538044109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36166263392946115025362739 54249395089419172538044109)
            ·
              refine ⟨20343523158532189701766541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 54249395089419172538044109 20343523158532189701766541)
              ·
                refine ⟨7628821184449571138162453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20343523158532189701766541 7628821184449571138162453)
                ·
                  refine ⟨357600993021073647101365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7628821184449571138162453 357600993021073647101365)
                  ·
                    rfl

theorem cell23_6267829_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 3, 3, 6].length) (baseStart_6267829 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6267829 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6267829 prefixEnd_6267829 := by exact prefixLift 6267829
  have htrace : WordTrace (prefixWord ++ tailWord_6267829) baseStart_6267829 baseEnd_6267829 := by
    simpa [prefixWord, tailWord_6267829, baseEnd_6267829] using wordTrace_append hprefix tailTrace_6267829
  have hstable : (prefixWord ++ tailWord_6267829).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6267829).length < 2 ^ (prefixWord ++ tailWord_6267829).sum := by decide
  have hdescent : baseEnd_6267829 < baseStart_6267829 := by decide
  rcases family_descends (prefixWord ++ tailWord_6267829) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6267889 : List Nat := [1, 2, 2, 2, 4, 1, 1, 3, 1, 6]
def baseStart_6267889 : Nat := 118140960795 + 6267889 * 2 ^ 59
def prefixEnd_6267889 : Nat := 4983230072969 + 3 ^ 40 * 6267889 * 2
def baseEnd_6267889 : Nat := 1072813248676310863054003

theorem tailTrace_6267889 : CollatzResearch.WordTrace tailWord_6267889 prefixEnd_6267889 1072813248676310863054003 := by
  unfold tailWord_6267889
  simp only [CollatzResearch.WordTrace]
  refine ⟨228608692789516098061822721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152405795193010732041215147 228608692789516098061822721)
  ·
    refine ⟨171456519592137073546367041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 228608692789516098061822721 171456519592137073546367041)
    ·
      refine ⟨128592389694102805159775281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 171456519592137073546367041 128592389694102805159775281)
      ·
        refine ⟨96444292270577103869831461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 128592389694102805159775281 96444292270577103869831461)
        ·
          refine ⟨18083304800733206975593399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 96444292270577103869831461 18083304800733206975593399)
          ·
            refine ⟨27124957201099810463390099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18083304800733206975593399 27124957201099810463390099)
            ·
              refine ⟨40687435801649715695085149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27124957201099810463390099 40687435801649715695085149)
              ·
                refine ⟨15257788425618643385656931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 40687435801649715695085149 15257788425618643385656931)
                ·
                  refine ⟨22886682638427965078485397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15257788425618643385656931 22886682638427965078485397)
                  ·
                    refine ⟨1072813248676310863054003, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 22886682638427965078485397 1072813248676310863054003)
                    ·
                      rfl

theorem cell23_6267889_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 1, 1, 3, 1, 6].length) (baseStart_6267889 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6267889 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6267889 prefixEnd_6267889 := by exact prefixLift 6267889
  have htrace : WordTrace (prefixWord ++ tailWord_6267889) baseStart_6267889 baseEnd_6267889 := by
    simpa [prefixWord, tailWord_6267889, baseEnd_6267889] using wordTrace_append hprefix tailTrace_6267889
  have hstable : (prefixWord ++ tailWord_6267889).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6267889).length < 2 ^ (prefixWord ++ tailWord_6267889).sum := by decide
  have hdescent : baseEnd_6267889 < baseStart_6267889 := by decide
  rcases family_descends (prefixWord ++ tailWord_6267889) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6267890 : List Nat := [3, 2, 1, 5, 1, 1, 1, 2, 3, 1, 3]
def baseStart_6267890 : Nat := 118140960795 + 6267890 * 2 ^ 59
def prefixEnd_6267890 : Nat := 4983230072969 + 3 ^ 40 * 6267890 * 2
def baseEnd_6267890 : Nat := 3218440259509587085249505

theorem tailTrace_6267890 : CollatzResearch.WordTrace tailWord_6267890 prefixEnd_6267890 3218440259509587085249505 := by
  unfold tailWord_6267890
  simp only [CollatzResearch.WordTrace]
  refine ⟨57152182315628118808152281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 152405819508341650155072749 57152182315628118808152281)
  ·
    refine ⟨42864136736721089106114211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57152182315628118808152281 42864136736721089106114211)
    ·
      refine ⟨64296205105081633659171317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42864136736721089106114211 64296205105081633659171317)
      ·
        refine ⟨6027769228601403155547311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 64296205105081633659171317 6027769228601403155547311)
        ·
          refine ⟨9041653842902104733320967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6027769228601403155547311 9041653842902104733320967)
          ·
            refine ⟨13562480764353157099981451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9041653842902104733320967 13562480764353157099981451)
            ·
              refine ⟨20343721146529735649972177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13562480764353157099981451 20343721146529735649972177)
              ·
                refine ⟨15257790859897301737479133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20343721146529735649972177 15257790859897301737479133)
                ·
                  refine ⟨5721671572461488151554675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15257790859897301737479133 5721671572461488151554675)
                  ·
                    refine ⟨8582507358692232227332013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5721671572461488151554675 8582507358692232227332013)
                    ·
                      refine ⟨3218440259509587085249505, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8582507358692232227332013 3218440259509587085249505)
                      ·
                        rfl

theorem cell23_6267890_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 5, 1, 1, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 5, 1, 1, 1, 2, 3, 1, 3].length) (baseStart_6267890 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6267890 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6267890 prefixEnd_6267890 := by exact prefixLift 6267890
  have htrace : WordTrace (prefixWord ++ tailWord_6267890) baseStart_6267890 baseEnd_6267890 := by
    simpa [prefixWord, tailWord_6267890, baseEnd_6267890] using wordTrace_append hprefix tailTrace_6267890
  have hstable : (prefixWord ++ tailWord_6267890).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6267890).length < 2 ^ (prefixWord ++ tailWord_6267890).sum := by decide
  have hdescent : baseEnd_6267890 < baseStart_6267890 := by decide
  rcases family_descends (prefixWord ++ tailWord_6267890) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6267909 : List Nat := [1, 3, 1, 1, 2, 3, 1, 4, 1, 2, 4]
def baseStart_6267909 : Nat := 118140960795 + 6267909 * 2 ^ 59
def prefixEnd_6267909 : Nat := 4983230072969 + 3 ^ 40 * 6267909 * 2
def baseEnd_6267909 : Nat := 3218450015642022510911917

theorem tailTrace_6267909 : CollatzResearch.WordTrace tailWord_6267909 prefixEnd_6267909 3218450015642022510911917 := by
  unfold tailWord_6267909
  simp only [CollatzResearch.WordTrace]
  refine ⟨228609422249443641477550781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152406281499629094318367187 228609422249443641477550781)
  ·
    refine ⟨85728533343541365554081543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 228609422249443641477550781 85728533343541365554081543)
    ·
      refine ⟨128592800015312048331122315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85728533343541365554081543 128592800015312048331122315)
      ·
        refine ⟨192889200022968072496683473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 128592800015312048331122315 192889200022968072496683473)
        ·
          refine ⟨144666900017226054372512605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 192889200022968072496683473 144666900017226054372512605)
          ·
            refine ⟨54250087506459770389692227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 144666900017226054372512605 54250087506459770389692227)
            ·
              refine ⟨81375131259689655584538341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 54250087506459770389692227 81375131259689655584538341)
              ·
                refine ⟨15257837111191810422100939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 81375131259689655584538341 15257837111191810422100939)
                ·
                  refine ⟨22886755666787715633151409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15257837111191810422100939 22886755666787715633151409)
                  ·
                    refine ⟨17165066750090786724863557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 22886755666787715633151409 17165066750090786724863557)
                    ·
                      refine ⟨3218450015642022510911917, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17165066750090786724863557 3218450015642022510911917)
                      ·
                        rfl

theorem cell23_6267909_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 1, 4, 1, 2, 4].length) (baseStart_6267909 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6267909 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6267909 prefixEnd_6267909 := by exact prefixLift 6267909
  have htrace : WordTrace (prefixWord ++ tailWord_6267909) baseStart_6267909 baseEnd_6267909 := by
    simpa [prefixWord, tailWord_6267909, baseEnd_6267909] using wordTrace_append hprefix tailTrace_6267909
  have hstable : (prefixWord ++ tailWord_6267909).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6267909).length < 2 ^ (prefixWord ++ tailWord_6267909).sum := by decide
  have hdescent : baseEnd_6267909 < baseStart_6267909 := by decide
  rcases family_descends (prefixWord ++ tailWord_6267909) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6267929 : List Nat := [1, 2, 1, 2, 1, 1, 4, 2, 3, 3, 3]
def baseStart_6267929 : Nat := 118140960795 + 6267929 * 2 ^ 59
def prefixEnd_6267929 : Nat := 4983230072969 + 3 ^ 40 * 6267929 * 2
def baseEnd_6267929 : Nat := 3218460285255112432661825

theorem tailTrace_6267929 : CollatzResearch.WordTrace tailWord_6267929 prefixEnd_6267929 3218460285255112432661825 := by
  unfold tailWord_6267929
  simp only [CollatzResearch.WordTrace]
  refine ⟨228610151709371184893278841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152406767806247456595519227 228610151709371184893278841)
  ·
    refine ⟨171457613782028388669959131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 228610151709371184893278841 171457613782028388669959131)
    ·
      refine ⟨257186420673042583004938697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 171457613782028388669959131 257186420673042583004938697)
      ·
        refine ⟨192889815504781937253704023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 257186420673042583004938697 192889815504781937253704023)
        ·
          refine ⟨289334723257172905880556035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 192889815504781937253704023 289334723257172905880556035)
          ·
            refine ⟨434002084885759358820834053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 289334723257172905880556035 434002084885759358820834053)
            ·
              refine ⟨81375390916079879778906385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 434002084885759358820834053 81375390916079879778906385)
              ·
                refine ⟨61031543187059909834179789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 81375390916079879778906385 61031543187059909834179789)
                ·
                  refine ⟨22886828695147466187817421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 61031543187059909834179789 22886828695147466187817421)
                  ·
                    refine ⟨8582560760680299820431533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 22886828695147466187817421 8582560760680299820431533)
                    ·
                      refine ⟨3218460285255112432661825, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8582560760680299820431533 3218460285255112432661825)
                      ·
                        rfl

theorem cell23_6267929_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 4, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 4, 2, 3, 3, 3].length) (baseStart_6267929 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6267929 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6267929 prefixEnd_6267929 := by exact prefixLift 6267929
  have htrace : WordTrace (prefixWord ++ tailWord_6267929) baseStart_6267929 baseEnd_6267929 := by
    simpa [prefixWord, tailWord_6267929, baseEnd_6267929] using wordTrace_append hprefix tailTrace_6267929
  have hstable : (prefixWord ++ tailWord_6267929).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6267929).length < 2 ^ (prefixWord ++ tailWord_6267929).sum := by decide
  have hdescent : baseEnd_6267929 < baseStart_6267929 := by decide
  rcases family_descends (prefixWord ++ tailWord_6267929) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6267930 : List Nat := [3, 1, 1, 3, 1, 2, 1, 6, 1, 2, 2]
def baseStart_6267930 : Nat := 118140960795 + 6267930 * 2 ^ 59
def prefixEnd_6267930 : Nat := 4983230072969 + 3 ^ 40 * 6267930 * 2
def baseEnd_6267930 : Nat := 3218460798735766928749321

theorem tailTrace_6267930 : CollatzResearch.WordTrace tailWord_6267930 prefixEnd_6267930 3218460798735766928749321 := by
  unfold tailWord_6267930
  simp only [CollatzResearch.WordTrace]
  refine ⟨57152547045591890516016311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 152406792121578374709376829 57152547045591890516016311)
  ·
    refine ⟨85728820568387835774024467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57152547045591890516016311 85728820568387835774024467)
    ·
      refine ⟨128593230852581753661036701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85728820568387835774024467 128593230852581753661036701)
      ·
        refine ⟨48222461569718157622888763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 128593230852581753661036701 48222461569718157622888763)
        ·
          refine ⟨72333692354577236434333145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48222461569718157622888763 72333692354577236434333145)
          ·
            refine ⟨54250269265932927325749859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 72333692354577236434333145 54250269265932927325749859)
            ·
              refine ⟨81375403898899390988624789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 54250269265932927325749859 81375403898899390988624789)
              ·
                refine ⟨3814472057760908952591787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 81375403898899390988624789 3814472057760908952591787)
                ·
                  refine ⟨5721708086641363428887681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3814472057760908952591787 5721708086641363428887681)
                  ·
                    refine ⟨4291281064981022571665761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5721708086641363428887681 4291281064981022571665761)
                    ·
                      refine ⟨3218460798735766928749321, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4291281064981022571665761 3218460798735766928749321)
                      ·
                        rfl

theorem cell23_6267930_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 1, 6, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 1, 6, 1, 2, 2].length) (baseStart_6267930 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6267930 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6267930 prefixEnd_6267930 := by exact prefixLift 6267930
  have htrace : WordTrace (prefixWord ++ tailWord_6267930) baseStart_6267930 baseEnd_6267930 := by
    simpa [prefixWord, tailWord_6267930, baseEnd_6267930] using wordTrace_append hprefix tailTrace_6267930
  have hstable : (prefixWord ++ tailWord_6267930).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6267930).length < 2 ^ (prefixWord ++ tailWord_6267930).sum := by decide
  have hdescent : baseEnd_6267930 < baseStart_6267930 := by decide
  rcases family_descends (prefixWord ++ tailWord_6267930) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6267940 : List Nat := [2, 3, 1, 4, 1, 2, 3, 1, 2, 4]
def baseStart_6267940 : Nat := 118140960795 + 6267940 * 2 ^ 59
def prefixEnd_6267940 : Nat := 4983230072969 + 3 ^ 40 * 6267940 * 2
def baseEnd_6267940 : Nat := 1072821977847437296541425

theorem tailTrace_6267940 : CollatzResearch.WordTrace tailWord_6267940 prefixEnd_6267940 1072821977847437296541425 := by
  unfold tailWord_6267940
  simp only [CollatzResearch.WordTrace]
  refine ⟨114305276456165666885964637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 152407035274887555847952849 114305276456165666885964637)
  ·
    refine ⟨42864478671062125082236739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 114305276456165666885964637 42864478671062125082236739)
    ·
      refine ⟨64296718006593187623355109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42864478671062125082236739 64296718006593187623355109)
      ·
        refine ⟨12055634626236222679379083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 64296718006593187623355109 12055634626236222679379083)
        ·
          refine ⟨18083451939354334019068625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12055634626236222679379083 18083451939354334019068625)
          ·
            refine ⟨13562588954515750514301469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18083451939354334019068625 13562588954515750514301469)
            ·
              refine ⟨5085970857943406442863051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13562588954515750514301469 5085970857943406442863051)
              ·
                refine ⟨7628956286915109664294577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5085970857943406442863051 7628956286915109664294577)
                ·
                  refine ⟨5721717215186332248220933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7628956286915109664294577 5721717215186332248220933)
                  ·
                    refine ⟨1072821977847437296541425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5721717215186332248220933 1072821977847437296541425)
                    ·
                      rfl

theorem cell23_6267940_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 2, 3, 1, 2, 4].length) (baseStart_6267940 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6267940 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6267940 prefixEnd_6267940 := by exact prefixLift 6267940
  have htrace : WordTrace (prefixWord ++ tailWord_6267940) baseStart_6267940 baseEnd_6267940 := by
    simpa [prefixWord, tailWord_6267940, baseEnd_6267940] using wordTrace_append hprefix tailTrace_6267940
  have hstable : (prefixWord ++ tailWord_6267940).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6267940).length < 2 ^ (prefixWord ++ tailWord_6267940).sum := by decide
  have hdescent : baseEnd_6267940 < baseStart_6267940 := by decide
  rcases family_descends (prefixWord ++ tailWord_6267940) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6267943 : List Nat := [1, 1, 7, 1, 1, 1, 3, 1, 1, 2, 4]
def baseStart_6267943 : Nat := 118140960795 + 6267943 * 2 ^ 59
def prefixEnd_6267943 : Nat := 4983230072969 + 3 ^ 40 * 6267943 * 2
def baseEnd_6267943 : Nat := 3218467473984275377886761

theorem tailTrace_6267943 : CollatzResearch.WordTrace tailWord_6267943 prefixEnd_6267943 3218467473984275377886761 := by
  unfold tailWord_6267943
  simp only [CollatzResearch.WordTrace]
  refine ⟨228610662331320465284288483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152407108220880310189525655 228610662331320465284288483)
  ·
    refine ⟨342915993496980697926432725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 228610662331320465284288483 342915993496980697926432725)
    ·
      refine ⟨8037093597585485107650767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 342915993496980697926432725 8037093597585485107650767)
      ·
        refine ⟨12055640396378227661476151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8037093597585485107650767 12055640396378227661476151)
        ·
          refine ⟨18083460594567341492214227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12055640396378227661476151 18083460594567341492214227)
          ·
            refine ⟨27125190891851012238321341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18083460594567341492214227 27125190891851012238321341)
            ·
              refine ⟨10171946584444129589370503, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27125190891851012238321341 10171946584444129589370503)
              ·
                refine ⟨15257919876666194384055755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10171946584444129589370503 15257919876666194384055755)
                ·
                  refine ⟨22886879814999291576083633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15257919876666194384055755 22886879814999291576083633)
                  ·
                    refine ⟨17165159861249468682062725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 22886879814999291576083633 17165159861249468682062725)
                    ·
                      refine ⟨3218467473984275377886761, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17165159861249468682062725 3218467473984275377886761)
                      ·
                        rfl

theorem cell23_6267943_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 1, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 1, 3, 1, 1, 2, 4].length) (baseStart_6267943 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6267943 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6267943 prefixEnd_6267943 := by exact prefixLift 6267943
  have htrace : WordTrace (prefixWord ++ tailWord_6267943) baseStart_6267943 baseEnd_6267943 := by
    simpa [prefixWord, tailWord_6267943, baseEnd_6267943] using wordTrace_append hprefix tailTrace_6267943
  have hstable : (prefixWord ++ tailWord_6267943).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6267943).length < 2 ^ (prefixWord ++ tailWord_6267943).sum := by decide
  have hdescent : baseEnd_6267943 < baseStart_6267943 := by decide
  rcases family_descends (prefixWord ++ tailWord_6267943) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6267973 : List Nat := [1, 3, 1, 1, 1, 3, 4, 3, 1, 3, 2]
def baseStart_6267973 : Nat := 118140960795 + 6267973 * 2 ^ 59
def prefixEnd_6267973 : Nat := 4983230072969 + 3 ^ 40 * 6267973 * 2
def baseEnd_6267973 : Nat := 3218482878403910260511623

theorem tailTrace_6267973 : CollatzResearch.WordTrace tailWord_6267973 prefixEnd_6267973 3218482878403910260511623 := by
  unfold tailWord_6267973
  simp only [CollatzResearch.WordTrace]
  refine ⟨228611756521211780407880573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152407837680807853605253715 228611756521211780407880573)
  ·
    refine ⟨85729408695454417652955215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 228611756521211780407880573 85729408695454417652955215)
    ·
      refine ⟨128594113043181626479432823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85729408695454417652955215 128594113043181626479432823)
      ·
        refine ⟨192891169564772439719149235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 128594113043181626479432823 192891169564772439719149235)
        ·
          refine ⟨289336754347158659578723853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 192891169564772439719149235 289336754347158659578723853)
          ·
            refine ⟨108501282880184497342021445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 289336754347158659578723853 108501282880184497342021445)
            ·
              refine ⟨20343990540034593251629021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 108501282880184497342021445 20343990540034593251629021)
              ·
                refine ⟨7628996452512972469360883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20343990540034593251629021 7628996452512972469360883)
                ·
                  refine ⟨11443494678769458704041325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7628996452512972469360883 11443494678769458704041325)
                  ·
                    refine ⟨4291310504538547014015497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11443494678769458704041325 4291310504538547014015497)
                    ·
                      refine ⟨3218482878403910260511623, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4291310504538547014015497 3218482878403910260511623)
                      ·
                        rfl

theorem cell23_6267973_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 4, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 4, 3, 1, 3, 2].length) (baseStart_6267973 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6267973 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6267973 prefixEnd_6267973 := by exact prefixLift 6267973
  have htrace : WordTrace (prefixWord ++ tailWord_6267973) baseStart_6267973 baseEnd_6267973 := by
    simpa [prefixWord, tailWord_6267973, baseEnd_6267973] using wordTrace_append hprefix tailTrace_6267973
  have hstable : (prefixWord ++ tailWord_6267973).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6267973).length < 2 ^ (prefixWord ++ tailWord_6267973).sum := by decide
  have hdescent : baseEnd_6267973 < baseStart_6267973 := by decide
  rcases family_descends (prefixWord ++ tailWord_6267973) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6267989 : List Nat := [1, 3, 2, 2, 1, 2, 1, 2, 1, 3, 5]
def baseStart_6267989 : Nat := 118140960795 + 6267989 * 2 ^ 59
def prefixEnd_6267989 : Nat := 4983230072969 + 3 ^ 40 * 6267989 * 2
def baseEnd_6267989 : Nat := 3218491094094382197911549

theorem tailTrace_6267989 : CollatzResearch.WordTrace tailWord_6267989 prefixEnd_6267989 3218491094094382197911549 := by
  unfold tailWord_6267989
  simp only [CollatzResearch.WordTrace]
  refine ⟨228612340089153815140463021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152408226726102543426975347 228612340089153815140463021)
  ·
    refine ⟨85729627533432680677673633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 228612340089153815140463021 85729627533432680677673633)
    ·
      refine ⟨64297220650074510508255225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 85729627533432680677673633 64297220650074510508255225)
      ·
        refine ⟨48222915487555882881191419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 64297220650074510508255225 48222915487555882881191419)
        ·
          refine ⟨72334373231333824321787129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48222915487555882881191419 72334373231333824321787129)
          ·
            refine ⟨54250779923500368241340347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 72334373231333824321787129 54250779923500368241340347)
            ·
              refine ⟨81376169885250552362010521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 54250779923500368241340347 81376169885250552362010521)
              ·
                refine ⟨61032127413937914271507891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 81376169885250552362010521 61032127413937914271507891)
                ·
                  refine ⟨91548191120906871407261837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 61032127413937914271507891 91548191120906871407261837)
                  ·
                    refine ⟨34330571670340076777723189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 91548191120906871407261837 34330571670340076777723189)
                    ·
                      refine ⟨3218491094094382197911549, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 34330571670340076777723189 3218491094094382197911549)
                      ·
                        rfl

theorem cell23_6267989_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 1, 2, 1, 3, 5].length) (baseStart_6267989 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6267989 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6267989 prefixEnd_6267989 := by exact prefixLift 6267989
  have htrace : WordTrace (prefixWord ++ tailWord_6267989) baseStart_6267989 baseEnd_6267989 := by
    simpa [prefixWord, tailWord_6267989, baseEnd_6267989] using wordTrace_append hprefix tailTrace_6267989
  have hstable : (prefixWord ++ tailWord_6267989).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6267989).length < 2 ^ (prefixWord ++ tailWord_6267989).sum := by decide
  have hdescent : baseEnd_6267989 < baseStart_6267989 := by decide
  rcases family_descends (prefixWord ++ tailWord_6267989) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6267997 : List Nat := [1, 4, 4, 1, 2, 1, 1, 3, 2, 1, 3]
def baseStart_6267997 : Nat := 118140960795 + 6267997 * 2 ^ 59
def prefixEnd_6267997 : Nat := 4983230072969 + 3 ^ 40 * 6267997 * 2
def baseEnd_6267997 : Nat := 3218495201939618166611513

theorem tailTrace_6267997 : CollatzResearch.WordTrace tailWord_6267997 prefixEnd_6267997 3218495201939618166611513 := by
  unfold tailWord_6267997
  simp only [CollatzResearch.WordTrace]
  refine ⟨228612631873124832506754245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152408421248749888337836163 228612631873124832506754245)
  ·
    refine ⟨42864868476210906095016421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 228612631873124832506754245 42864868476210906095016421)
    ·
      refine ⟨8037162839289544892815579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 42864868476210906095016421 8037162839289544892815579)
      ·
        refine ⟨12055744258934317339223369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8037162839289544892815579 12055744258934317339223369)
        ·
          refine ⟨9041808194200738004417527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12055744258934317339223369 9041808194200738004417527)
          ·
            refine ⟨13562712291301107006626291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9041808194200738004417527 13562712291301107006626291)
            ·
              refine ⟨20344068436951660509939437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13562712291301107006626291 20344068436951660509939437)
              ·
                refine ⟨7629025663856872691227289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20344068436951660509939437 7629025663856872691227289)
                ·
                  refine ⟨5721769247892654518420467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7629025663856872691227289 5721769247892654518420467)
                  ·
                    refine ⟨8582653871838981777630701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5721769247892654518420467 8582653871838981777630701)
                    ·
                      refine ⟨3218495201939618166611513, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8582653871838981777630701 3218495201939618166611513)
                      ·
                        rfl

theorem cell23_6267997_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 2, 1, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 2, 1, 1, 3, 2, 1, 3].length) (baseStart_6267997 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6267997 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6267997 prefixEnd_6267997 := by exact prefixLift 6267997
  have htrace : WordTrace (prefixWord ++ tailWord_6267997) baseStart_6267997 baseEnd_6267997 := by
    simpa [prefixWord, tailWord_6267997, baseEnd_6267997] using wordTrace_append hprefix tailTrace_6267997
  have hstable : (prefixWord ++ tailWord_6267997).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6267997).length < 2 ^ (prefixWord ++ tailWord_6267997).sum := by decide
  have hdescent : baseEnd_6267997 < baseStart_6267997 := by decide
  rcases family_descends (prefixWord ++ tailWord_6267997) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6267999 : List Nat := [1, 1, 2, 3, 1, 1, 4, 1, 1, 4, 4]
def baseStart_6267999 : Nat := 118140960795 + 6267999 * 2 ^ 59
def prefixEnd_6267999 : Nat := 4983230072969 + 3 ^ 40 * 6267999 * 2
def baseEnd_6267999 : Nat := 3218496228900927158786503

theorem tailTrace_6267999 : CollatzResearch.WordTrace tailWord_6267999 prefixEnd_6267999 3218496228900927158786503 := by
  unfold tailWord_6267999
  simp only [CollatzResearch.WordTrace]
  refine ⟨228612704819117586848327051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152408469879411724565551367 228612704819117586848327051)
  ·
    refine ⟨342919057228676380272490577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 228612704819117586848327051 342919057228676380272490577)
    ·
      refine ⟨257189292921507285204367933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 342919057228676380272490577 257189292921507285204367933)
      ·
        refine ⟨96445984845565231951637975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 257189292921507285204367933 96445984845565231951637975)
        ·
          refine ⟨144668977268347847927456963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 96445984845565231951637975 144668977268347847927456963)
          ·
            refine ⟨217003465902521771891185445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 144668977268347847927456963 217003465902521771891185445)
            ·
              refine ⟨40688149856722832229597271, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 217003465902521771891185445 40688149856722832229597271)
              ·
                refine ⟨61032224785084248344395907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40688149856722832229597271 61032224785084248344395907)
                ·
                  refine ⟨91548337177626372516593861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 61032224785084248344395907 91548337177626372516593861)
                  ·
                    refine ⟨17165313220804944846861349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 91548337177626372516593861 17165313220804944846861349)
                    ·
                      refine ⟨3218496228900927158786503, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17165313220804944846861349 3218496228900927158786503)
                      ·
                        rfl

theorem cell23_6267999_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 4, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 4, 1, 1, 4, 4].length) (baseStart_6267999 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6267999 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6267999 prefixEnd_6267999 := by exact prefixLift 6267999
  have htrace : WordTrace (prefixWord ++ tailWord_6267999) baseStart_6267999 baseEnd_6267999 := by
    simpa [prefixWord, tailWord_6267999, baseEnd_6267999] using wordTrace_append hprefix tailTrace_6267999
  have hstable : (prefixWord ++ tailWord_6267999).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6267999).length < 2 ^ (prefixWord ++ tailWord_6267999).sum := by decide
  have hdescent : baseEnd_6267999 < baseStart_6267999 := by decide
  rcases family_descends (prefixWord ++ tailWord_6267999) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6268037 : List Nat := [1, 3, 1, 1, 6, 1, 2, 2, 2, 2, 2]
def baseStart_6268037 : Nat := 118140960795 + 6268037 * 2 ^ 59
def prefixEnd_6268037 : Nat := 4983230072969 + 3 ^ 40 * 6268037 * 2
def baseEnd_6268037 : Nat := 3218515741165798010111329

theorem tailTrace_6268037 : CollatzResearch.WordTrace tailWord_6268037 prefixEnd_6268037 3218515741165798010111329 := by
  unfold tailWord_6268037
  simp only [CollatzResearch.WordTrace]
  refine ⟨228614090792979919338210365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152409393861986612892140243 228614090792979919338210365)
  ·
    refine ⟨85730284047367469751828887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 228614090792979919338210365 85730284047367469751828887)
    ·
      refine ⟨128595426071051204627743331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85730284047367469751828887 128595426071051204627743331)
      ·
        refine ⟨192893139106576806941614997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 128595426071051204627743331 192893139106576806941614997)
        ·
          refine ⟨9041865895620787825388203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 192893139106576806941614997 9041865895620787825388203)
          ·
            refine ⟨13562798843431181738082305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9041865895620787825388203 13562798843431181738082305)
            ·
              refine ⟨10172099132573386303561729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13562798843431181738082305 10172099132573386303561729)
              ·
                refine ⟨7629074349430039727671297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10172099132573386303561729 7629074349430039727671297)
                ·
                  refine ⟨5721805762072529795753473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7629074349430039727671297 5721805762072529795753473)
                  ·
                    refine ⟨4291354321554397346815105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5721805762072529795753473 4291354321554397346815105)
                    ·
                      refine ⟨3218515741165798010111329, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4291354321554397346815105 3218515741165798010111329)
                      ·
                        rfl

theorem cell23_6268037_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 6, 1, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 6, 1, 2, 2, 2, 2, 2].length) (baseStart_6268037 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6268037 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6268037 prefixEnd_6268037 := by exact prefixLift 6268037
  have htrace : WordTrace (prefixWord ++ tailWord_6268037) baseStart_6268037 baseEnd_6268037 := by
    simpa [prefixWord, tailWord_6268037, baseEnd_6268037] using wordTrace_append hprefix tailTrace_6268037
  have hstable : (prefixWord ++ tailWord_6268037).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6268037).length < 2 ^ (prefixWord ++ tailWord_6268037).sum := by decide
  have hdescent : baseEnd_6268037 < baseStart_6268037 := by decide
  rcases family_descends (prefixWord ++ tailWord_6268037) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6268039 : List Nat := [1, 1, 4, 2, 1, 1, 1, 2, 3, 7]
def baseStart_6268039 : Nat := 118140960795 + 6268039 * 2 ^ 59
def prefixEnd_6268039 : Nat := 4983230072969 + 3 ^ 40 * 6268039 * 2
def baseEnd_6268039 : Nat := 1072838922709035667428773

theorem tailTrace_6268039 : CollatzResearch.WordTrace tailWord_6268039 prefixEnd_6268039 1072838922709035667428773 := by
  unfold tailWord_6268039
  simp only [CollatzResearch.WordTrace]
  refine ⟨228614163738972673679783171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152409442492648449119855447 228614163738972673679783171)
  ·
    refine ⟨342921245608459010519674757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 228614163738972673679783171 342921245608459010519674757)
    ·
      refine ⟨64297733551586064472439017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 342921245608459010519674757 64297733551586064472439017)
      ·
        refine ⟨48223300163689548354329263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 64297733551586064472439017 48223300163689548354329263)
        ·
          refine ⟨72334950245534322531493895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48223300163689548354329263 72334950245534322531493895)
          ·
            refine ⟨108502425368301483797240843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 72334950245534322531493895 108502425368301483797240843)
            ·
              refine ⟨162753638052452225695861265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 108502425368301483797240843 162753638052452225695861265)
              ·
                refine ⟨122065228539339169271895949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 162753638052452225695861265 122065228539339169271895949)
                ·
                  refine ⟨45774460702252188476960981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 122065228539339169271895949 45774460702252188476960981)
                  ·
                    refine ⟨1072838922709035667428773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 45774460702252188476960981 1072838922709035667428773)
                    ·
                      rfl

theorem cell23_6268039_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 1, 2, 3, 7].length) (baseStart_6268039 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6268039 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6268039 prefixEnd_6268039 := by exact prefixLift 6268039
  have htrace : WordTrace (prefixWord ++ tailWord_6268039) baseStart_6268039 baseEnd_6268039 := by
    simpa [prefixWord, tailWord_6268039, baseEnd_6268039] using wordTrace_append hprefix tailTrace_6268039
  have hstable : (prefixWord ++ tailWord_6268039).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6268039).length < 2 ^ (prefixWord ++ tailWord_6268039).sum := by decide
  have hdescent : baseEnd_6268039 < baseStart_6268039 := by decide
  rcases family_descends (prefixWord ++ tailWord_6268039) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6268076 : List Nat := [2, 2, 1, 1, 1, 1, 1, 7, 2, 1, 4]
def baseStart_6268076 : Nat := 118140960795 + 6268076 * 2 ^ 59
def prefixEnd_6268076 : Nat := 4983230072969 + 3 ^ 40 * 6268076 * 2
def baseEnd_6268076 : Nat := 3218535766911323357523649

theorem tailTrace_6268076 : CollatzResearch.WordTrace tailWord_6268076 prefixEnd_6268076 3218535766911323357523649 := by
  unfold tailWord_6268076
  simp only [CollatzResearch.WordTrace]
  refine ⟨114307756619919314499440041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 152410342159892419332586721 114307756619919314499440041)
  ·
    refine ⟨85730817464939485874580031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 114307756619919314499440041 85730817464939485874580031)
    ·
      refine ⟨128596226197409228811870047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85730817464939485874580031 128596226197409228811870047)
      ·
        refine ⟨192894339296113843217805071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 128596226197409228811870047 192894339296113843217805071)
        ·
          refine ⟨289341508944170764826707607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 192894339296113843217805071 289341508944170764826707607)
          ·
            refine ⟨434012263416256147240061411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 289341508944170764826707607 434012263416256147240061411)
            ·
              refine ⟨651018395124384220860092117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 434012263416256147240061411 651018395124384220860092117)
              ·
                refine ⟨15258243635727755176408409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 651018395124384220860092117 15258243635727755176408409)
                ·
                  refine ⟨11443682726795816382306307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15258243635727755176408409 11443682726795816382306307)
                  ·
                    refine ⟨17165524090193724573459461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11443682726795816382306307 17165524090193724573459461)
                    ·
                      refine ⟨3218535766911323357523649, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17165524090193724573459461 3218535766911323357523649)
                      ·
                        rfl

theorem cell23_6268076_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 2, 1, 4].length) (baseStart_6268076 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6268076 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6268076 prefixEnd_6268076 := by exact prefixLift 6268076
  have htrace : WordTrace (prefixWord ++ tailWord_6268076) baseStart_6268076 baseEnd_6268076 := by
    simpa [prefixWord, tailWord_6268076, baseEnd_6268076] using wordTrace_append hprefix tailTrace_6268076
  have hstable : (prefixWord ++ tailWord_6268076).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6268076).length < 2 ^ (prefixWord ++ tailWord_6268076).sum := by decide
  have hdescent : baseEnd_6268076 < baseStart_6268076 := by decide
  rcases family_descends (prefixWord ++ tailWord_6268076) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6268093 : List Nat := [1, 4, 1, 2, 1, 1, 3, 2, 2, 4, 2]
def baseStart_6268093 : Nat := 118140960795 + 6268093 * 2 ^ 59
def prefixEnd_6268093 : Nat := 4983230072969 + 3 ^ 40 * 6268093 * 2
def baseEnd_6268093 : Nat := 3218544496082449791011071

theorem tailTrace_6268093 : CollatzResearch.WordTrace tailWord_6268093 prefixEnd_6268093 3218544496082449791011071 := by
  unfold tailWord_6268093
  simp only [CollatzResearch.WordTrace]
  refine ⟨228616133280777040902248933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152410755520518027268165955 228616133280777040902248933)
  ·
    refine ⟨42865524990145695169171675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 228616133280777040902248933 42865524990145695169171675)
    ·
      refine ⟨64298287485218542753757513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42865524990145695169171675 64298287485218542753757513)
      ·
        refine ⟨48223715613913907065318135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 64298287485218542753757513 48223715613913907065318135)
        ·
          refine ⟨72335573420870860597977203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48223715613913907065318135 72335573420870860597977203)
          ·
            refine ⟨108503360131306290896965805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 72335573420870860597977203 108503360131306290896965805)
            ·
              refine ⟨40688760049239859086362177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 108503360131306290896965805 40688760049239859086362177)
              ·
                refine ⟨30516570036929894314771633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 40688760049239859086362177 30516570036929894314771633)
                ·
                  refine ⟨22887427527697420736078725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 30516570036929894314771633 22887427527697420736078725)
                  ·
                    refine ⟨4291392661443266388014761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 22887427527697420736078725 4291392661443266388014761)
                    ·
                      refine ⟨3218544496082449791011071, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4291392661443266388014761 3218544496082449791011071)
                      ·
                        rfl

theorem cell23_6268093_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 3, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 3, 2, 2, 4, 2].length) (baseStart_6268093 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6268093 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6268093 prefixEnd_6268093 := by exact prefixLift 6268093
  have htrace : WordTrace (prefixWord ++ tailWord_6268093) baseStart_6268093 baseEnd_6268093 := by
    simpa [prefixWord, tailWord_6268093, baseEnd_6268093] using wordTrace_append hprefix tailTrace_6268093
  have hstable : (prefixWord ++ tailWord_6268093).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6268093).length < 2 ^ (prefixWord ++ tailWord_6268093).sum := by decide
  have hdescent : baseEnd_6268093 < baseStart_6268093 := by decide
  rcases family_descends (prefixWord ++ tailWord_6268093) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6268183 : List Nat := [1, 1, 3, 4, 1, 1, 3, 1, 3, 1, 4]
def baseStart_6268183 : Nat := 118140960795 + 6268183 * 2 ^ 59
def prefixEnd_6268183 : Nat := 4983230072969 + 3 ^ 40 * 6268183 * 2
def baseEnd_6268183 : Nat := 3218590709341354438885657

theorem tailTrace_6268183 : CollatzResearch.WordTrace tailWord_6268183 prefixEnd_6268183 3218590709341354438885657 := by
  unfold tailWord_6268183
  simp only [CollatzResearch.WordTrace]
  refine ⟨228619415850450986273025203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152412943900300657515350135 228619415850450986273025203)
  ·
    refine ⟨342929123775676479409537805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 228619415850450986273025203 342929123775676479409537805)
    ·
      refine ⟨128598421415878679778576677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 342929123775676479409537805 128598421415878679778576677)
      ·
        refine ⟨24112204015477252458483127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 128598421415878679778576677 24112204015477252458483127)
        ·
          refine ⟨36168306023215878687724691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24112204015477252458483127 36168306023215878687724691)
          ·
            refine ⟨54252459034823818031587037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36168306023215878687724691 54252459034823818031587037)
            ·
              refine ⟨20344672138058931761845139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 54252459034823818031587037 20344672138058931761845139)
              ·
                refine ⟨30517008207088397642767709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20344672138058931761845139 30517008207088397642767709)
                ·
                  refine ⟨11443878077658149116037891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 30517008207088397642767709 11443878077658149116037891)
                  ·
                    refine ⟨17165817116487223674056837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11443878077658149116037891 17165817116487223674056837)
                    ·
                      refine ⟨3218590709341354438885657, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17165817116487223674056837 3218590709341354438885657)
                      ·
                        rfl

theorem cell23_6268183_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 3, 1, 3, 1, 4].length) (baseStart_6268183 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6268183 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6268183 prefixEnd_6268183 := by exact prefixLift 6268183
  have htrace : WordTrace (prefixWord ++ tailWord_6268183) baseStart_6268183 baseEnd_6268183 := by
    simpa [prefixWord, tailWord_6268183, baseEnd_6268183] using wordTrace_append hprefix tailTrace_6268183
  have hstable : (prefixWord ++ tailWord_6268183).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6268183).length < 2 ^ (prefixWord ++ tailWord_6268183).sum := by decide
  have hdescent : baseEnd_6268183 < baseStart_6268183 := by decide
  rcases family_descends (prefixWord ++ tailWord_6268183) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6268206 : List Nat := [4, 1, 3, 15]
def baseStart_6268206 : Nat := 118140960795 + 6268206 * 2 ^ 59
def prefixEnd_6268206 : Nat := 4983230072969 + 3 ^ 40 * 6268206 * 2
def baseEnd_6268206 : Nat := 1471697539733154023273

theorem tailTrace_6268206 : CollatzResearch.WordTrace tailWord_6268206 prefixEnd_6268206 1471697539733154023273 := by
  unfold tailWord_6268206
  simp only [CollatzResearch.WordTrace]
  refine ⟨28577531841170957650139059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 152413503152911774134074981 28577531841170957650139059)
  ·
    refine ⟨42866297761756436475208589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28577531841170957650139059 42866297761756436475208589)
    ·
      refine ⟨16074861660658663678203221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 42866297761756436475208589 16074861660658663678203221)
      ·
        refine ⟨1471697539733154023273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 15 16074861660658663678203221 1471697539733154023273)
        ·
          rfl

theorem cell23_6268206_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 15].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 15].length) (baseStart_6268206 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6268206 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6268206 prefixEnd_6268206 := by exact prefixLift 6268206
  have htrace : WordTrace (prefixWord ++ tailWord_6268206) baseStart_6268206 baseEnd_6268206 := by
    simpa [prefixWord, tailWord_6268206, baseEnd_6268206] using wordTrace_append hprefix tailTrace_6268206
  have hstable : (prefixWord ++ tailWord_6268206).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6268206).length < 2 ^ (prefixWord ++ tailWord_6268206).sum := by decide
  have hdescent : baseEnd_6268206 < baseStart_6268206 := by decide
  rcases family_descends (prefixWord ++ tailWord_6268206) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6268210 : List Nat := [3, 2, 1, 1, 4, 1, 1, 4, 2, 4]
def baseStart_6268210 : Nat := 118140960795 + 6268210 * 2 ^ 59
def prefixEnd_6268210 : Nat := 4983230072969 + 3 ^ 40 * 6268210 * 2
def baseEnd_6268210 : Nat := 1072868191106341944416011

theorem tailTrace_6268210 : CollatzResearch.WordTrace tailWord_6268210 prefixEnd_6268210 1072868191106341944416011 := by
  unfold tailWord_6268210
  simp only [CollatzResearch.WordTrace]
  refine ⟨57155100155338292471064521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 152413600414235446589505389 57155100155338292471064521)
  ·
    refine ⟨42866325116503719353298391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57155100155338292471064521 42866325116503719353298391)
    ·
      refine ⟨64299487674755579029947587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42866325116503719353298391 64299487674755579029947587)
      ·
        refine ⟨96449231512133368544921381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64299487674755579029947587 96449231512133368544921381)
        ·
          refine ⟨18084230908525006602172759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 96449231512133368544921381 18084230908525006602172759)
          ·
            refine ⟨27126346362787509903259139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18084230908525006602172759 27126346362787509903259139)
            ·
              refine ⟨40689519544181264854888709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27126346362787509903259139 40689519544181264854888709)
              ·
                refine ⟨7629284914533987160291633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 40689519544181264854888709 7629284914533987160291633)
                ·
                  refine ⟨5721963685900490370218725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7629284914533987160291633 5721963685900490370218725)
                  ·
                    refine ⟨1072868191106341944416011, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5721963685900490370218725 1072868191106341944416011)
                    ·
                      rfl

theorem cell23_6268210_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 1, 1, 4, 2, 4].length) (baseStart_6268210 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6268210 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6268210 prefixEnd_6268210 := by exact prefixLift 6268210
  have htrace : WordTrace (prefixWord ++ tailWord_6268210) baseStart_6268210 baseEnd_6268210 := by
    simpa [prefixWord, tailWord_6268210, baseEnd_6268210] using wordTrace_append hprefix tailTrace_6268210
  have hstable : (prefixWord ++ tailWord_6268210).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6268210).length < 2 ^ (prefixWord ++ tailWord_6268210).sum := by decide
  have hdescent : baseEnd_6268210 < baseStart_6268210 := by decide
  rcases family_descends (prefixWord ++ tailWord_6268210) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6268223 : List Nat := [1, 1, 2, 2, 4, 4, 1, 8]
def baseStart_6268223 : Nat := 118140960795 + 6268223 * 2 ^ 59
def prefixEnd_6268223 : Nat := 4983230072969 + 3 ^ 40 * 6268223 * 2
def baseEnd_6268223 : Nat := 119207824021019788236499

theorem tailTrace_6268223 : CollatzResearch.WordTrace tailWord_6268223 prefixEnd_6268223 119207824021019788236499 := by
  unfold tailWord_6268223
  simp only [CollatzResearch.WordTrace]
  refine ⟨228620874770306073104481323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152413916513537382069654215 228620874770306073104481323)
  ·
    refine ⟨342931312155459109656721985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 228620874770306073104481323 342931312155459109656721985)
    ·
      refine ⟨257198484116594332242541489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 342931312155459109656721985 257198484116594332242541489)
      ·
        refine ⟨192898863087445749181906117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 257198484116594332242541489 192898863087445749181906117)
        ·
          refine ⟨36168536828896077971607397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 192898863087445749181906117 36168536828896077971607397)
          ·
            refine ⟨6781600655418014619676387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 36168536828896077971607397 6781600655418014619676387)
            ·
              refine ⟨10172400983127021929514581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6781600655418014619676387 10172400983127021929514581)
              ·
                refine ⟨119207824021019788236499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 10172400983127021929514581 119207824021019788236499)
                ·
                  rfl

theorem cell23_6268223_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 4, 1, 8].length) (baseStart_6268223 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6268223 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6268223 prefixEnd_6268223 := by exact prefixLift 6268223
  have htrace : WordTrace (prefixWord ++ tailWord_6268223) baseStart_6268223 baseEnd_6268223 := by
    simpa [prefixWord, tailWord_6268223, baseEnd_6268223] using wordTrace_append hprefix tailTrace_6268223
  have hstable : (prefixWord ++ tailWord_6268223).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6268223).length < 2 ^ (prefixWord ++ tailWord_6268223).sum := by decide
  have hdescent : baseEnd_6268223 < baseStart_6268223 := by decide
  rcases family_descends (prefixWord ++ tailWord_6268223) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6268233 : List Nat := [1, 2, 1, 1, 2, 3, 3, 3, 1, 3, 3]
def baseStart_6268233 : Nat := 118140960795 + 6268233 * 2 ^ 59
def prefixEnd_6268233 : Nat := 4983230072969 + 3 ^ 40 * 6268233 * 2
def baseEnd_6268233 : Nat := 3218616383374079243260427

theorem tailTrace_6268233 : CollatzResearch.WordTrace tailWord_6268233 prefixEnd_6268233 3218616383374079243260427 := by
  unfold tailWord_6268233
  simp only [CollatzResearch.WordTrace]
  refine ⟨228621239500269844812345353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152414159666846563208230235 228621239500269844812345353)
  ·
    refine ⟨171465929625202383609259015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 228621239500269844812345353 171465929625202383609259015)
    ·
      refine ⟨257198894437803575413888523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 171465929625202383609259015 257198894437803575413888523)
      ·
        refine ⟨385798341656705363120832785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 257198894437803575413888523 385798341656705363120832785)
        ·
          refine ⟨289348756242529022340624589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 385798341656705363120832785 289348756242529022340624589)
          ·
            refine ⟨108505783590948383377734221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 289348756242529022340624589 108505783590948383377734221)
            ·
              refine ⟨40689668846605643766650333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 108505783590948383377734221 40689668846605643766650333)
              ·
                refine ⟨15258625817477116412493875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 40689668846605643766650333 15258625817477116412493875)
                ·
                  refine ⟨22887938726215674618740813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15258625817477116412493875 22887938726215674618740813)
                  ·
                    refine ⟨8582977022330877982027805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 22887938726215674618740813 8582977022330877982027805)
                    ·
                      refine ⟨3218616383374079243260427, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8582977022330877982027805 3218616383374079243260427)
                      ·
                        rfl

theorem cell23_6268233_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 3, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 3, 3, 1, 3, 3].length) (baseStart_6268233 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6268233 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6268233 prefixEnd_6268233 := by exact prefixLift 6268233
  have htrace : WordTrace (prefixWord ++ tailWord_6268233) baseStart_6268233 baseEnd_6268233 := by
    simpa [prefixWord, tailWord_6268233, baseEnd_6268233] using wordTrace_append hprefix tailTrace_6268233
  have hstable : (prefixWord ++ tailWord_6268233).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6268233).length < 2 ^ (prefixWord ++ tailWord_6268233).sum := by decide
  have hdescent : baseEnd_6268233 < baseStart_6268233 := by decide
  rcases family_descends (prefixWord ++ tailWord_6268233) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6268293 : List Nat := [1, 3, 1, 1, 3, 1, 2, 2, 2, 4, 3]
def baseStart_6268293 : Nat := 118140960795 + 6268293 * 2 ^ 59
def prefixEnd_6268293 : Nat := 4983230072969 + 3 ^ 40 * 6268293 * 2
def baseEnd_6268293 : Nat := 3218647192213349008510151

theorem tailTrace_6268293 : CollatzResearch.WordTrace tailWord_6268293 prefixEnd_6268293 3218647192213349008510151 := by
  unfold tailWord_6268293
  simp only [CollatzResearch.WordTrace]
  refine ⟨228623427880052475059529533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152415618586701650039686355 228623427880052475059529533)
  ·
    refine ⟨85733785455019678147323575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 228623427880052475059529533 85733785455019678147323575)
    ·
      refine ⟨128600678182529517220985363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85733785455019678147323575 128600678182529517220985363)
      ·
        refine ⟨192901017273794275831478045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 128600678182529517220985363 192901017273794275831478045)
        ·
          refine ⟨72337881477672853436804267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 192901017273794275831478045 72337881477672853436804267)
          ·
            refine ⟨108506822216509280155206401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 72337881477672853436804267 108506822216509280155206401)
            ·
              refine ⟨81380116662381960116404801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 108506822216509280155206401 81380116662381960116404801)
              ·
                refine ⟨61035087496786470087303601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 81380116662381960116404801 61035087496786470087303601)
                ·
                  refine ⟨45776315622589852565477701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 61035087496786470087303601 45776315622589852565477701)
                  ·
                    refine ⟨8583059179235597356027069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 45776315622589852565477701 8583059179235597356027069)
                    ·
                      refine ⟨3218647192213349008510151, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8583059179235597356027069 3218647192213349008510151)
                      ·
                        rfl

theorem cell23_6268293_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 2, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 2, 2, 2, 4, 3].length) (baseStart_6268293 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6268293 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6268293 prefixEnd_6268293 := by exact prefixLift 6268293
  have htrace : WordTrace (prefixWord ++ tailWord_6268293) baseStart_6268293 baseEnd_6268293 := by
    simpa [prefixWord, tailWord_6268293, baseEnd_6268293] using wordTrace_append hprefix tailTrace_6268293
  have hstable : (prefixWord ++ tailWord_6268293).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6268293).length < 2 ^ (prefixWord ++ tailWord_6268293).sum := by decide
  have hdescent : baseEnd_6268293 < baseStart_6268293 := by decide
  rcases family_descends (prefixWord ++ tailWord_6268293) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6268341 : List Nat := [1, 3, 3, 2, 2, 1, 4, 1, 2, 2, 2]
def baseStart_6268341 : Nat := 118140960795 + 6268341 * 2 ^ 59
def prefixEnd_6268341 : Nat := 4983230072969 + 3 ^ 40 * 6268341 * 2
def baseEnd_6268341 : Nat := 3218671839284764820709931

theorem tailTrace_6268341 : CollatzResearch.WordTrace tailWord_6268341 prefixEnd_6268341 3218671839284764820709931 := by
  unfold tailWord_6268341
  simp only [CollatzResearch.WordTrace]
  refine ⟨228625178583878579257276877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152416785722585719504851251 228625178583878579257276877)
  ·
    refine ⟨85734441968954467221478829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 228625178583878579257276877 85734441968954467221478829)
    ·
      refine ⟨32150415738357925208054561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 85734441968954467221478829 32150415738357925208054561)
      ·
        refine ⟨24112811803768443906040921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32150415738357925208054561 24112811803768443906040921)
        ·
          refine ⟨18084608852826332929530691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24112811803768443906040921 18084608852826332929530691)
          ·
            refine ⟨27126913279239499394296037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18084608852826332929530691 27126913279239499394296037)
            ·
              refine ⟨5086296239857406136430507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 27126913279239499394296037 5086296239857406136430507)
              ·
                refine ⟨7629444359786109204645761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5086296239857406136430507 7629444359786109204645761)
                ·
                  refine ⟨5722083269839581903484321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7629444359786109204645761 5722083269839581903484321)
                  ·
                    refine ⟨4291562452379686427613241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5722083269839581903484321 4291562452379686427613241)
                    ·
                      refine ⟨3218671839284764820709931, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4291562452379686427613241 3218671839284764820709931)
                      ·
                        rfl

theorem cell23_6268341_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 1, 4, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 1, 4, 1, 2, 2, 2].length) (baseStart_6268341 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6268341 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6268341 prefixEnd_6268341 := by exact prefixLift 6268341
  have htrace : WordTrace (prefixWord ++ tailWord_6268341) baseStart_6268341 baseEnd_6268341 := by
    simpa [prefixWord, tailWord_6268341, baseEnd_6268341] using wordTrace_append hprefix tailTrace_6268341
  have hstable : (prefixWord ++ tailWord_6268341).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6268341).length < 2 ^ (prefixWord ++ tailWord_6268341).sum := by decide
  have hdescent : baseEnd_6268341 < baseStart_6268341 := by decide
  rcases family_descends (prefixWord ++ tailWord_6268341) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6268343 : List Nat := [1, 1, 3, 1, 3, 2, 1, 2, 4, 5]
def baseStart_6268343 : Nat := 118140960795 + 6268343 * 2 ^ 59
def prefixEnd_6268343 : Nat := 4983230072969 + 3 ^ 40 * 6268343 * 2
def baseEnd_6268343 : Nat := 1072890955415357937628307

theorem tailTrace_6268343 : CollatzResearch.WordTrace tailWord_6268343 prefixEnd_6268343 1072890955415357937628307 := by
  unfold tailWord_6268343
  simp only [CollatzResearch.WordTrace]
  refine ⟨228625251529871333598849683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152416834353247555732566455 228625251529871333598849683)
  ·
    refine ⟨342937877294807000398274525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 228625251529871333598849683 342937877294807000398274525)
    ·
      refine ⟨128601703985552625149352947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 342937877294807000398274525 128601703985552625149352947)
      ·
        refine ⟨192902555978328937724029421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 128601703985552625149352947 192902555978328937724029421)
        ·
          refine ⟨72338458491873351646511033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 192902555978328937724029421 72338458491873351646511033)
          ·
            refine ⟨54253843868905013734883275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 72338458491873351646511033 54253843868905013734883275)
            ·
              refine ⟨81380765803357520602324913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 54253843868905013734883275 81380765803357520602324913)
              ·
                refine ⟨61035574352518140451743685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 81380765803357520602324913 61035574352518140451743685)
                ·
                  refine ⟨11444170191097151334701941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 61035574352518140451743685 11444170191097151334701941)
                  ·
                    refine ⟨1072890955415357937628307, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11444170191097151334701941 1072890955415357937628307)
                    ·
                      rfl

theorem cell23_6268343_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 1, 2, 4, 5].length) (baseStart_6268343 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6268343 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6268343 prefixEnd_6268343 := by exact prefixLift 6268343
  have htrace : WordTrace (prefixWord ++ tailWord_6268343) baseStart_6268343 baseEnd_6268343 := by
    simpa [prefixWord, tailWord_6268343, baseEnd_6268343] using wordTrace_append hprefix tailTrace_6268343
  have hstable : (prefixWord ++ tailWord_6268343).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6268343).length < 2 ^ (prefixWord ++ tailWord_6268343).sum := by decide
  have hdescent : baseEnd_6268343 < baseStart_6268343 := by decide
  rcases family_descends (prefixWord ++ tailWord_6268343) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6268360 : List Nat := [2, 1, 3, 1, 3, 1, 4, 1, 2, 5]
def baseStart_6268360 : Nat := 118140960795 + 6268360 * 2 ^ 59
def prefixEnd_6268360 : Nat := 4983230072969 + 3 ^ 40 * 6268360 * 2
def baseEnd_6268360 : Nat := 1072893865139066748790781

theorem tailTrace_6268360 : CollatzResearch.WordTrace tailWord_6268360 prefixEnd_6268360 1072893865139066748790781 := by
  unfold tailWord_6268360
  simp only [CollatzResearch.WordTrace]
  refine ⟨114312935785404872751109267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 152417247713873163668145689 114312935785404872751109267)
  ·
    refine ⟨171469403678107309126663901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114312935785404872751109267 171469403678107309126663901)
    ·
      refine ⟨64301026379290240922498963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 171469403678107309126663901 64301026379290240922498963)
      ·
        refine ⟨96451539568935361383748445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64301026379290240922498963 96451539568935361383748445)
        ·
          refine ⟨36169327338350760518905667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 96451539568935361383748445 36169327338350760518905667)
          ·
            refine ⟨54253991007526140778358501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36169327338350760518905667 54253991007526140778358501)
            ·
              refine ⟨10172623313911151395942219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 54253991007526140778358501 10172623313911151395942219)
              ·
                refine ⟨15258934970866727093913329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10172623313911151395942219 15258934970866727093913329)
                ·
                  refine ⟨11444201228150045320434997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15258934970866727093913329 11444201228150045320434997)
                  ·
                    refine ⟨1072893865139066748790781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11444201228150045320434997 1072893865139066748790781)
                    ·
                      rfl

theorem cell23_6268360_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 4, 1, 2, 5].length) (baseStart_6268360 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6268360 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6268360 prefixEnd_6268360 := by exact prefixLift 6268360
  have htrace : WordTrace (prefixWord ++ tailWord_6268360) baseStart_6268360 baseEnd_6268360 := by
    simpa [prefixWord, tailWord_6268360, baseEnd_6268360] using wordTrace_append hprefix tailTrace_6268360
  have hstable : (prefixWord ++ tailWord_6268360).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6268360).length < 2 ^ (prefixWord ++ tailWord_6268360).sum := by decide
  have hdescent : baseEnd_6268360 < baseStart_6268360 := by decide
  rcases family_descends (prefixWord ++ tailWord_6268360) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6268363 : List Nat := [1, 1, 1, 1, 3, 3, 2, 3, 1, 3, 4]
def baseStart_6268363 : Nat := 118140960795 + 6268363 * 2 ^ 59
def prefixEnd_6268363 : Nat := 4983230072969 + 3 ^ 40 * 6268363 * 2
def baseEnd_6268363 : Nat := 3218683135859163734634829

theorem tailTrace_6268363 : CollatzResearch.WordTrace tailWord_6268363 prefixEnd_6268363 3218683135859163734634829 := by
  unfold tailWord_6268363
  simp only [CollatzResearch.WordTrace]
  refine ⟨228625980989798877014577743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152417320659865918009718495 228625980989798877014577743)
  ·
    refine ⟨342938971484698315521866615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 228625980989798877014577743 342938971484698315521866615)
    ·
      refine ⟨514408457227047473282799923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 342938971484698315521866615 514408457227047473282799923)
      ·
        refine ⟨771612685840571209924199885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 514408457227047473282799923 771612685840571209924199885)
        ·
          refine ⟨289354757190214203721574957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 771612685840571209924199885 289354757190214203721574957)
          ·
            refine ⟨108508033946330326395590609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 289354757190214203721574957 108508033946330326395590609)
            ·
              refine ⟨81381025459747744796692957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 108508033946330326395590609 81381025459747744796692957)
              ·
                refine ⟨30517884547405404298759859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 81381025459747744796692957 30517884547405404298759859)
                ·
                  refine ⟨45776826821108106448139789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30517884547405404298759859 45776826821108106448139789)
                  ·
                    refine ⟨17166310057915539918052421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 45776826821108106448139789 17166310057915539918052421)
                    ·
                      refine ⟨3218683135859163734634829, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17166310057915539918052421 3218683135859163734634829)
                      ·
                        rfl

theorem cell23_6268363_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 2, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 2, 3, 1, 3, 4].length) (baseStart_6268363 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6268363 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6268363 prefixEnd_6268363 := by exact prefixLift 6268363
  have htrace : WordTrace (prefixWord ++ tailWord_6268363) baseStart_6268363 baseEnd_6268363 := by
    simpa [prefixWord, tailWord_6268363, baseEnd_6268363] using wordTrace_append hprefix tailTrace_6268363
  have hstable : (prefixWord ++ tailWord_6268363).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6268363).length < 2 ^ (prefixWord ++ tailWord_6268363).sum := by decide
  have hdescent : baseEnd_6268363 < baseStart_6268363 := by decide
  rcases family_descends (prefixWord ++ tailWord_6268363) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6268383 : List Nat := [1, 1, 2, 3, 3, 1, 1, 1, 2, 3, 5]
def baseStart_6268383 : Nat := 118140960795 + 6268383 * 2 ^ 59
def prefixEnd_6268383 : Nat := 4983230072969 + 3 ^ 40 * 6268383 * 2
def baseEnd_6268383 : Nat := 3218693405472253656384737

theorem tailTrace_6268383 : CollatzResearch.WordTrace tailWord_6268383 prefixEnd_6268383 3218693405472253656384737 := by
  unfold tailWord_6268383
  simp only [CollatzResearch.WordTrace]
  refine ⟨228626710449726420430305803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152417806966484280286870535 228626710449726420430305803)
  ·
    refine ⟨342940065674589630645458705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 228626710449726420430305803 342940065674589630645458705)
    ·
      refine ⟨257205049255942222984094029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 342940065674589630645458705 257205049255942222984094029)
      ·
        refine ⟨96451893470978333619035261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 257205049255942222984094029 96451893470978333619035261)
        ·
          refine ⟨36169460051616875107138223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 96451893470978333619035261 36169460051616875107138223)
          ·
            refine ⟨54254190077425312660707335, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36169460051616875107138223 54254190077425312660707335)
            ·
              refine ⟨81381285116137968991061003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 54254190077425312660707335 81381285116137968991061003)
              ·
                refine ⟨122071927674206953486591505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 81381285116137968991061003 122071927674206953486591505)
                ·
                  refine ⟨91553945755655215114943629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 122071927674206953486591505 91553945755655215114943629)
                  ·
                    refine ⟨34332729658370705668103861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 91553945755655215114943629 34332729658370705668103861)
                    ·
                      refine ⟨3218693405472253656384737, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 34332729658370705668103861 3218693405472253656384737)
                      ·
                        rfl

theorem cell23_6268383_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 1, 1, 2, 3, 5].length) (baseStart_6268383 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6268383 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6268383 prefixEnd_6268383 := by exact prefixLift 6268383
  have htrace : WordTrace (prefixWord ++ tailWord_6268383) baseStart_6268383 baseEnd_6268383 := by
    simpa [prefixWord, tailWord_6268383, baseEnd_6268383] using wordTrace_append hprefix tailTrace_6268383
  have hstable : (prefixWord ++ tailWord_6268383).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6268383).length < 2 ^ (prefixWord ++ tailWord_6268383).sum := by decide
  have hdescent : baseEnd_6268383 < baseStart_6268383 := by decide
  rcases family_descends (prefixWord ++ tailWord_6268383) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6268414 : List Nat := [4, 2, 2, 3, 1, 1, 1, 1, 1, 3, 4]
def baseStart_6268414 : Nat := 118140960795 + 6268414 * 2 ^ 59
def prefixEnd_6268414 : Nat := 4983230072969 + 3 ^ 40 * 6268414 * 2
def baseEnd_6268414 : Nat := 3218709323372543035097095

theorem tailTrace_6268414 : CollatzResearch.WordTrace tailWord_6268414 prefixEnd_6268414 3218709323372543035097095 := by
  unfold tailWord_6268414
  simp only [CollatzResearch.WordTrace]
  refine ⟨28578480139076764090585537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 152418560741742741816456197 28578480139076764090585537)
  ·
    refine ⟨21433860104307573067939153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28578480139076764090585537 21433860104307573067939153)
    ·
      refine ⟨16075395078230679800954365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21433860104307573067939153 16075395078230679800954365)
      ·
        refine ⟨6028273154336504925357887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16075395078230679800954365 6028273154336504925357887)
        ·
          refine ⟨9042409731504757388036831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6028273154336504925357887 9042409731504757388036831)
          ·
            refine ⟨13563614597257136082055247, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9042409731504757388036831 13563614597257136082055247)
            ·
              refine ⟨20345421895885704123082871, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13563614597257136082055247 20345421895885704123082871)
              ·
                refine ⟨30518132843828556184624307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20345421895885704123082871 30518132843828556184624307)
                ·
                  refine ⟨45777199265742834276936461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30518132843828556184624307 45777199265742834276936461)
                  ·
                    refine ⟨17166449724653562853851173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 45777199265742834276936461 17166449724653562853851173)
                    ·
                      refine ⟨3218709323372543035097095, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17166449724653562853851173 3218709323372543035097095)
                      ·
                        rfl

theorem cell23_6268414_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 3, 1, 1, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 3, 1, 1, 1, 1, 1, 3, 4].length) (baseStart_6268414 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6268414 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6268414 prefixEnd_6268414 := by exact prefixLift 6268414
  have htrace : WordTrace (prefixWord ++ tailWord_6268414) baseStart_6268414 baseEnd_6268414 := by
    simpa [prefixWord, tailWord_6268414, baseEnd_6268414] using wordTrace_append hprefix tailTrace_6268414
  have hstable : (prefixWord ++ tailWord_6268414).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6268414).length < 2 ^ (prefixWord ++ tailWord_6268414).sum := by decide
  have hdescent : baseEnd_6268414 < baseStart_6268414 := by decide
  rcases family_descends (prefixWord ++ tailWord_6268414) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6268417 : List Nat := [1, 2, 4, 1, 4, 1, 1, 1, 1, 4, 3]
def baseStart_6268417 : Nat := 118140960795 + 6268417 * 2 ^ 59
def prefixEnd_6268417 : Nat := 4983230072969 + 3 ^ 40 * 6268417 * 2
def baseEnd_6268417 : Nat := 3218710863814506523359581

theorem tailTrace_6268417 : CollatzResearch.WordTrace tailWord_6268417 prefixEnd_6268417 3218710863814506523359581 := by
  unfold tailWord_6268417
  simp only [CollatzResearch.WordTrace]
  refine ⟨228627950531603244237043505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152418633687735496158029003 228627950531603244237043505)
  ·
    refine ⟨171470962898702433177782629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 228627950531603244237043505 171470962898702433177782629)
    ·
      refine ⟨32150805543506706220834243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 171470962898702433177782629 32150805543506706220834243)
      ·
        refine ⟨48226208315260059331251365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32150805543506706220834243 48226208315260059331251365)
        ·
          refine ⟨9042414059111261124609631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 48226208315260059331251365 9042414059111261124609631)
          ·
            refine ⟨13563621088666891686914447, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9042414059111261124609631 13563621088666891686914447)
            ·
              refine ⟨20345431633000337530371671, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13563621088666891686914447 20345431633000337530371671)
              ·
                refine ⟨30518147449500506295557507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20345431633000337530371671 30518147449500506295557507)
                ·
                  refine ⟨45777221174250759443336261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30518147449500506295557507 45777221174250759443336261)
                  ·
                    refine ⟨8583228970172017395625549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 45777221174250759443336261 8583228970172017395625549)
                    ·
                      refine ⟨3218710863814506523359581, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8583228970172017395625549 3218710863814506523359581)
                      ·
                        rfl

theorem cell23_6268417_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 4, 1, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 4, 1, 1, 1, 1, 4, 3].length) (baseStart_6268417 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6268417 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6268417 prefixEnd_6268417 := by exact prefixLift 6268417
  have htrace : WordTrace (prefixWord ++ tailWord_6268417) baseStart_6268417 baseEnd_6268417 := by
    simpa [prefixWord, tailWord_6268417, baseEnd_6268417] using wordTrace_append hprefix tailTrace_6268417
  have hstable : (prefixWord ++ tailWord_6268417).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6268417).length < 2 ^ (prefixWord ++ tailWord_6268417).sum := by decide
  have hdescent : baseEnd_6268417 < baseStart_6268417 := by decide
  rcases family_descends (prefixWord ++ tailWord_6268417) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6268437 : List Nat := [1, 3, 2, 1, 3, 4, 1, 2, 6]
def baseStart_6268437 : Nat := 118140960795 + 6268437 * 2 ^ 59
def prefixEnd_6268437 : Nat := 4983230072969 + 3 ^ 40 * 6268437 * 2
def baseEnd_6268437 : Nat := 357635681491955160567721

theorem tailTrace_6268437 : CollatzResearch.WordTrace tailWord_6268437 prefixEnd_6268437 357635681491955160567721 := by
  unfold tailWord_6268437
  simp only [CollatzResearch.WordTrace]
  refine ⟨228628679991530787652771565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152419119994353858435181043 228628679991530787652771565)
  ·
    refine ⟨85735754996824045369789337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 228628679991530787652771565 85735754996824045369789337)
    ·
      refine ⟨64301816247618034027342003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 85735754996824045369789337 64301816247618034027342003)
      ·
        refine ⟨96452724371427051041013005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64301816247618034027342003 96452724371427051041013005)
        ·
          refine ⟨36169771639285144140379877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 96452724371427051041013005 36169771639285144140379877)
          ·
            refine ⟨6781832182365964526321227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 36169771639285144140379877 6781832182365964526321227)
            ·
              refine ⟨10172748273548946789481841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6781832182365964526321227 10172748273548946789481841)
              ·
                refine ⟨7629561205161710092111381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10172748273548946789481841 7629561205161710092111381)
                ·
                  refine ⟨357635681491955160567721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7629561205161710092111381 357635681491955160567721)
                  ·
                    rfl

theorem cell23_6268437_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 4, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 4, 1, 2, 6].length) (baseStart_6268437 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6268437 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6268437 prefixEnd_6268437 := by exact prefixLift 6268437
  have htrace : WordTrace (prefixWord ++ tailWord_6268437) baseStart_6268437 baseEnd_6268437 := by
    simpa [prefixWord, tailWord_6268437, baseEnd_6268437] using wordTrace_append hprefix tailTrace_6268437
  have hstable : (prefixWord ++ tailWord_6268437).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6268437).length < 2 ^ (prefixWord ++ tailWord_6268437).sum := by decide
  have hdescent : baseEnd_6268437 < baseStart_6268437 := by decide
  rcases family_descends (prefixWord ++ tailWord_6268437) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6268447 : List Nat := [1, 1, 2, 4, 1, 1, 3, 3, 3, 1, 3]
def baseStart_6268447 : Nat := 118140960795 + 6268447 * 2 ^ 59
def prefixEnd_6268447 : Nat := 4983230072969 + 3 ^ 40 * 6268447 * 2
def baseEnd_6268447 : Nat := 3218726268234141405984443

theorem tailTrace_6268447 : CollatzResearch.WordTrace tailWord_6268447 prefixEnd_6268447 3218726268234141405984443 := by
  unfold tailWord_6268447
  simp only [CollatzResearch.WordTrace]
  refine ⟨228629044721494559360635595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152419363147663039573757063 228629044721494559360635595)
  ·
    refine ⟨342943567082241839040953393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 228629044721494559360635595 342943567082241839040953393)
    ·
      refine ⟨257207675311681379280715045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 342943567082241839040953393 257207675311681379280715045)
      ·
        refine ⟨48226439120940258615134071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 257207675311681379280715045 48226439120940258615134071)
        ·
          refine ⟨72339658681410387922701107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48226439120940258615134071 72339658681410387922701107)
          ·
            refine ⟨108509488022115581884051661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 72339658681410387922701107 108509488022115581884051661)
            ·
              refine ⟨40691058008293343206519373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 108509488022115581884051661 40691058008293343206519373)
              ·
                refine ⟨15259146753110003702444765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 40691058008293343206519373 15259146753110003702444765)
                ·
                  refine ⟨5722180032416251388416787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15259146753110003702444765 5722180032416251388416787)
                  ·
                    refine ⟨8583270048624377082625181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5722180032416251388416787 8583270048624377082625181)
                    ·
                      refine ⟨3218726268234141405984443, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8583270048624377082625181 3218726268234141405984443)
                      ·
                        rfl

theorem cell23_6268447_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 3, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 3, 3, 3, 1, 3].length) (baseStart_6268447 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6268447 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6268447 prefixEnd_6268447 := by exact prefixLift 6268447
  have htrace : WordTrace (prefixWord ++ tailWord_6268447) baseStart_6268447 baseEnd_6268447 := by
    simpa [prefixWord, tailWord_6268447, baseEnd_6268447] using wordTrace_append hprefix tailTrace_6268447
  have hstable : (prefixWord ++ tailWord_6268447).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6268447).length < 2 ^ (prefixWord ++ tailWord_6268447).sum := by decide
  have hdescent : baseEnd_6268447 < baseStart_6268447 := by decide
  rcases family_descends (prefixWord ++ tailWord_6268447) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6268450 : List Nat := [3, 3, 1, 1, 1, 1, 2, 1, 5, 5]
def baseStart_6268450 : Nat := 118140960795 + 6268450 * 2 ^ 59
def prefixEnd_6268450 : Nat := 4983230072969 + 3 ^ 40 * 6268450 * 2
def baseEnd_6268450 : Nat := 1072909269558701631415643

theorem tailTrace_6268450 : CollatzResearch.WordTrace tailWord_6268450 prefixEnd_6268450 1072909269558701631415643 := by
  unfold tailWord_6268450
  simp only [CollatzResearch.WordTrace]
  refine ⟨57157288535120922718248701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 152419436093655793915329869 57157288535120922718248701)
  ·
    refine ⟨21433983200670346019343263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 57157288535120922718248701 21433983200670346019343263)
    ·
      refine ⟨32150974801005519029014895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21433983200670346019343263 32150974801005519029014895)
      ·
        refine ⟨48226462201508278543522343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32150974801005519029014895 48226462201508278543522343)
        ·
          refine ⟨72339693302262417815283515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48226462201508278543522343 72339693302262417815283515)
          ·
            refine ⟨108509539953393626722925273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 72339693302262417815283515 108509539953393626722925273)
            ·
              refine ⟨81382154965045220042193955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 108509539953393626722925273 81382154965045220042193955)
              ·
                refine ⟨122073232447567830063290933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 81382154965045220042193955 122073232447567830063290933)
                ·
                  refine ⟨11444365541959484068433525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 122073232447567830063290933 11444365541959484068433525)
                  ·
                    refine ⟨1072909269558701631415643, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11444365541959484068433525 1072909269558701631415643)
                    ·
                      rfl

theorem cell23_6268450_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 2, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 2, 1, 5, 5].length) (baseStart_6268450 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6268450 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6268450 prefixEnd_6268450 := by exact prefixLift 6268450
  have htrace : WordTrace (prefixWord ++ tailWord_6268450) baseStart_6268450 baseEnd_6268450 := by
    simpa [prefixWord, tailWord_6268450, baseEnd_6268450] using wordTrace_append hprefix tailTrace_6268450
  have hstable : (prefixWord ++ tailWord_6268450).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6268450).length < 2 ^ (prefixWord ++ tailWord_6268450).sum := by decide
  have hdescent : baseEnd_6268450 < baseStart_6268450 := by decide
  rcases family_descends (prefixWord ++ tailWord_6268450) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6268467 : List Nat := [1, 1, 1, 2, 4, 4, 2, 2, 1, 5]
def baseStart_6268467 : Nat := 118140960795 + 6268467 * 2 ^ 59
def prefixEnd_6268467 : Nat := 4983230072969 + 3 ^ 40 * 6268467 * 2
def baseEnd_6268467 : Nat := 1072912179282410442578117

theorem tailTrace_6268467 : CollatzResearch.WordTrace tailWord_6268467 prefixEnd_6268467 1072912179282410442578117 := by
  unfold tailWord_6268467
  simp only [CollatzResearch.WordTrace]
  refine ⟨228629774181422102776363655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152419849454281401850909103 228629774181422102776363655)
  ·
    refine ⟨342944661272133154164545483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 228629774181422102776363655 342944661272133154164545483)
    ·
      refine ⟨514416991908199731246818225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 342944661272133154164545483 514416991908199731246818225)
      ·
        refine ⟨385812743931149798435113669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 514416991908199731246818225 385812743931149798435113669)
        ·
          refine ⟨72339889487090587206583813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 385812743931149798435113669 72339889487090587206583813)
          ·
            refine ⟨13563729278829485101234465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 72339889487090587206583813 13563729278829485101234465)
            ·
              refine ⟨10172796959122113825925849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13563729278829485101234465 10172796959122113825925849)
              ·
                refine ⟨7629597719341585369444387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10172796959122113825925849 7629597719341585369444387)
                ·
                  refine ⟨11444396579012378054166581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7629597719341585369444387 11444396579012378054166581)
                  ·
                    refine ⟨1072912179282410442578117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11444396579012378054166581 1072912179282410442578117)
                    ·
                      rfl

theorem cell23_6268467_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 4, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 4, 2, 2, 1, 5].length) (baseStart_6268467 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6268467 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6268467 prefixEnd_6268467 := by exact prefixLift 6268467
  have htrace : WordTrace (prefixWord ++ tailWord_6268467) baseStart_6268467 baseEnd_6268467 := by
    simpa [prefixWord, tailWord_6268467, baseEnd_6268467] using wordTrace_append hprefix tailTrace_6268467
  have hstable : (prefixWord ++ tailWord_6268467).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6268467).length < 2 ^ (prefixWord ++ tailWord_6268467).sum := by decide
  have hdescent : baseEnd_6268467 < baseStart_6268467 := by decide
  rcases family_descends (prefixWord ++ tailWord_6268467) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6268497 : List Nat := [1, 2, 2, 1, 3, 2, 2, 4, 2, 4]
def baseStart_6268497 : Nat := 118140960795 + 6268497 * 2 ^ 59
def prefixEnd_6268497 : Nat := 4983230072969 + 3 ^ 40 * 6268497 * 2
def baseEnd_6268497 : Nat := 1072917314088955403453071

theorem tailTrace_6268497 : CollatzResearch.WordTrace tailWord_6268497 prefixEnd_6268497 1072917314088955403453071 := by
  unfold tailWord_6268497
  simp only [CollatzResearch.WordTrace]
  refine ⟨228630868371313417899955745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152420578914208945266637163 228630868371313417899955745)
  ·
    refine ⟨171473151278485063424966809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 228630868371313417899955745 171473151278485063424966809)
    ·
      refine ⟨128604863458863797568725107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 171473151278485063424966809 128604863458863797568725107)
      ·
        refine ⟨192907295188295696353087661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 128604863458863797568725107 192907295188295696353087661)
        ·
          refine ⟨72340235695610886132407873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 192907295188295696353087661 72340235695610886132407873)
          ·
            refine ⟨54255176771708164599305905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 72340235695610886132407873 54255176771708164599305905)
            ·
              refine ⟨40691382578781123449479429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 54255176771708164599305905 40691382578781123449479429)
              ·
                refine ⟨7629634233521460646777393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 40691382578781123449479429 7629634233521460646777393)
                ·
                  refine ⟨5722225675141095485083045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7629634233521460646777393 5722225675141095485083045)
                  ·
                    refine ⟨1072917314088955403453071, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5722225675141095485083045 1072917314088955403453071)
                    ·
                      rfl

theorem cell23_6268497_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 2, 4, 2, 4].length) (baseStart_6268497 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6268497 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6268497 prefixEnd_6268497 := by exact prefixLift 6268497
  have htrace : WordTrace (prefixWord ++ tailWord_6268497) baseStart_6268497 baseEnd_6268497 := by
    simpa [prefixWord, tailWord_6268497, baseEnd_6268497] using wordTrace_append hprefix tailTrace_6268497
  have hstable : (prefixWord ++ tailWord_6268497).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6268497).length < 2 ^ (prefixWord ++ tailWord_6268497).sum := by decide
  have hdescent : baseEnd_6268497 < baseStart_6268497 := by decide
  rcases family_descends (prefixWord ++ tailWord_6268497) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6268498 : List Nat := [3, 2, 2, 1, 2, 3, 3, 2, 1, 1, 3]
def baseStart_6268498 : Nat := 118140960795 + 6268498 * 2 ^ 59
def prefixEnd_6268498 : Nat := 4983230072969 + 3 ^ 40 * 6268498 * 2
def baseEnd_6268498 : Nat := 3218752455747520706446709

theorem tailTrace_6268498 : CollatzResearch.WordTrace tailWord_6268498 prefixEnd_6268498 3218752455747520706446709 := by
  unfold tailWord_6268498
  simp only [CollatzResearch.WordTrace]
  refine ⟨57157726211077448767685537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 152420603229539863380494765 57157726211077448767685537)
  ·
    refine ⟨42868294658308086575764153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57157726211077448767685537 42868294658308086575764153)
    ·
      refine ⟨32151220993731064931823115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42868294658308086575764153 32151220993731064931823115)
      ·
        refine ⟨48226831490596597397734673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32151220993731064931823115 48226831490596597397734673)
        ·
          refine ⟨36170123617947448048301005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48226831490596597397734673 36170123617947448048301005)
          ·
            refine ⟨13563796356730293018112877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 36170123617947448048301005 13563796356730293018112877)
            ·
              refine ⟨5086423633773859881792329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13563796356730293018112877 5086423633773859881792329)
              ·
                refine ⟨3814817725330394911344247, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5086423633773859881792329 3814817725330394911344247)
                ·
                  refine ⟨5722226587995592367016371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3814817725330394911344247 5722226587995592367016371)
                  ·
                    refine ⟨8583339881993388550524557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5722226587995592367016371 8583339881993388550524557)
                    ·
                      refine ⟨3218752455747520706446709, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8583339881993388550524557 3218752455747520706446709)
                      ·
                        rfl

theorem cell23_6268498_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 3, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 3, 3, 2, 1, 1, 3].length) (baseStart_6268498 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6268498 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6268498 prefixEnd_6268498 := by exact prefixLift 6268498
  have htrace : WordTrace (prefixWord ++ tailWord_6268498) baseStart_6268498 baseEnd_6268498 := by
    simpa [prefixWord, tailWord_6268498, baseEnd_6268498] using wordTrace_append hprefix tailTrace_6268498
  have hstable : (prefixWord ++ tailWord_6268498).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6268498).length < 2 ^ (prefixWord ++ tailWord_6268498).sum := by decide
  have hdescent : baseEnd_6268498 < baseStart_6268498 := by decide
  rcases family_descends (prefixWord ++ tailWord_6268498) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6268500 : List Nat := [2, 4, 1, 1, 1, 2, 1, 1, 3, 1, 6]
def baseStart_6268500 : Nat := 118140960795 + 6268500 * 2 ^ 59
def prefixEnd_6268500 : Nat := 4983230072969 + 3 ^ 40 * 6268500 * 2
def baseEnd_6268500 : Nat := 3218753482708829698621699

theorem tailTrace_6268500 : CollatzResearch.WordTrace tailWord_6268500 prefixEnd_6268500 3218753482708829698621699 := by
  unfold tailWord_6268500
  simp only [CollatzResearch.WordTrace]
  refine ⟨114315488895151274706157477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 152420651860201699608209969 114315488895151274706157477)
  ·
    refine ⟨21434154167840864007404527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 114315488895151274706157477 21434154167840864007404527)
    ·
      refine ⟨32151231251761296011106791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21434154167840864007404527 32151231251761296011106791)
      ·
        refine ⟨48226846877641944016660187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32151231251761296011106791 48226846877641944016660187)
        ·
          refine ⟨72340270316462916024990281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48226846877641944016660187 72340270316462916024990281)
          ·
            refine ⟨54255202737347187018742711, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 72340270316462916024990281 54255202737347187018742711)
            ·
              refine ⟨81382804106020780528114067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 54255202737347187018742711 81382804106020780528114067)
              ·
                refine ⟨122074206159031170792171101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 81382804106020780528114067 122074206159031170792171101)
                ·
                  refine ⟨45777827309636689047064163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 122074206159031170792171101 45777827309636689047064163)
                  ·
                    refine ⟨68666740964455033570596245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 45777827309636689047064163 68666740964455033570596245)
                    ·
                      refine ⟨3218753482708829698621699, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 68666740964455033570596245 3218753482708829698621699)
                      ·
                        rfl

theorem cell23_6268500_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 1, 1, 3, 1, 6].length) (baseStart_6268500 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6268500 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6268500 prefixEnd_6268500 := by exact prefixLift 6268500
  have htrace : WordTrace (prefixWord ++ tailWord_6268500) baseStart_6268500 baseEnd_6268500 := by
    simpa [prefixWord, tailWord_6268500, baseEnd_6268500] using wordTrace_append hprefix tailTrace_6268500
  have hstable : (prefixWord ++ tailWord_6268500).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6268500).length < 2 ^ (prefixWord ++ tailWord_6268500).sum := by decide
  have hdescent : baseEnd_6268500 < baseStart_6268500 := by decide
  rcases family_descends (prefixWord ++ tailWord_6268500) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6268534 : List Nat := [5, 1, 1, 2, 2, 2, 1, 2, 1, 2, 4]
def baseStart_6268534 : Nat := 118140960795 + 6268534 * 2 ^ 59
def prefixEnd_6268534 : Nat := 4983230072969 + 3 ^ 40 * 6268534 * 2
def baseEnd_6268534 : Nat := 3218770941051082565596543

theorem tailTrace_6268534 : CollatzResearch.WordTrace tailWord_6268534 prefixEnd_6268534 3218770941051082565596543 := by
  unfold tailWord_6268534
  simp only [CollatzResearch.WordTrace]
  refine ⟨14289513617011210826190791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 152421478581452915479368437 14289513617011210826190791)
  ·
    refine ⟨21434270425516816239286187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14289513617011210826190791 21434270425516816239286187)
    ·
      refine ⟨32151405638275224358929281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21434270425516816239286187 32151405638275224358929281)
      ·
        refine ⟨24113554228706418269196961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32151405638275224358929281 24113554228706418269196961)
        ·
          refine ⟨18085165671529813701897721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24113554228706418269196961 18085165671529813701897721)
          ·
            refine ⟨13563874253647360276423291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18085165671529813701897721 13563874253647360276423291)
            ·
              refine ⟨20345811380471040414634937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13563874253647360276423291 20345811380471040414634937)
              ·
                refine ⟨15259358535353280310976203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20345811380471040414634937 15259358535353280310976203)
                ·
                  refine ⟨22889037803029920466464305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15259358535353280310976203 22889037803029920466464305)
                  ·
                    refine ⟨17166778352272440349848229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 22889037803029920466464305 17166778352272440349848229)
                    ·
                      refine ⟨3218770941051082565596543, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17166778352272440349848229 3218770941051082565596543)
                      ·
                        rfl

theorem cell23_6268534_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 2, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 2, 1, 2, 1, 2, 4].length) (baseStart_6268534 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6268534 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6268534 prefixEnd_6268534 := by exact prefixLift 6268534
  have htrace : WordTrace (prefixWord ++ tailWord_6268534) baseStart_6268534 baseEnd_6268534 := by
    simpa [prefixWord, tailWord_6268534, baseEnd_6268534] using wordTrace_append hprefix tailTrace_6268534
  have hstable : (prefixWord ++ tailWord_6268534).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6268534).length < 2 ^ (prefixWord ++ tailWord_6268534).sum := by decide
  have hdescent : baseEnd_6268534 < baseStart_6268534 := by decide
  rcases family_descends (prefixWord ++ tailWord_6268534) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6268537 : List Nat := [1, 2, 1, 3, 3, 1, 3, 2, 1, 3, 3]
def baseStart_6268537 : Nat := 118140960795 + 6268537 * 2 ^ 59
def prefixEnd_6268537 : Nat := 4983230072969 + 3 ^ 40 * 6268537 * 2
def baseEnd_6268537 : Nat := 3218772481493046053859029

theorem tailTrace_6268537 : CollatzResearch.WordTrace tailWord_6268537 prefixEnd_6268537 3218772481493046053859029 := by
  unfold tailWord_6268537
  simp only [CollatzResearch.WordTrace]
  refine ⟨228632327291168504731411865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152421551527445669820941243 228632327291168504731411865)
  ·
    refine ⟨171474245468376378548558899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 228632327291168504731411865 171474245468376378548558899)
    ·
      refine ⟨257211368202564567822838349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 171474245468376378548558899 257211368202564567822838349)
      ·
        refine ⟨96454263075961712933564381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 257211368202564567822838349 96454263075961712933564381)
        ·
          refine ⟨36170348653485642350086643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 96454263075961712933564381 36170348653485642350086643)
          ·
            refine ⟨54255522980228463525129965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36170348653485642350086643 54255522980228463525129965)
            ·
              refine ⟨20345821117585673821923737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 54255522980228463525129965 20345821117585673821923737)
              ·
                refine ⟨15259365838189255366442803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20345821117585673821923737 15259365838189255366442803)
                ·
                  refine ⟨22889048757283883049664205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15259365838189255366442803 22889048757283883049664205)
                  ·
                    refine ⟨8583393283981456143624077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 22889048757283883049664205 8583393283981456143624077)
                    ·
                      refine ⟨3218772481493046053859029, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8583393283981456143624077 3218772481493046053859029)
                      ·
                        rfl

theorem cell23_6268537_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 3, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 3, 2, 1, 3, 3].length) (baseStart_6268537 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6268537 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6268537 prefixEnd_6268537 := by exact prefixLift 6268537
  have htrace : WordTrace (prefixWord ++ tailWord_6268537) baseStart_6268537 baseEnd_6268537 := by
    simpa [prefixWord, tailWord_6268537, baseEnd_6268537] using wordTrace_append hprefix tailTrace_6268537
  have hstable : (prefixWord ++ tailWord_6268537).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6268537).length < 2 ^ (prefixWord ++ tailWord_6268537).sum := by decide
  have hdescent : baseEnd_6268537 < baseStart_6268537 := by decide
  rcases family_descends (prefixWord ++ tailWord_6268537) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6268541 : List Nat := [1, 4, 1, 1, 4, 2, 3, 1, 1, 2, 3]
def baseStart_6268541 : Nat := 118140960795 + 6268541 * 2 ^ 59
def prefixEnd_6268541 : Nat := 4983230072969 + 3 ^ 40 * 6268541 * 2
def baseEnd_6268541 : Nat := 3218774535415664038209011

theorem tailTrace_6268541 : CollatzResearch.WordTrace tailWord_6268541 prefixEnd_6268541 3218774535415664038209011 := by
  unfold tailWord_6268541
  simp only [CollatzResearch.WordTrace]
  refine ⟨228632473183154013414557477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152421648788769342276371651 228632473183154013414557477)
  ·
    refine ⟨42868588721841377515229527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 228632473183154013414557477 42868588721841377515229527)
    ·
      refine ⟨64302883082762066272844291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42868588721841377515229527 64302883082762066272844291)
      ·
        refine ⟨96454324624143099409266437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64302883082762066272844291 96454324624143099409266437)
        ·
          refine ⟨18085185867026831139237457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 96454324624143099409266437 18085185867026831139237457)
          ·
            refine ⟨13563889400270123354428093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18085185867026831139237457 13563889400270123354428093)
            ·
              refine ⟨5086458525101296257910535, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13563889400270123354428093 5086458525101296257910535)
              ·
                refine ⟨7629687787651944386865803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5086458525101296257910535 7629687787651944386865803)
                ·
                  refine ⟨11444531681477916580298705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7629687787651944386865803 11444531681477916580298705)
                  ·
                    refine ⟨8583398761108437435224029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11444531681477916580298705 8583398761108437435224029)
                    ·
                      refine ⟨3218774535415664038209011, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8583398761108437435224029 3218774535415664038209011)
                      ·
                        rfl

theorem cell23_6268541_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 2, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 2, 3, 1, 1, 2, 3].length) (baseStart_6268541 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6268541 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6268541 prefixEnd_6268541 := by exact prefixLift 6268541
  have htrace : WordTrace (prefixWord ++ tailWord_6268541) baseStart_6268541 baseEnd_6268541 := by
    simpa [prefixWord, tailWord_6268541, baseEnd_6268541] using wordTrace_append hprefix tailTrace_6268541
  have hstable : (prefixWord ++ tailWord_6268541).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6268541).length < 2 ^ (prefixWord ++ tailWord_6268541).sum := by decide
  have hdescent : baseEnd_6268541 < baseStart_6268541 := by decide
  rcases family_descends (prefixWord ++ tailWord_6268541) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6268594 : List Nat := [3, 2, 1, 1, 1, 2, 4, 2, 1, 4, 2]
def baseStart_6268594 : Nat := 118140960795 + 6268594 * 2 ^ 59
def prefixEnd_6268594 : Nat := 4983230072969 + 3 ^ 40 * 6268594 * 2
def baseEnd_6268594 : Nat := 3218801749890352330846267

theorem tailTrace_6268594 : CollatzResearch.WordTrace tailWord_6268594 prefixEnd_6268594 3218801749890352330846267 := by
  unfold tailWord_6268594
  simp only [CollatzResearch.WordTrace]
  refine ⟨57158601562990500866559209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 152422937501308002310824557 57158601562990500866559209)
  ·
    refine ⟨42868951172242875649919407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57158601562990500866559209 42868951172242875649919407)
    ·
      refine ⟨64303426758364313474879111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42868951172242875649919407 64303426758364313474879111)
      ·
        refine ⟨96455140137546470212318667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64303426758364313474879111 96455140137546470212318667)
        ·
          refine ⟨144682710206319705318478001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 96455140137546470212318667 144682710206319705318478001)
          ·
            refine ⟨108512032654739778988858501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 144682710206319705318478001 108512032654739778988858501)
            ·
              refine ⟨20346006122763708560410969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 108512032654739778988858501 20346006122763708560410969)
              ·
                refine ⟨15259504592072781420308227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20346006122763708560410969 15259504592072781420308227)
                ·
                  refine ⟨22889256888109172130462341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15259504592072781420308227 22889256888109172130462341)
                  ·
                    refine ⟨4291735666520469774461689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 22889256888109172130462341 4291735666520469774461689)
                    ·
                      refine ⟨3218801749890352330846267, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4291735666520469774461689 3218801749890352330846267)
                      ·
                        rfl

theorem cell23_6268594_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 4, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 4, 2, 1, 4, 2].length) (baseStart_6268594 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6268594 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6268594 prefixEnd_6268594 := by exact prefixLift 6268594
  have htrace : WordTrace (prefixWord ++ tailWord_6268594) baseStart_6268594 baseEnd_6268594 := by
    simpa [prefixWord, tailWord_6268594, baseEnd_6268594] using wordTrace_append hprefix tailTrace_6268594
  have hstable : (prefixWord ++ tailWord_6268594).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6268594).length < 2 ^ (prefixWord ++ tailWord_6268594).sum := by decide
  have hdescent : baseEnd_6268594 < baseStart_6268594 := by decide
  rcases family_descends (prefixWord ++ tailWord_6268594) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6268628 : List Nat := [2, 4, 1, 3, 1, 3, 1, 1, 1, 4, 2]
def baseStart_6268628 : Nat := 118140960795 + 6268628 * 2 ^ 59
def prefixEnd_6268628 : Nat := 4983230072969 + 3 ^ 40 * 6268628 * 2
def baseEnd_6268628 : Nat := 3218819208232605197821111

theorem tailTrace_6268628 : CollatzResearch.WordTrace tailWord_6268628 prefixEnd_6268628 3218819208232605197821111 := by
  unfold tailWord_6268628
  simp only [CollatzResearch.WordTrace]
  refine ⟨114317823166919413636487269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 152423764222559218181983025 114317823166919413636487269)
  ·
    refine ⟨21434591843797390056841363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 114317823166919413636487269 21434591843797390056841363)
    ·
      refine ⟨32151887765696085085262045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21434591843797390056841363 32151887765696085085262045)
      ·
        refine ⟨12056957912136031906973267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 32151887765696085085262045 12056957912136031906973267)
        ·
          refine ⟨18085436868204047860459901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12056957912136031906973267 18085436868204047860459901)
          ·
            refine ⟨6782038825576517947672463, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18085436868204047860459901 6782038825576517947672463)
            ·
              refine ⟨10173058238364776921508695, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6782038825576517947672463 10173058238364776921508695)
              ·
                refine ⟨15259587357547165382263043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10173058238364776921508695 15259587357547165382263043)
                ·
                  refine ⟨22889381036320748073394565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15259587357547165382263043 22889381036320748073394565)
                  ·
                    refine ⟨4291758944310140263761481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 22889381036320748073394565 4291758944310140263761481)
                    ·
                      refine ⟨3218819208232605197821111, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4291758944310140263761481 3218819208232605197821111)
                      ·
                        rfl

theorem cell23_6268628_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 3, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 3, 1, 1, 1, 4, 2].length) (baseStart_6268628 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6268628 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6268628 prefixEnd_6268628 := by exact prefixLift 6268628
  have htrace : WordTrace (prefixWord ++ tailWord_6268628) baseStart_6268628 baseEnd_6268628 := by
    simpa [prefixWord, tailWord_6268628, baseEnd_6268628] using wordTrace_append hprefix tailTrace_6268628
  have hstable : (prefixWord ++ tailWord_6268628).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6268628).length < 2 ^ (prefixWord ++ tailWord_6268628).sum := by decide
  have hdescent : baseEnd_6268628 < baseStart_6268628 := by decide
  rcases family_descends (prefixWord ++ tailWord_6268628) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6268674 : List Nat := [3, 4, 1, 1, 1, 1, 3, 1, 1, 2, 5]
def baseStart_6268674 : Nat := 118140960795 + 6268674 * 2 ^ 59
def prefixEnd_6268674 : Nat := 4983230072969 + 3 ^ 40 * 6268674 * 2
def baseEnd_6268674 : Nat := 3218842828342712017845899

theorem tailTrace_6268674 : CollatzResearch.WordTrace tailWord_6268674 prefixEnd_6268674 3218842828342712017845899 := by
  unfold tailWord_6268674
  simp only [CollatzResearch.WordTrace]
  refine ⟨57159331022918044282287269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 152424882727781451419432717 57159331022918044282287269)
  ·
    refine ⟨10717374566797133302928863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 57159331022918044282287269 10717374566797133302928863)
    ·
      refine ⟨16076061850195699954393295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10717374566797133302928863 16076061850195699954393295)
      ·
        refine ⟨24114092775293549931589943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16076061850195699954393295 24114092775293549931589943)
        ·
          refine ⟨36171139162940324897384915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24114092775293549931589943 36171139162940324897384915)
          ·
            refine ⟨54256708744410487346077373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36171139162940324897384915 54256708744410487346077373)
            ·
              refine ⟨20346265779153932754779015, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 54256708744410487346077373 20346265779153932754779015)
              ·
                refine ⟨30519398668730899132168523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20346265779153932754779015 30519398668730899132168523)
                ·
                  refine ⟨45779098003096348698252785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30519398668730899132168523 45779098003096348698252785)
                  ·
                    refine ⟨34334323502322261523689589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 45779098003096348698252785 34334323502322261523689589)
                    ·
                      refine ⟨3218842828342712017845899, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 34334323502322261523689589 3218842828342712017845899)
                      ·
                        rfl

theorem cell23_6268674_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 3, 1, 1, 2, 5].length) (baseStart_6268674 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6268674 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6268674 prefixEnd_6268674 := by exact prefixLift 6268674
  have htrace : WordTrace (prefixWord ++ tailWord_6268674) baseStart_6268674 baseEnd_6268674 := by
    simpa [prefixWord, tailWord_6268674, baseEnd_6268674] using wordTrace_append hprefix tailTrace_6268674
  have hstable : (prefixWord ++ tailWord_6268674).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6268674).length < 2 ^ (prefixWord ++ tailWord_6268674).sum := by decide
  have hdescent : baseEnd_6268674 < baseStart_6268674 := by decide
  rcases family_descends (prefixWord ++ tailWord_6268674) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6268684 : List Nat := [2, 2, 1, 2, 2, 1, 2, 3, 2, 4, 2]
def baseStart_6268684 : Nat := 118140960795 + 6268684 * 2 ^ 59
def prefixEnd_6268684 : Nat := 4983230072969 + 3 ^ 40 * 6268684 * 2
def baseEnd_6268684 : Nat := 3218847963149256978720853

theorem tailTrace_6268684 : CollatzResearch.WordTrace tailWord_6268684 prefixEnd_6268684 3218847963149256978720853 := by
  unfold tailWord_6268684
  simp only [CollatzResearch.WordTrace]
  refine ⟨114318844410817974418506553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 152425125881090632558008737 114318844410817974418506553)
  ·
    refine ⟨85739133308113480813879915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 114318844410817974418506553 85739133308113480813879915)
    ·
      refine ⟨128608699962170221220819873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85739133308113480813879915 128608699962170221220819873)
      ·
        refine ⟨96456524971627665915614905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 128608699962170221220819873 96456524971627665915614905)
        ·
          refine ⟨72342393728720749436711179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 96456524971627665915614905 72342393728720749436711179)
          ·
            refine ⟨108513590593081124155066769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 72342393728720749436711179 108513590593081124155066769)
            ·
              refine ⟨81385192944810843116300077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 108513590593081124155066769 81385192944810843116300077)
              ·
                refine ⟨30519447354304066168612529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 81385192944810843116300077 30519447354304066168612529)
                ·
                  refine ⟨22889585515728049626459397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 30519447354304066168612529 22889585515728049626459397)
                  ·
                    refine ⟨4291797284199009304961137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 22889585515728049626459397 4291797284199009304961137)
                    ·
                      refine ⟨3218847963149256978720853, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4291797284199009304961137 3218847963149256978720853)
                      ·
                        rfl

theorem cell23_6268684_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 2, 3, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 2, 3, 2, 4, 2].length) (baseStart_6268684 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6268684 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6268684 prefixEnd_6268684 := by exact prefixLift 6268684
  have htrace : WordTrace (prefixWord ++ tailWord_6268684) baseStart_6268684 baseEnd_6268684 := by
    simpa [prefixWord, tailWord_6268684, baseEnd_6268684] using wordTrace_append hprefix tailTrace_6268684
  have hstable : (prefixWord ++ tailWord_6268684).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6268684).length < 2 ^ (prefixWord ++ tailWord_6268684).sum := by decide
  have hdescent : baseEnd_6268684 < baseStart_6268684 := by decide
  rcases family_descends (prefixWord ++ tailWord_6268684) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6268687 : List Nat := [1, 1, 2, 1, 1, 1, 4, 4, 1, 4, 3]
def baseStart_6268687 : Nat := 118140960795 + 6268687 * 2 ^ 59
def prefixEnd_6268687 : Nat := 4983230072969 + 3 ^ 40 * 6268687 * 2
def baseEnd_6268687 : Nat := 3218849503591220466983339

theorem tailTrace_6268687 : CollatzResearch.WordTrace tailWord_6268687 prefixEnd_6268687 3218849503591220466983339 := by
  unfold tailWord_6268687
  simp only [CollatzResearch.WordTrace]
  refine ⟨228637798240625080349372315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152425198827083386899581543 228637798240625080349372315)
  ·
    refine ⟨342956697360937620524058473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 228637798240625080349372315 342956697360937620524058473)
    ·
      refine ⟨257217523020703215393043855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 342956697360937620524058473 257217523020703215393043855)
      ·
        refine ⟨385826284531054823089565783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 257217523020703215393043855 385826284531054823089565783)
        ·
          refine ⟨578739426796582234634348675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 385826284531054823089565783 578739426796582234634348675)
          ·
            refine ⟨868109140194873351951523013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 578739426796582234634348675 868109140194873351951523013)
            ·
              refine ⟨162770463786538753490910565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 868109140194873351951523013 162770463786538753490910565)
              ·
                refine ⟨30519461959976016279545731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 162770463786538753490910565 30519461959976016279545731)
                ·
                  refine ⟨45779192939964024419318597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30519461959976016279545731 45779192939964024419318597)
                  ·
                    refine ⟨8583598676243254578622237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 45779192939964024419318597 8583598676243254578622237)
                    ·
                      refine ⟨3218849503591220466983339, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8583598676243254578622237 3218849503591220466983339)
                      ·
                        rfl

theorem cell23_6268687_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 4, 4, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 4, 4, 1, 4, 3].length) (baseStart_6268687 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6268687 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6268687 prefixEnd_6268687 := by exact prefixLift 6268687
  have htrace : WordTrace (prefixWord ++ tailWord_6268687) baseStart_6268687 baseEnd_6268687 := by
    simpa [prefixWord, tailWord_6268687, baseEnd_6268687] using wordTrace_append hprefix tailTrace_6268687
  have hstable : (prefixWord ++ tailWord_6268687).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6268687).length < 2 ^ (prefixWord ++ tailWord_6268687).sum := by decide
  have hdescent : baseEnd_6268687 < baseStart_6268687 := by decide
  rcases family_descends (prefixWord ++ tailWord_6268687) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6268728 : List Nat := [2, 1, 2, 1, 3, 3, 4, 2, 1, 4]
def baseStart_6268728 : Nat := 118140960795 + 6268728 * 2 ^ 59
def prefixEnd_6268728 : Nat := 4983230072969 + 3 ^ 40 * 6268728 * 2
def baseEnd_6268728 : Nat := 1072956852099351602190217

theorem tailTrace_6268728 : CollatzResearch.WordTrace tailWord_6268728 prefixEnd_6268728 1072956852099351602190217 := by
  unfold tailWord_6268728
  simp only [CollatzResearch.WordTrace]
  refine ⟨114319646816738272175807419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 152426195755651029567743225 114319646816738272175807419)
  ·
    refine ⟨171479470225107408263711129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114319646816738272175807419 171479470225107408263711129)
    ·
      refine ⟨128609602668830556197783347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 171479470225107408263711129 128609602668830556197783347)
      ·
        refine ⟨192914404003245834296675021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 128609602668830556197783347 192914404003245834296675021)
        ·
          refine ⟨72342901501217187861253133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 192914404003245834296675021 72342901501217187861253133)
          ·
            refine ⟨27128588062956445447969925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 72342901501217187861253133 27128588062956445447969925)
            ·
              refine ⟨5086610261804333521494361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 27128588062956445447969925 5086610261804333521494361)
              ·
                refine ⟨3814957696353250141120771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5086610261804333521494361 3814957696353250141120771)
                ·
                  refine ⟨5722436544529875211681157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3814957696353250141120771 5722436544529875211681157)
                  ·
                    refine ⟨1072956852099351602190217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5722436544529875211681157 1072956852099351602190217)
                    ·
                      rfl

theorem cell23_6268728_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 3, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 3, 4, 2, 1, 4].length) (baseStart_6268728 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6268728 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6268728 prefixEnd_6268728 := by exact prefixLift 6268728
  have htrace : WordTrace (prefixWord ++ tailWord_6268728) baseStart_6268728 baseEnd_6268728 := by
    simpa [prefixWord, tailWord_6268728, baseEnd_6268728] using wordTrace_append hprefix tailTrace_6268728
  have hstable : (prefixWord ++ tailWord_6268728).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6268728).length < 2 ^ (prefixWord ++ tailWord_6268728).sum := by decide
  have hdescent : baseEnd_6268728 < baseStart_6268728 := by decide
  rcases family_descends (prefixWord ++ tailWord_6268728) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6268754 : List Nat := [3, 2, 2, 1, 1, 3, 2, 1, 3, 5]
def baseStart_6268754 : Nat := 118140960795 + 6268754 * 2 ^ 59
def prefixEnd_6268754 : Nat := 4983230072969 + 3 ^ 40 * 6268754 * 2
def baseEnd_6268754 : Nat := 1072961302265023901615177

theorem tailTrace_6268754 : CollatzResearch.WordTrace tailWord_6268754 prefixEnd_6268754 1072961302265023901615177 := by
  unfold tailWord_6268754
  simp only [CollatzResearch.WordTrace]
  refine ⟨57160060482845587698015329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 152426827954254900528040877 57160060482845587698015329)
  ·
    refine ⟨42870045362134190773511497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57160060482845587698015329 42870045362134190773511497)
    ·
      refine ⟨32152534021600643080133623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42870045362134190773511497 32152534021600643080133623)
      ·
        refine ⟨48228801032400964620200435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32152534021600643080133623 48228801032400964620200435)
        ·
          refine ⟨72343201548601446930300653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48228801032400964620200435 72343201548601446930300653)
          ·
            refine ⟨27128700580725542598862745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 72343201548601446930300653 27128700580725542598862745)
            ·
              refine ⟨20346525435544156949147059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27128700580725542598862745 20346525435544156949147059)
              ·
                refine ⟨30519788153316235423720589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20346525435544156949147059 30519788153316235423720589)
                ·
                  refine ⟨11444920557493588283895221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 30519788153316235423720589 11444920557493588283895221)
                  ·
                    refine ⟨1072961302265023901615177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11444920557493588283895221 1072961302265023901615177)
                    ·
                      rfl

theorem cell23_6268754_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 3, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 3, 2, 1, 3, 5].length) (baseStart_6268754 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6268754 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6268754 prefixEnd_6268754 := by exact prefixLift 6268754
  have htrace : WordTrace (prefixWord ++ tailWord_6268754) baseStart_6268754 baseEnd_6268754 := by
    simpa [prefixWord, tailWord_6268754, baseEnd_6268754] using wordTrace_append hprefix tailTrace_6268754
  have hstable : (prefixWord ++ tailWord_6268754).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6268754).length < 2 ^ (prefixWord ++ tailWord_6268754).sum := by decide
  have hdescent : baseEnd_6268754 < baseStart_6268754 := by decide
  rcases family_descends (prefixWord ++ tailWord_6268754) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6268768 : List Nat := [2, 1, 1, 3, 3, 2, 1, 5, 1, 1, 3]
def baseStart_6268768 : Nat := 118140960795 + 6268768 * 2 ^ 59
def prefixEnd_6268768 : Nat := 4983230072969 + 3 ^ 40 * 6268768 * 2
def baseEnd_6268768 : Nat := 3218891095524234650070467

theorem tailTrace_6268768 : CollatzResearch.WordTrace tailWord_6268768 prefixEnd_6268768 3218891095524234650070467 := by
  unfold tailWord_6268768
  simp only [CollatzResearch.WordTrace]
  refine ⟨114320376276665815591535479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 152427168368887754122047305 114320376276665815591535479)
  ·
    refine ⟨171480564414998723387303219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114320376276665815591535479 171480564414998723387303219)
    ·
      refine ⟨257220846622498085080954829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 171480564414998723387303219 257220846622498085080954829)
      ·
        refine ⟨96457817483436781905358061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 257220846622498085080954829 96457817483436781905358061)
        ·
          refine ⟨36171681556288793214509273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 96457817483436781905358061 36171681556288793214509273)
          ·
            refine ⟨27128761167216594910881955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36171681556288793214509273 27128761167216594910881955)
            ·
              refine ⟨40693141750824892366322933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27128761167216594910881955 40693141750824892366322933)
              ·
                refine ⟨3814982039139833659342775, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 40693141750824892366322933 3814982039139833659342775)
                ·
                  refine ⟨5722473058709750489014163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3814982039139833659342775 5722473058709750489014163)
                  ·
                    refine ⟨8583709588064625733521245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5722473058709750489014163 8583709588064625733521245)
                    ·
                      refine ⟨3218891095524234650070467, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8583709588064625733521245 3218891095524234650070467)
                      ·
                        rfl

theorem cell23_6268768_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 2, 1, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 2, 1, 5, 1, 1, 3].length) (baseStart_6268768 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6268768 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6268768 prefixEnd_6268768 := by exact prefixLift 6268768
  have htrace : WordTrace (prefixWord ++ tailWord_6268768) baseStart_6268768 baseEnd_6268768 := by
    simpa [prefixWord, tailWord_6268768, baseEnd_6268768] using wordTrace_append hprefix tailTrace_6268768
  have hstable : (prefixWord ++ tailWord_6268768).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6268768).length < 2 ^ (prefixWord ++ tailWord_6268768).sum := by decide
  have hdescent : baseEnd_6268768 < baseStart_6268768 := by decide
  rcases family_descends (prefixWord ++ tailWord_6268768) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6268771 : List Nat := [1, 1, 1, 5, 4, 1, 1, 3, 1, 5]
def baseStart_6268771 : Nat := 118140960795 + 6268771 * 2 ^ 59
def prefixEnd_6268771 : Nat := 4983230072969 + 3 ^ 40 * 6268771 * 2
def baseEnd_6268771 : Nat := 1072964211988732712777651

theorem tailTrace_6268771 : CollatzResearch.WordTrace tailWord_6268771 prefixEnd_6268771 1072964211988732712777651 := by
  unfold tailWord_6268771
  simp only [CollatzResearch.WordTrace]
  refine ⟨228640861972320762695430167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152427241314880508463620111 228640861972320762695430167)
  ·
    refine ⟨342961292958481144043145251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 228640861972320762695430167 342961292958481144043145251)
    ·
      refine ⟨514441939437721716064717877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 342961292958481144043145251 514441939437721716064717877)
      ·
        refine ⟨48228931822286410881067301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 514441939437721716064717877 48228931822286410881067301)
        ·
          refine ⟨9042924716678702040200119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 48228931822286410881067301 9042924716678702040200119)
          ·
            refine ⟨13564387075018053060300179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9042924716678702040200119 13564387075018053060300179)
            ·
              refine ⟨20346580612527079590450269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13564387075018053060300179 20346580612527079590450269)
              ·
                refine ⟨7629967729697654846418851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20346580612527079590450269 7629967729697654846418851)
                ·
                  refine ⟨11444951594546482269628277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7629967729697654846418851 11444951594546482269628277)
                  ·
                    refine ⟨1072964211988732712777651, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11444951594546482269628277 1072964211988732712777651)
                    ·
                      rfl

theorem cell23_6268771_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 4, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 4, 1, 1, 3, 1, 5].length) (baseStart_6268771 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6268771 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6268771 prefixEnd_6268771 := by exact prefixLift 6268771
  have htrace : WordTrace (prefixWord ++ tailWord_6268771) baseStart_6268771 baseEnd_6268771 := by
    simpa [prefixWord, tailWord_6268771, baseEnd_6268771] using wordTrace_append hprefix tailTrace_6268771
  have hstable : (prefixWord ++ tailWord_6268771).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6268771).length < 2 ^ (prefixWord ++ tailWord_6268771).sum := by decide
  have hdescent : baseEnd_6268771 < baseStart_6268771 := by decide
  rcases family_descends (prefixWord ++ tailWord_6268771) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6268777 : List Nat := [1, 2, 1, 1, 1, 3, 1, 2, 5, 1, 5]
def baseStart_6268777 : Nat := 118140960795 + 6268777 * 2 ^ 59
def prefixEnd_6268777 : Nat := 4983230072969 + 3 ^ 40 * 6268777 * 2
def baseEnd_6268777 : Nat := 3218895716850125114857925

theorem tailTrace_6268777 : CollatzResearch.WordTrace tailWord_6268777 prefixEnd_6268777 3218895716850125114857925 := by
  unfold tailWord_6268777
  simp only [CollatzResearch.WordTrace]
  refine ⟨228641080810299025720148585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152427387206866017146765723 228641080810299025720148585)
  ·
    refine ⟨171480810607724269290111439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 228641080810299025720148585 171480810607724269290111439)
    ·
      refine ⟨257221215911586403935167159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 171480810607724269290111439 257221215911586403935167159)
      ·
        refine ⟨385831823867379605902750739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 257221215911586403935167159 385831823867379605902750739)
        ·
          refine ⟨578747735801069408854126109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 385831823867379605902750739 578747735801069408854126109)
          ·
            refine ⟨217030400925401028320297291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 578747735801069408854126109 217030400925401028320297291)
            ·
              refine ⟨325545601388101542480445937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 217030400925401028320297291 325545601388101542480445937)
              ·
                refine ⟨244159201041076156860334453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 325545601388101542480445937 244159201041076156860334453)
                ·
                  refine ⟨22889925097600889705656355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 244159201041076156860334453 22889925097600889705656355)
                  ·
                    refine ⟨34334887646401334558484533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 22889925097600889705656355 34334887646401334558484533)
                    ·
                      refine ⟨3218895716850125114857925, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 34334887646401334558484533 3218895716850125114857925)
                      ·
                        rfl

theorem cell23_6268777_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 1, 2, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 1, 2, 5, 1, 5].length) (baseStart_6268777 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6268777 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6268777 prefixEnd_6268777 := by exact prefixLift 6268777
  have htrace : WordTrace (prefixWord ++ tailWord_6268777) baseStart_6268777 baseEnd_6268777 := by
    simpa [prefixWord, tailWord_6268777, baseEnd_6268777] using wordTrace_append hprefix tailTrace_6268777
  have hstable : (prefixWord ++ tailWord_6268777).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6268777).length < 2 ^ (prefixWord ++ tailWord_6268777).sum := by decide
  have hdescent : baseEnd_6268777 < baseStart_6268777 := by decide
  rcases family_descends (prefixWord ++ tailWord_6268777) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6268787 : List Nat := [1, 1, 1, 2, 2, 1, 3, 4, 1, 1, 6]
def baseStart_6268787 : Nat := 118140960795 + 6268787 * 2 ^ 59
def prefixEnd_6268787 : Nat := 4983230072969 + 3 ^ 40 * 6268787 * 2
def baseEnd_6268787 : Nat := 3218900851656670075732879

theorem tailTrace_6268787 : CollatzResearch.WordTrace tailWord_6268787 prefixEnd_6268787 3218900851656670075732879 := by
  unfold tailWord_6268787
  simp only [CollatzResearch.WordTrace]
  refine ⟨228641445540262797428012615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152427630360175198285341743 228641445540262797428012615)
  ·
    refine ⟨342962168310394196142018923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 228641445540262797428012615 342962168310394196142018923)
    ·
      refine ⟨514443252465591294213028385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 342962168310394196142018923 514443252465591294213028385)
      ·
        refine ⟨385832439349193470659771289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 514443252465591294213028385 385832439349193470659771289)
        ·
          refine ⟨289374329511895102994828467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 385832439349193470659771289 289374329511895102994828467)
          ·
            refine ⟨434061494267842654492242701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 289374329511895102994828467 434061494267842654492242701)
            ·
              refine ⟨162773060350440995434591013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 434061494267842654492242701 162773060350440995434591013)
              ·
                refine ⟨30519948815707686643985815, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 162773060350440995434591013 30519948815707686643985815)
                ·
                  refine ⟨45779923223561529965978723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30519948815707686643985815 45779923223561529965978723)
                  ·
                    refine ⟨68669884835342294948968085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 45779923223561529965978723 68669884835342294948968085)
                    ·
                      refine ⟨3218900851656670075732879, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 68669884835342294948968085 3218900851656670075732879)
                      ·
                        rfl

theorem cell23_6268787_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 3, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 3, 4, 1, 1, 6].length) (baseStart_6268787 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6268787 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6268787 prefixEnd_6268787 := by exact prefixLift 6268787
  have htrace : WordTrace (prefixWord ++ tailWord_6268787) baseStart_6268787 baseEnd_6268787 := by
    simpa [prefixWord, tailWord_6268787, baseEnd_6268787] using wordTrace_append hprefix tailTrace_6268787
  have hstable : (prefixWord ++ tailWord_6268787).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6268787).length < 2 ^ (prefixWord ++ tailWord_6268787).sum := by decide
  have hdescent : baseEnd_6268787 < baseStart_6268787 := by decide
  rcases family_descends (prefixWord ++ tailWord_6268787) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6268794 : List Nat := [3, 1, 1, 1, 1, 1, 4, 1, 5, 2, 3]
def baseStart_6268794 : Nat := 118140960795 + 6268794 * 2 ^ 59
def prefixEnd_6268794 : Nat := 4983230072969 + 3 ^ 40 * 6268794 * 2
def baseEnd_6268794 : Nat := 3218904446021251548345347

theorem tailTrace_6268794 : CollatzResearch.WordTrace tailWord_6268794 prefixEnd_6268794 3218904446021251548345347 := by
  unfold tailWord_6268794
  simp only [CollatzResearch.WordTrace]
  refine ⟨57160425212809359405879359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 152427800567491625082344957 57160425212809359405879359)
  ·
    refine ⟨85740637819214039108819039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57160425212809359405879359 85740637819214039108819039)
    ·
      refine ⟨128610956728821058663228559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85740637819214039108819039 128610956728821058663228559)
      ·
        refine ⟨192916435093231587994842839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 128610956728821058663228559 192916435093231587994842839)
        ·
          refine ⟨289374652639847381992264259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 192916435093231587994842839 289374652639847381992264259)
          ·
            refine ⟨434061978959771072988396389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 289374652639847381992264259 434061978959771072988396389)
            ·
              refine ⟨81386621054957076185324323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 434061978959771072988396389 81386621054957076185324323)
              ·
                refine ⟨122079931582435614277986485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 81386621054957076185324323 122079931582435614277986485)
                ·
                  refine ⟨11444993585853338838561233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 122079931582435614277986485 11444993585853338838561233)
                  ·
                    refine ⟨8583745189390004128920925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11444993585853338838561233 8583745189390004128920925)
                    ·
                      refine ⟨3218904446021251548345347, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8583745189390004128920925 3218904446021251548345347)
                      ·
                        rfl

theorem cell23_6268794_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 4, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 4, 1, 5, 2, 3].length) (baseStart_6268794 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6268794 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6268794 prefixEnd_6268794 := by exact prefixLift 6268794
  have htrace : WordTrace (prefixWord ++ tailWord_6268794) baseStart_6268794 baseEnd_6268794 := by
    simpa [prefixWord, tailWord_6268794, baseEnd_6268794] using wordTrace_append hprefix tailTrace_6268794
  have hstable : (prefixWord ++ tailWord_6268794).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6268794).length < 2 ^ (prefixWord ++ tailWord_6268794).sum := by decide
  have hdescent : baseEnd_6268794 < baseStart_6268794 := by decide
  rcases family_descends (prefixWord ++ tailWord_6268794) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6268797 : List Nat := [1, 4, 1, 1, 2, 1, 1, 12]
def baseStart_6268797 : Nat := 118140960795 + 6268797 * 2 ^ 59
def prefixEnd_6268797 : Nat := 4983230072969 + 3 ^ 40 * 6268797 * 2
def baseEnd_6268797 : Nat := 119218740239378334689179

theorem tailTrace_6268797 : CollatzResearch.WordTrace tailWord_6268797 prefixEnd_6268797 119218740239378334689179 := by
  unfold tailWord_6268797
  simp only [CollatzResearch.WordTrace]
  refine ⟨228641810270226569135876645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152427873513484379423917763 228641810270226569135876645)
  ·
    refine ⟨42870339425667481712976871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 228641810270226569135876645 42870339425667481712976871)
    ·
      refine ⟨64305509138501222569465307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42870339425667481712976871 64305509138501222569465307)
      ·
        refine ⟨96458263707751833854197961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64305509138501222569465307 96458263707751833854197961)
        ·
          refine ⟨72343697780813875390648471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 96458263707751833854197961 72343697780813875390648471)
          ·
            refine ⟨108515546671220813085972707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 72343697780813875390648471 108515546671220813085972707)
            ·
              refine ⟨162773320006831219628959061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 108515546671220813085972707 162773320006831219628959061)
              ·
                refine ⟨119218740239378334689179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 12 162773320006831219628959061 119218740239378334689179)
                ·
                  rfl

theorem cell23_6268797_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 1, 12].length) (baseStart_6268797 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6268797 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6268797 prefixEnd_6268797 := by exact prefixLift 6268797
  have htrace : WordTrace (prefixWord ++ tailWord_6268797) baseStart_6268797 baseEnd_6268797 := by
    simpa [prefixWord, tailWord_6268797, baseEnd_6268797] using wordTrace_append hprefix tailTrace_6268797
  have hstable : (prefixWord ++ tailWord_6268797).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6268797).length < 2 ^ (prefixWord ++ tailWord_6268797).sum := by decide
  have hdescent : baseEnd_6268797 < baseStart_6268797 := by decide
  rcases family_descends (prefixWord ++ tailWord_6268797) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6268808 : List Nat := [2, 1, 3, 3, 3, 1, 2, 2, 1, 1, 4]
def baseStart_6268808 : Nat := 118140960795 + 6268808 * 2 ^ 59
def prefixEnd_6268808 : Nat := 4983230072969 + 3 ^ 40 * 6268808 * 2
def baseEnd_6268808 : Nat := 3218911634750414493570283

theorem tailTrace_6268808 : CollatzResearch.WordTrace tailWord_6268808 prefixEnd_6268808 3218911634750414493570283 := by
  unfold tailWord_6268808
  simp only [CollatzResearch.WordTrace]
  refine ⟨114321105736593359007263539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 152428140982124478676351385 114321105736593359007263539)
  ·
    refine ⟨171481658604890038510895309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114321105736593359007263539 171481658604890038510895309)
    ·
      refine ⟨64305621976833764441585741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 171481658604890038510895309 64305621976833764441585741)
      ·
        refine ⟨24114608241312661665594653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 64305621976833764441585741 24114608241312661665594653)
        ·
          refine ⟨9042978090492248124597995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24114608241312661665594653 9042978090492248124597995)
          ·
            refine ⟨13564467135738372186896993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9042978090492248124597995 13564467135738372186896993)
            ·
              refine ⟨10173350351803779140172745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13564467135738372186896993 10173350351803779140172745)
              ·
                refine ⟨7630012763852834355129559, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10173350351803779140172745 7630012763852834355129559)
                ·
                  refine ⟨11445019145779251532694339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7630012763852834355129559 11445019145779251532694339)
                  ·
                    refine ⟨17167528718668877299041509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11445019145779251532694339 17167528718668877299041509)
                    ·
                      refine ⟨3218911634750414493570283, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17167528718668877299041509 3218911634750414493570283)
                      ·
                        rfl

theorem cell23_6268808_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 3, 1, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 3, 1, 2, 2, 1, 1, 4].length) (baseStart_6268808 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6268808 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6268808 prefixEnd_6268808 := by exact prefixLift 6268808
  have htrace : WordTrace (prefixWord ++ tailWord_6268808) baseStart_6268808 baseEnd_6268808 := by
    simpa [prefixWord, tailWord_6268808, baseEnd_6268808] using wordTrace_append hprefix tailTrace_6268808
  have hstable : (prefixWord ++ tailWord_6268808).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6268808).length < 2 ^ (prefixWord ++ tailWord_6268808).sum := by decide
  have hdescent : baseEnd_6268808 < baseStart_6268808 := by decide
  rcases family_descends (prefixWord ++ tailWord_6268808) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6268825 : List Nat := [1, 2, 1, 2, 1, 3, 5, 3, 1, 2, 2]
def baseStart_6268825 : Nat := 118140960795 + 6268825 * 2 ^ 59
def prefixEnd_6268825 : Nat := 4983230072969 + 3 ^ 40 * 6268825 * 2
def baseEnd_6268825 : Nat := 3218920363921540927057705

theorem tailTrace_6268825 : CollatzResearch.WordTrace tailWord_6268825 prefixEnd_6268825 3218920363921540927057705 := by
  unfold tailWord_6268825
  simp only [CollatzResearch.WordTrace]
  refine ⟨228642831514125129917895929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152428554342750086611930619 228642831514125129917895929)
  ·
    refine ⟨171482123635593847438421947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 228642831514125129917895929 171482123635593847438421947)
    ·
      refine ⟨257223185453390771157632921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 171482123635593847438421947 257223185453390771157632921)
      ·
        refine ⟨192917389090043078368224691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 257223185453390771157632921 192917389090043078368224691)
        ·
          refine ⟨289376083635064617552337037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 192917389090043078368224691 289376083635064617552337037)
          ·
            refine ⟨108516031363149231582126389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 289376083635064617552337037 108516031363149231582126389)
            ·
              refine ⟨10173377940295240460824349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 108516031363149231582126389 10173377940295240460824349)
              ·
                refine ⟨3815016727610715172809131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10173377940295240460824349 3815016727610715172809131)
                ·
                  refine ⟨5722525091416072759213697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3815016727610715172809131 5722525091416072759213697)
                  ·
                    refine ⟨4291893818562054569410273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5722525091416072759213697 4291893818562054569410273)
                    ·
                      refine ⟨3218920363921540927057705, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4291893818562054569410273 3218920363921540927057705)
                      ·
                        rfl

theorem cell23_6268825_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 5, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 5, 3, 1, 2, 2].length) (baseStart_6268825 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6268825 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6268825 prefixEnd_6268825 := by exact prefixLift 6268825
  have htrace : WordTrace (prefixWord ++ tailWord_6268825) baseStart_6268825 baseEnd_6268825 := by
    simpa [prefixWord, tailWord_6268825, baseEnd_6268825] using wordTrace_append hprefix tailTrace_6268825
  have hstable : (prefixWord ++ tailWord_6268825).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6268825).length < 2 ^ (prefixWord ++ tailWord_6268825).sum := by decide
  have hdescent : baseEnd_6268825 < baseStart_6268825 := by decide
  rcases family_descends (prefixWord ++ tailWord_6268825) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6268828 : List Nat := [2, 2, 3, 3, 1, 1, 2, 3, 1, 2, 3]
def baseStart_6268828 : Nat := 118140960795 + 6268828 * 2 ^ 59
def prefixEnd_6268828 : Nat := 4983230072969 + 3 ^ 40 * 6268828 * 2
def baseEnd_6268828 : Nat := 3218921904363504415320191

theorem tailTrace_6268828 : CollatzResearch.WordTrace tailWord_6268828 prefixEnd_6268828 3218921904363504415320191 := by
  unfold tailWord_6268828
  simp only [CollatzResearch.WordTrace]
  refine ⟨114321470466557130715127569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 152428627288742840953503425 114321470466557130715127569)
  ·
    refine ⟨85741102849917848036345677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 114321470466557130715127569 85741102849917848036345677)
    ·
      refine ⟨32152913568719193013629629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 85741102849917848036345677 32152913568719193013629629)
      ·
        refine ⟨12057342588269697380111111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 32152913568719193013629629 12057342588269697380111111)
        ·
          refine ⟨18086013882404546070166667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12057342588269697380111111 18086013882404546070166667)
          ·
            refine ⟨27129020823606819105250001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18086013882404546070166667 27129020823606819105250001)
            ·
              refine ⟨20346765617705114328937501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27129020823606819105250001 20346765617705114328937501)
              ·
                refine ⟨7630037106639417873351563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20346765617705114328937501 7630037106639417873351563)
                ·
                  refine ⟨11445055659959126810027345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7630037106639417873351563 11445055659959126810027345)
                  ·
                    refine ⟨8583791744969345107520509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11445055659959126810027345 8583791744969345107520509)
                    ·
                      refine ⟨3218921904363504415320191, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8583791744969345107520509 3218921904363504415320191)
                      ·
                        rfl

theorem cell23_6268828_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 1, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 1, 2, 3, 1, 2, 3].length) (baseStart_6268828 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6268828 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6268828 prefixEnd_6268828 := by exact prefixLift 6268828
  have htrace : WordTrace (prefixWord ++ tailWord_6268828) baseStart_6268828 baseEnd_6268828 := by
    simpa [prefixWord, tailWord_6268828, baseEnd_6268828] using wordTrace_append hprefix tailTrace_6268828
  have hstable : (prefixWord ++ tailWord_6268828).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6268828).length < 2 ^ (prefixWord ++ tailWord_6268828).sum := by decide
  have hdescent : baseEnd_6268828 < baseStart_6268828 := by decide
  rcases family_descends (prefixWord ++ tailWord_6268828) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6268831 : List Nat := [1, 1, 2, 5, 4, 1, 9]
def baseStart_6268831 : Nat := 118140960795 + 6268831 * 2 ^ 59
def prefixEnd_6268831 : Nat := 4983230072969 + 3 ^ 40 * 6268831 * 2
def baseEnd_6268831 : Nat := 39739795614882319797317

theorem tailTrace_6268831 : CollatzResearch.WordTrace tailWord_6268831 prefixEnd_6268831 39739795614882319797317 := by
  unfold tailWord_6268831
  simp only [CollatzResearch.WordTrace]
  refine ⟨228643050352103392942614347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152428700234735595295076231 228643050352103392942614347)
  ·
    refine ⟨342964575528155089413921521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 228643050352103392942614347 342964575528155089413921521)
    ·
      refine ⟨257223431646116317060441141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 342964575528155089413921521 257223431646116317060441141)
      ·
        refine ⟨24114696716823404724416357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 257223431646116317060441141 24114696716823404724416357)
        ·
          refine ⟨4521505634404388385828067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 24114696716823404724416357 4521505634404388385828067)
          ·
            refine ⟨6782258451606582578742101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4521505634404388385828067 6782258451606582578742101)
            ·
              refine ⟨39739795614882319797317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 6782258451606582578742101 39739795614882319797317)
              ·
                rfl

theorem cell23_6268831_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 4, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 4, 1, 9].length) (baseStart_6268831 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6268831 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6268831 prefixEnd_6268831 := by exact prefixLift 6268831
  have htrace : WordTrace (prefixWord ++ tailWord_6268831) baseStart_6268831 baseEnd_6268831 := by
    simpa [prefixWord, tailWord_6268831, baseEnd_6268831] using wordTrace_append hprefix tailTrace_6268831
  have hstable : (prefixWord ++ tailWord_6268831).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6268831).length < 2 ^ (prefixWord ++ tailWord_6268831).sum := by decide
  have hdescent : baseEnd_6268831 < baseStart_6268831 := by decide
  rcases family_descends (prefixWord ++ tailWord_6268831) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6268851 : List Nat := [1, 1, 1, 2, 3, 1, 4, 2, 3, 3, 2]
def baseStart_6268851 : Nat := 118140960795 + 6268851 * 2 ^ 59
def prefixEnd_6268851 : Nat := 4983230072969 + 3 ^ 40 * 6268851 * 2
def baseEnd_6268851 : Nat := 3218933714418557825332585

theorem tailTrace_6268851 : CollatzResearch.WordTrace tailWord_6268851 prefixEnd_6268851 3218933714418557825332585 := by
  unfold tailWord_6268851
  simp only [CollatzResearch.WordTrace]
  refine ⟨228643779812030936358342407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152429186541353957572228271 228643779812030936358342407)
  ·
    refine ⟨342965669718046404537513611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 228643779812030936358342407 342965669718046404537513611)
    ·
      refine ⟨514448504577069606806270417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 342965669718046404537513611 514448504577069606806270417)
      ·
        refine ⟨385836378432802205104702813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 514448504577069606806270417 385836378432802205104702813)
        ·
          refine ⟨144688641912300826914263555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 385836378432802205104702813 144688641912300826914263555)
          ·
            refine ⟨217032962868451240371395333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 144688641912300826914263555 217032962868451240371395333)
            ·
              refine ⟨40693680537834607569636625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 217032962868451240371395333 40693680537834607569636625)
              ·
                refine ⟨30520260403375955677227469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 40693680537834607569636625 30520260403375955677227469)
                ·
                  refine ⟨11445097651265983378960301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 30520260403375955677227469 11445097651265983378960301)
                  ·
                    refine ⟨4291911619224743767110113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11445097651265983378960301 4291911619224743767110113)
                    ·
                      refine ⟨3218933714418557825332585, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4291911619224743767110113 3218933714418557825332585)
                      ·
                        rfl

theorem cell23_6268851_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 4, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 4, 2, 3, 3, 2].length) (baseStart_6268851 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6268851 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6268851 prefixEnd_6268851 := by exact prefixLift 6268851
  have htrace : WordTrace (prefixWord ++ tailWord_6268851) baseStart_6268851 baseEnd_6268851 := by
    simpa [prefixWord, tailWord_6268851, baseEnd_6268851] using wordTrace_append hprefix tailTrace_6268851
  have hstable : (prefixWord ++ tailWord_6268851).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6268851).length < 2 ^ (prefixWord ++ tailWord_6268851).sum := by decide
  have hdescent : baseEnd_6268851 < baseStart_6268851 := by decide
  rcases family_descends (prefixWord ++ tailWord_6268851) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6268904 : List Nat := [2, 1, 4, 1, 1, 1, 1, 5, 7]
def baseStart_6268904 : Nat := 118140960795 + 6268904 * 2 ^ 59
def prefixEnd_6268904 : Nat := 4983230072969 + 3 ^ 40 * 6268904 * 2
def baseEnd_6268904 : Nat := 357662325432582901996649

theorem tailTrace_6268904 : CollatzResearch.WordTrace tailWord_6268904 prefixEnd_6268904 357662325432582901996649 := by
  unfold tailWord_6268904
  simp only [CollatzResearch.WordTrace]
  refine ⟨114322856440419463205010883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 152430475253892617606681177 114322856440419463205010883)
  ·
    refine ⟨171484284660629194807516325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114322856440419463205010883 171484284660629194807516325)
    ·
      refine ⟨32153303373867974026409311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 171484284660629194807516325 32153303373867974026409311)
      ·
        refine ⟨48229955060801961039613967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32153303373867974026409311 48229955060801961039613967)
        ·
          refine ⟨72344932591202941559420951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48229955060801961039613967 72344932591202941559420951)
          ·
            refine ⟨108517398886804412339131427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 72344932591202941559420951 108517398886804412339131427)
            ·
              refine ⟨162776098330206618508697141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 108517398886804412339131427 162776098330206618508697141)
              ·
                refine ⟨15260259218456870485190357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 162776098330206618508697141 15260259218456870485190357)
                ·
                  refine ⟨357662325432582901996649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 15260259218456870485190357 357662325432582901996649)
                  ·
                    rfl

theorem cell23_6268904_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 1, 5, 7].length) (baseStart_6268904 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6268904 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6268904 prefixEnd_6268904 := by exact prefixLift 6268904
  have htrace : WordTrace (prefixWord ++ tailWord_6268904) baseStart_6268904 baseEnd_6268904 := by
    simpa [prefixWord, tailWord_6268904, baseEnd_6268904] using wordTrace_append hprefix tailTrace_6268904
  have hstable : (prefixWord ++ tailWord_6268904).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6268904).length < 2 ^ (prefixWord ++ tailWord_6268904).sum := by decide
  have hdescent : baseEnd_6268904 < baseStart_6268904 := by decide
  rcases family_descends (prefixWord ++ tailWord_6268904) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6268949 : List Nat := [1, 3, 2, 1, 6, 1, 1, 2, 2, 2, 2]
def baseStart_6268949 : Nat := 118140960795 + 6268949 * 2 ^ 59
def prefixEnd_6268949 : Nat := 4983230072969 + 3 ^ 40 * 6268949 * 2
def baseEnd_6268949 : Nat := 3218984035522698441907135

theorem tailTrace_6268949 : CollatzResearch.WordTrace tailWord_6268949 prefixEnd_6268949 3218984035522698441907135 := by
  unfold tailWord_6268949
  simp only [CollatzResearch.WordTrace]
  refine ⟨228647354165675899095409901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152431569443783932730273267 228647354165675899095409901)
  ·
    refine ⟨85742757812128462160778713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 228647354165675899095409901 85742757812128462160778713)
    ·
      refine ⟨64307068359096346620584035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 85742757812128462160778713 64307068359096346620584035)
      ·
        refine ⟨96460602538644519930876053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64307068359096346620584035 96460602538644519930876053)
        ·
          refine ⟨4521590743998961871759815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 96460602538644519930876053 4521590743998961871759815)
          ·
            refine ⟨6782386115998442807639723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4521590743998961871759815 6782386115998442807639723)
            ·
              refine ⟨10173579173997664211459585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6782386115998442807639723 10173579173997664211459585)
              ·
                refine ⟨7630184380498248158594689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10173579173997664211459585 7630184380498248158594689)
                ·
                  refine ⟨5722638285373686118946017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7630184380498248158594689 5722638285373686118946017)
                  ·
                    refine ⟨4291978714030264589209513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5722638285373686118946017 4291978714030264589209513)
                    ·
                      refine ⟨3218984035522698441907135, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4291978714030264589209513 3218984035522698441907135)
                      ·
                        rfl

theorem cell23_6268949_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 6, 1, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 6, 1, 1, 2, 2, 2, 2].length) (baseStart_6268949 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6268949 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6268949 prefixEnd_6268949 := by exact prefixLift 6268949
  have htrace : WordTrace (prefixWord ++ tailWord_6268949) baseStart_6268949 baseEnd_6268949 := by
    simpa [prefixWord, tailWord_6268949, baseEnd_6268949] using wordTrace_append hprefix tailTrace_6268949
  have hstable : (prefixWord ++ tailWord_6268949).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6268949).length < 2 ^ (prefixWord ++ tailWord_6268949).sum := by decide
  have hdescent : baseEnd_6268949 < baseStart_6268949 := by decide
  rcases family_descends (prefixWord ++ tailWord_6268949) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6268971 : List Nat := [1, 1, 1, 1, 2, 1, 4, 3, 1, 6, 2]
def baseStart_6268971 : Nat := 118140960795 + 6268971 * 2 ^ 59
def prefixEnd_6268971 : Nat := 4983230072969 + 3 ^ 40 * 6268971 * 2
def baseEnd_6268971 : Nat := 3218995332097097355832033

theorem tailTrace_6268971 : CollatzResearch.WordTrace tailWord_6268971 prefixEnd_6268971 3218995332097097355832033 := by
  unfold tailWord_6268971
  simp only [CollatzResearch.WordTrace]
  refine ⟨228648156571596196852710767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152432104381064131235140511 228648156571596196852710767)
  ·
    refine ⟨342972234857394295279066151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 228648156571596196852710767 342972234857394295279066151)
    ·
      refine ⟨514458352286091442918599227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 342972234857394295279066151 514458352286091442918599227)
      ·
        refine ⟨771687528429137164377898841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 514458352286091442918599227 771687528429137164377898841)
        ·
          refine ⟨578765646321852873283424131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 771687528429137164377898841 578765646321852873283424131)
          ·
            refine ⟨868148469482779309925136197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 578765646321852873283424131 868148469482779309925136197)
            ·
              refine ⟨162777838028021120610963037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 868148469482779309925136197 162777838028021120610963037)
              ·
                refine ⟨61041689260507920229111139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 162777838028021120610963037 61041689260507920229111139)
                ·
                  refine ⟨91562533890761880343666709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 61041689260507920229111139 91562533890761880343666709)
                  ·
                    refine ⟨4291993776129463141109377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 91562533890761880343666709 4291993776129463141109377)
                    ·
                      refine ⟨3218995332097097355832033, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4291993776129463141109377 3218995332097097355832033)
                      ·
                        rfl

theorem cell23_6268971_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 4, 3, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 4, 3, 1, 6, 2].length) (baseStart_6268971 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6268971 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6268971 prefixEnd_6268971 := by exact prefixLift 6268971
  have htrace : WordTrace (prefixWord ++ tailWord_6268971) baseStart_6268971 baseEnd_6268971 := by
    simpa [prefixWord, tailWord_6268971, baseEnd_6268971] using wordTrace_append hprefix tailTrace_6268971
  have hstable : (prefixWord ++ tailWord_6268971).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6268971).length < 2 ^ (prefixWord ++ tailWord_6268971).sum := by decide
  have hdescent : baseEnd_6268971 < baseStart_6268971 := by decide
  rcases family_descends (prefixWord ++ tailWord_6268971) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6268991 : List Nat := [1, 1, 2, 2, 3, 1, 4, 1, 1, 4, 3]
def baseStart_6268991 : Nat := 118140960795 + 6268991 * 2 ^ 59
def prefixEnd_6268991 : Nat := 4983230072969 + 3 ^ 40 * 6268991 * 2
def baseEnd_6268991 : Nat := 3219005601710187277581941

theorem tailTrace_6268991 : CollatzResearch.WordTrace tailWord_6268991 prefixEnd_6268991 3219005601710187277581941 := by
  unfold tailWord_6268991
  simp only [CollatzResearch.WordTrace]
  refine ⟨228648886031523740268438827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152432590687682493512292551 228648886031523740268438827)
  ·
    refine ⟨342973329047285610402658241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 228648886031523740268438827 342973329047285610402658241)
    ·
      refine ⟨257229996785464207801993681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 342973329047285610402658241 257229996785464207801993681)
      ·
        refine ⟨192922497589098155851495261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 257229996785464207801993681 192922497589098155851495261)
        ·
          refine ⟨72345936595911808444310723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 192922497589098155851495261 72345936595911808444310723)
          ·
            refine ⟨108518904893867712666466085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 72345936595911808444310723 108518904893867712666466085)
            ·
              refine ⟨20347294667600196124962391, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 108518904893867712666466085 20347294667600196124962391)
              ·
                refine ⟨30520942001400294187443587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20347294667600196124962391 30520942001400294187443587)
                ·
                  refine ⟨45781413002100441281165381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30520942001400294187443587 45781413002100441281165381)
                  ·
                    refine ⟨8584014937893832740218509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 45781413002100441281165381 8584014937893832740218509)
                    ·
                      refine ⟨3219005601710187277581941, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8584014937893832740218509 3219005601710187277581941)
                      ·
                        rfl

theorem cell23_6268991_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 4, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 4, 1, 1, 4, 3].length) (baseStart_6268991 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6268991 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6268991 prefixEnd_6268991 := by exact prefixLift 6268991
  have htrace : WordTrace (prefixWord ++ tailWord_6268991) baseStart_6268991 baseEnd_6268991 := by
    simpa [prefixWord, tailWord_6268991, baseEnd_6268991] using wordTrace_append hprefix tailTrace_6268991
  have hstable : (prefixWord ++ tailWord_6268991).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6268991).length < 2 ^ (prefixWord ++ tailWord_6268991).sum := by decide
  have hdescent : baseEnd_6268991 < baseStart_6268991 := by decide
  rcases family_descends (prefixWord ++ tailWord_6268991) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6269028 : List Nat := [2, 3, 1, 1, 2, 1, 6, 1, 6]
def baseStart_6269028 : Nat := 118140960795 + 6269028 * 2 ^ 59
def prefixEnd_6269028 : Nat := 4983230072969 + 3 ^ 40 * 6269028 * 2
def baseEnd_6269028 : Nat := 357669400054933736979919

theorem tailTrace_6269028 : CollatzResearch.WordTrace tailWord_6269028 prefixEnd_6269028 357669400054933736979919 := by
  unfold tailWord_6269028
  simp only [CollatzResearch.WordTrace]
  refine ⟨114325117766194847793767869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 152433490354926463725023825 114325117766194847793767869)
  ·
    refine ⟨42871919162323067922662951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 114325117766194847793767869 42871919162323067922662951)
    ·
      refine ⟨64307878743484601883994427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42871919162323067922662951 64307878743484601883994427)
      ·
        refine ⟨96461818115226902825991641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64307878743484601883994427 96461818115226902825991641)
        ·
          refine ⟨72346363586420177119493731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 96461818115226902825991641 72346363586420177119493731)
          ·
            refine ⟨108519545379630265679240597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 72346363586420177119493731 108519545379630265679240597)
            ·
              refine ⟨5086853689670168703714403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 108519545379630265679240597 5086853689670168703714403)
              ·
                refine ⟨7630280534505253055571605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5086853689670168703714403 7630280534505253055571605)
                ·
                  refine ⟨357669400054933736979919, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7630280534505253055571605 357669400054933736979919)
                  ·
                    rfl

theorem cell23_6269028_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 6, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 6, 1, 6].length) (baseStart_6269028 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6269028 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6269028 prefixEnd_6269028 := by exact prefixLift 6269028
  have htrace : WordTrace (prefixWord ++ tailWord_6269028) baseStart_6269028 baseEnd_6269028 := by
    simpa [prefixWord, tailWord_6269028, baseEnd_6269028] using wordTrace_append hprefix tailTrace_6269028
  have hstable : (prefixWord ++ tailWord_6269028).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6269028).length < 2 ^ (prefixWord ++ tailWord_6269028).sum := by decide
  have hdescent : baseEnd_6269028 < baseStart_6269028 := by decide
  rcases family_descends (prefixWord ++ tailWord_6269028) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6269041 : List Nat := [1, 2, 2, 2, 1, 1, 5, 1, 3, 5]
def baseStart_6269041 : Nat := 118140960795 + 6269041 * 2 ^ 59
def prefixEnd_6269041 : Nat := 4983230072969 + 3 ^ 40 * 6269041 * 2
def baseEnd_6269041 : Nat := 1073010425247637360652237

theorem tailTrace_6269041 : CollatzResearch.WordTrace tailWord_6269041 prefixEnd_6269041 1073010425247637360652237 := by
  unfold tailWord_6269041
  simp only [CollatzResearch.WordTrace]
  refine ⟨228650709681342598807758977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152433806454228399205172651 228650709681342598807758977)
  ·
    refine ⟨171488032261006949105819233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 228650709681342598807758977 171488032261006949105819233)
    ·
      refine ⟨128616024195755211829364425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 171488032261006949105819233 128616024195755211829364425)
      ·
        refine ⟨96462018146816408872023319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 128616024195755211829364425 96462018146816408872023319)
        ·
          refine ⟨144693027220224613308034979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 96462018146816408872023319 144693027220224613308034979)
          ·
            refine ⟨217039540830336919962052469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 144693027220224613308034979 217039540830336919962052469)
            ·
              refine ⟨20347456952844086246442419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 217039540830336919962052469 20347456952844086246442419)
              ·
                refine ⟨30521185429266129369663629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20347456952844086246442419 30521185429266129369663629)
                ·
                  refine ⟨11445444535974798513623861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 30521185429266129369663629 11445444535974798513623861)
                  ·
                    refine ⟨1073010425247637360652237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11445444535974798513623861 1073010425247637360652237)
                    ·
                      rfl

theorem cell23_6269041_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 5, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 5, 1, 3, 5].length) (baseStart_6269041 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6269041 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6269041 prefixEnd_6269041 := by exact prefixLift 6269041
  have htrace : WordTrace (prefixWord ++ tailWord_6269041) baseStart_6269041 baseEnd_6269041 := by
    simpa [prefixWord, tailWord_6269041, baseEnd_6269041] using wordTrace_append hprefix tailTrace_6269041
  have hstable : (prefixWord ++ tailWord_6269041).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6269041).length < 2 ^ (prefixWord ++ tailWord_6269041).sum := by decide
  have hdescent : baseEnd_6269041 < baseStart_6269041 := by decide
  rcases family_descends (prefixWord ++ tailWord_6269041) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6269081 : List Nat := [1, 2, 1, 2, 1, 2, 1, 6, 1, 1, 5]
def baseStart_6269081 : Nat := 118140960795 + 6269081 * 2 ^ 59
def prefixEnd_6269081 : Nat := 4983230072969 + 3 ^ 40 * 6269081 * 2
def baseEnd_6269081 : Nat := 3219051814969091925456527

theorem tailTrace_6269081 : CollatzResearch.WordTrace tailWord_6269081 prefixEnd_6269081 3219051814969091925456527 := by
  unfold tailWord_6269081
  simp only [CollatzResearch.WordTrace]
  refine ⟨228652168601197685639215097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152434779067465123759476731 228652168601197685639215097)
  ·
    refine ⟨171489126450898264229411323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 228652168601197685639215097 171489126450898264229411323)
    ·
      refine ⟨257233689676347396344116985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 171489126450898264229411323 257233689676347396344116985)
      ·
        refine ⟨192925267257260547258087739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 257233689676347396344116985 192925267257260547258087739)
        ·
          refine ⟨289387900885890820887131609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 192925267257260547258087739 289387900885890820887131609)
          ·
            refine ⟨217040925664418115665348707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 289387900885890820887131609 217040925664418115665348707)
            ·
              refine ⟨325561388496627173498023061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 217040925664418115665348707 325561388496627173498023061)
              ·
                refine ⟨15260690085779398757719831, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 325561388496627173498023061 15260690085779398757719831)
                ·
                  refine ⟨22891035128669098136579747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15260690085779398757719831 22891035128669098136579747)
                  ·
                    refine ⟨34336552693003647204869621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 22891035128669098136579747 34336552693003647204869621)
                    ·
                      refine ⟨3219051814969091925456527, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 34336552693003647204869621 3219051814969091925456527)
                      ·
                        rfl

theorem cell23_6269081_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 1, 6, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 1, 6, 1, 1, 5].length) (baseStart_6269081 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6269081 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6269081 prefixEnd_6269081 := by exact prefixLift 6269081
  have htrace : WordTrace (prefixWord ++ tailWord_6269081) baseStart_6269081 baseEnd_6269081 := by
    simpa [prefixWord, tailWord_6269081, baseEnd_6269081] using wordTrace_append hprefix tailTrace_6269081
  have hstable : (prefixWord ++ tailWord_6269081).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6269081).length < 2 ^ (prefixWord ++ tailWord_6269081).sum := by decide
  have hdescent : baseEnd_6269081 < baseStart_6269081 := by decide
  rcases family_descends (prefixWord ++ tailWord_6269081) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6269088 : List Nat := [2, 1, 1, 4, 2, 3, 2, 1, 1, 6]
def baseStart_6269088 : Nat := 118140960795 + 6269088 * 2 ^ 59
def prefixEnd_6269088 : Nat := 4983230072969 + 3 ^ 40 * 6269088 * 2
def baseEnd_6269088 : Nat := 1073018469777891132689665

theorem tailTrace_6269088 : CollatzResearch.WordTrace tailWord_6269088 prefixEnd_6269088 1073018469777891132689665 := by
  unfold tailWord_6269088
  simp only [CollatzResearch.WordTrace]
  refine ⟨114326211956086162917359959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 152434949274781550556479945 114326211956086162917359959)
  ·
    refine ⟨171489317934129244376039939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114326211956086162917359959 171489317934129244376039939)
    ·
      refine ⟨257233976901193866564059909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 171489317934129244376039939 257233976901193866564059909)
      ·
        refine ⟨48231370668973849980761233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 257233976901193866564059909 48231370668973849980761233)
        ·
          refine ⟨36173528001730387485570925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48231370668973849980761233 36173528001730387485570925)
          ·
            refine ⟨13565073000648895307089097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 36173528001730387485570925 13565073000648895307089097)
            ·
              refine ⟨10173804750486671480316823, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13565073000648895307089097 10173804750486671480316823)
              ·
                refine ⟨15260707125730007220475235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10173804750486671480316823 15260707125730007220475235)
                ·
                  refine ⟨22891060688595010830712853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15260707125730007220475235 22891060688595010830712853)
                  ·
                    refine ⟨1073018469777891132689665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 22891060688595010830712853 1073018469777891132689665)
                    ·
                      rfl

theorem cell23_6269088_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 3, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 3, 2, 1, 1, 6].length) (baseStart_6269088 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6269088 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6269088 prefixEnd_6269088 := by exact prefixLift 6269088
  have htrace : WordTrace (prefixWord ++ tailWord_6269088) baseStart_6269088 baseEnd_6269088 := by
    simpa [prefixWord, tailWord_6269088, baseEnd_6269088] using wordTrace_append hprefix tailTrace_6269088
  have hstable : (prefixWord ++ tailWord_6269088).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6269088).length < 2 ^ (prefixWord ++ tailWord_6269088).sum := by decide
  have hdescent : baseEnd_6269088 < baseStart_6269088 := by decide
  rcases family_descends (prefixWord ++ tailWord_6269088) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6269109 : List Nat := [1, 3, 3, 4, 1, 2, 2, 1, 1, 5]
def baseStart_6269109 : Nat := 118140960795 + 6269109 * 2 ^ 59
def prefixEnd_6269109 : Nat := 4983230072969 + 3 ^ 40 * 6269109 * 2
def baseEnd_6269109 : Nat := 1073022064142472605302133

theorem tailTrace_6269109 : CollatzResearch.WordTrace tailWord_6269109 prefixEnd_6269109 1073022064142472605302133 := by
  unfold tailWord_6269109
  simp only [CollatzResearch.WordTrace]
  refine ⟨228653189845096246421234381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152435459896730830947489587 228653189845096246421234381)
  ·
    refine ⟨85744946191911092407962893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 228653189845096246421234381 85744946191911092407962893)
    ·
      refine ⟨32154354821966659652986085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 85744946191911092407962893 32154354821966659652986085)
      ·
        refine ⟨6028941529118748684934891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 32154354821966659652986085 6028941529118748684934891)
        ·
          refine ⟨9043412293678123027402337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6028941529118748684934891 9043412293678123027402337)
          ·
            refine ⟨6782559220258592270551753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9043412293678123027402337 6782559220258592270551753)
            ·
              refine ⟨5086919415193944202913815, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6782559220258592270551753 5086919415193944202913815)
              ·
                refine ⟨7630379122790916304370723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5086919415193944202913815 7630379122790916304370723)
                ·
                  refine ⟨11445568684186374456556085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7630379122790916304370723 11445568684186374456556085)
                  ·
                    refine ⟨1073022064142472605302133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11445568684186374456556085 1073022064142472605302133)
                    ·
                      rfl

theorem cell23_6269109_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 4, 1, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 4, 1, 2, 2, 1, 1, 5].length) (baseStart_6269109 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6269109 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6269109 prefixEnd_6269109 := by exact prefixLift 6269109
  have htrace : WordTrace (prefixWord ++ tailWord_6269109) baseStart_6269109 baseEnd_6269109 := by
    simpa [prefixWord, tailWord_6269109, baseEnd_6269109] using wordTrace_append hprefix tailTrace_6269109
  have hstable : (prefixWord ++ tailWord_6269109).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6269109).length < 2 ^ (prefixWord ++ tailWord_6269109).sum := by decide
  have hdescent : baseEnd_6269109 < baseStart_6269109 := by decide
  rcases family_descends (prefixWord ++ tailWord_6269109) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
