import V185TrunkScan20Chunk043

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental

namespace V185TrunkScan20Incremental

def tailWord_267441 : List Nat := [1, 2, 2, 5, 1, 1, 2, 2, 4]
def baseStart_267441 : Nat := 118140960795 + 267441 * 2 ^ 59
def prefixEnd_267441 : Nat := 4983230072969 + 3 ^ 40 * 267441 * 2
def baseEnd_267441 : Nat := 122067359750394106273393

theorem tailTrace_267441 : CollatzResearch.WordTrace tailWord_267441 prefixEnd_267441 122067359750394106273393 := by
  unfold tailWord_267441
  simp only [CollatzResearch.WordTrace]
  refine ⟨9754374624114407131514177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6502916416076271421009451 9754374624114407131514177)
  ·
    refine ⟨7315780968085805348635633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9754374624114407131514177 7315780968085805348635633)
    ·
      refine ⟨5486835726064354011476725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7315780968085805348635633 5486835726064354011476725)
      ·
        refine ⟨514390849318533188575943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 5486835726064354011476725 514390849318533188575943)
        ·
          refine ⟨771586273977799782863915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 514390849318533188575943 771586273977799782863915)
          ·
            refine ⟨1157379410966699674295873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 771586273977799782863915 1157379410966699674295873)
            ·
              refine ⟨868034558225024755721905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1157379410966699674295873 868034558225024755721905)
              ·
                refine ⟨651025918668768566791429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 868034558225024755721905 651025918668768566791429)
                ·
                  refine ⟨122067359750394106273393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 651025918668768566791429 122067359750394106273393)
                  ·
                    rfl

theorem cell20_267441_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 1, 2, 2, 4].length) (baseStart_267441 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_267441 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_267441 prefixEnd_267441 := by exact prefixLift 267441
  have htrace : WordTrace (prefixWord ++ tailWord_267441) baseStart_267441 baseEnd_267441 := by
    simpa [prefixWord, tailWord_267441, baseEnd_267441] using wordTrace_append hprefix tailTrace_267441
  have hstable : (prefixWord ++ tailWord_267441).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_267441).length < 2 ^ (prefixWord ++ tailWord_267441).sum := by decide
  have hdescent : baseEnd_267441 < baseStart_267441 := by decide
  rcases family_descends (prefixWord ++ tailWord_267441) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_267479 : List Nat := [1, 1, 3, 2, 1, 2, 2, 6, 2]
def baseStart_267479 : Nat := 118140960795 + 267479 * 2 ^ 59
def prefixEnd_267479 : Nat := 4983230072969 + 3 ^ 40 * 267479 * 2
def baseEnd_267479 : Nat := 122084703985834863006571

theorem tailTrace_267479 : CollatzResearch.WordTrace tailWord_267479 prefixEnd_267479 122084703985834863006571 := by
  unfold tailWord_267479
  simp only [CollatzResearch.WordTrace]
  refine ⟨9755760597976739621397491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6503840398651159747598327 9755760597976739621397491)
  ·
    refine ⟨14633640896965109432096237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9755760597976739621397491 14633640896965109432096237)
    ·
      refine ⟨5487615336361916037036089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14633640896965109432096237 5487615336361916037036089)
      ·
        refine ⟨4115711502271437027777067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5487615336361916037036089 4115711502271437027777067)
        ·
          refine ⟨6173567253407155541665601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4115711502271437027777067 6173567253407155541665601)
          ·
            refine ⟨4630175440055366656249201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6173567253407155541665601 4630175440055366656249201)
            ·
              refine ⟨3472631580041524992186901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4630175440055366656249201 3472631580041524992186901)
              ·
                refine ⟨162779605314446484008761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3472631580041524992186901 162779605314446484008761)
                ·
                  refine ⟨122084703985834863006571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 162779605314446484008761 122084703985834863006571)
                  ·
                    rfl

theorem cell20_267479_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 2, 6, 2].length) (baseStart_267479 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_267479 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_267479 prefixEnd_267479 := by exact prefixLift 267479
  have htrace : WordTrace (prefixWord ++ tailWord_267479) baseStart_267479 baseEnd_267479 := by
    simpa [prefixWord, tailWord_267479, baseEnd_267479] using wordTrace_append hprefix tailTrace_267479
  have hstable : (prefixWord ++ tailWord_267479).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_267479).length < 2 ^ (prefixWord ++ tailWord_267479).sum := by decide
  have hdescent : baseEnd_267479 < baseStart_267479 := by decide
  rcases family_descends (prefixWord ++ tailWord_267479) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_267485 : List Nat := [1, 4, 3, 2, 3, 1, 2, 1, 3]
def baseStart_267485 : Nat := 118140960795 + 267485 * 2 ^ 59
def prefixEnd_267485 : Nat := 4983230072969 + 3 ^ 40 * 267485 * 2
def baseEnd_267485 : Nat := 122087442549325508806547

theorem tailTrace_267485 : CollatzResearch.WordTrace tailWord_267485 prefixEnd_267485 122087442549325508806547 := by
  unfold tailWord_267485
  simp only [CollatzResearch.WordTrace]
  refine ⟨9755979435955002646115909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6503986290636668430743939 9755979435955002646115909)
  ·
    refine ⟨1829246144241562996146733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 9755979435955002646115909 1829246144241562996146733)
    ·
      refine ⟨685967304090586123555025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1829246144241562996146733 685967304090586123555025)
      ·
        refine ⟨514475478067939592666269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 685967304090586123555025 514475478067939592666269)
        ·
          refine ⟨192928304275477347249851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 514475478067939592666269 192928304275477347249851)
          ·
            refine ⟨289392456413216020874777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 192928304275477347249851 289392456413216020874777)
            ·
              refine ⟨217044342309912015656083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 289392456413216020874777 217044342309912015656083)
              ·
                refine ⟨325566513464868023484125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 217044342309912015656083 325566513464868023484125)
                ·
                  refine ⟨122087442549325508806547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 325566513464868023484125 122087442549325508806547)
                  ·
                    rfl

theorem cell20_267485_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 3, 1, 2, 1, 3].length) (baseStart_267485 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_267485 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_267485 prefixEnd_267485 := by exact prefixLift 267485
  have htrace : WordTrace (prefixWord ++ tailWord_267485) baseStart_267485 baseEnd_267485 := by
    simpa [prefixWord, tailWord_267485, baseEnd_267485] using wordTrace_append hprefix tailTrace_267485
  have hstable : (prefixWord ++ tailWord_267485).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_267485).length < 2 ^ (prefixWord ++ tailWord_267485).sum := by decide
  have hdescent : baseEnd_267485 < baseStart_267485 := by decide
  rcases family_descends (prefixWord ++ tailWord_267485) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_267489 : List Nat := [1, 2, 3, 1, 3, 4, 2, 1, 3]
def baseStart_267489 : Nat := 118140960795 + 267489 * 2 ^ 59
def prefixEnd_267489 : Nat := 4983230072969 + 3 ^ 40 * 267489 * 2
def baseEnd_267489 : Nat := 122089268258319272673197

theorem tailTrace_267489 : CollatzResearch.WordTrace tailWord_267489 prefixEnd_267489 122089268258319272673197 := by
  unfold tailWord_267489
  simp only [CollatzResearch.WordTrace]
  refine ⟨9756125327940511329261521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6504083551960340886174347 9756125327940511329261521)
  ·
    refine ⟨7317093995955383496946141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9756125327940511329261521 7317093995955383496946141)
    ·
      refine ⟨2743910248483268811354803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7317093995955383496946141 2743910248483268811354803)
      ·
        refine ⟨4115865372724903217032205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2743910248483268811354803 4115865372724903217032205)
        ·
          refine ⟨1543449514771838706387077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4115865372724903217032205 1543449514771838706387077)
          ·
            refine ⟨289396784019719757447577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1543449514771838706387077 289396784019719757447577)
            ·
              refine ⟨217047588014789818085683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 289396784019719757447577 217047588014789818085683)
              ·
                refine ⟨325571382022184727128525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 217047588014789818085683 325571382022184727128525)
                ·
                  refine ⟨122089268258319272673197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 325571382022184727128525 122089268258319272673197)
                  ·
                    rfl

theorem cell20_267489_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 4, 2, 1, 3].length) (baseStart_267489 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_267489 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_267489 prefixEnd_267489 := by exact prefixLift 267489
  have htrace : WordTrace (prefixWord ++ tailWord_267489) baseStart_267489 baseEnd_267489 := by
    simpa [prefixWord, tailWord_267489, baseEnd_267489] using wordTrace_append hprefix tailTrace_267489
  have hstable : (prefixWord ++ tailWord_267489).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_267489).length < 2 ^ (prefixWord ++ tailWord_267489).sum := by decide
  have hdescent : baseEnd_267489 < baseStart_267489 := by decide
  rcases family_descends (prefixWord ++ tailWord_267489) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_267507 : List Nat := [1, 1, 1, 2, 2, 5, 2, 6]
def baseStart_267507 : Nat := 118140960795 + 267507 * 2 ^ 59
def prefixEnd_267507 : Nat := 4983230072969 + 3 ^ 40 * 267507 * 2
def baseEnd_267507 : Nat := 40699161316263736691041

theorem tailTrace_267507 : CollatzResearch.WordTrace tailWord_267507 prefixEnd_267507 40699161316263736691041 := by
  unfold tailWord_267507
  simp only [CollatzResearch.WordTrace]
  refine ⟨9756781841875300403416775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6504521227916866935611183 9756781841875300403416775)
  ·
    refine ⟨14635172762812950605125163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9756781841875300403416775 14635172762812950605125163)
    ·
      refine ⟨21952759144219425907687745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14635172762812950605125163 21952759144219425907687745)
      ·
        refine ⟨16464569358164569430765809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21952759144219425907687745 16464569358164569430765809)
        ·
          refine ⟨12348427018623427073074357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16464569358164569430765809 12348427018623427073074357)
          ·
            refine ⟨1157665032995946288100721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 12348427018623427073074357 1157665032995946288100721)
            ·
              refine ⟨868248774746959716075541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1157665032995946288100721 868248774746959716075541)
              ·
                refine ⟨40699161316263736691041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 868248774746959716075541 40699161316263736691041)
                ·
                  rfl

theorem cell20_267507_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 5, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 5, 2, 6].length) (baseStart_267507 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_267507 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_267507 prefixEnd_267507 := by exact prefixLift 267507
  have htrace : WordTrace (prefixWord ++ tailWord_267507) baseStart_267507 baseEnd_267507 := by
    simpa [prefixWord, tailWord_267507, baseEnd_267507] using wordTrace_append hprefix tailTrace_267507
  have hstable : (prefixWord ++ tailWord_267507).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_267507).length < 2 ^ (prefixWord ++ tailWord_267507).sum := by decide
  have hdescent : baseEnd_267507 < baseStart_267507 := by decide
  rcases family_descends (prefixWord ++ tailWord_267507) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_267531 : List Nat := [1, 1, 1, 1, 5, 3, 1, 4, 3]
def baseStart_267531 : Nat := 118140960795 + 267531 * 2 ^ 59
def prefixEnd_267531 : Nat := 4983230072969 + 3 ^ 40 * 267531 * 2
def baseEnd_267531 : Nat := 122108438202753793273025

theorem tailTrace_267531 : CollatzResearch.WordTrace tailWord_267531 prefixEnd_267531 122108438202753793273025 := by
  unfold tailWord_267531
  simp only [CollatzResearch.WordTrace]
  refine ⟨9757657193788352502290447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6505104795858901668193631 9757657193788352502290447)
  ·
    refine ⟨14636485790682528753435671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9757657193788352502290447 14636485790682528753435671)
    ·
      refine ⟨21954728686023793130153507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14636485790682528753435671 21954728686023793130153507)
      ·
        refine ⟨32932093029035689695230261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21954728686023793130153507 32932093029035689695230261)
        ·
          refine ⟨3087383721472095908927837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 32932093029035689695230261 3087383721472095908927837)
          ·
            refine ⟨1157768895552035965847939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3087383721472095908927837 1157768895552035965847939)
            ·
              refine ⟨1736653343328053948771909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1157768895552035965847939 1736653343328053948771909)
              ·
                refine ⟨325622501874010115394733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1736653343328053948771909 325622501874010115394733)
                ·
                  refine ⟨122108438202753793273025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 325622501874010115394733 122108438202753793273025)
                  ·
                    rfl

theorem cell20_267531_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 3, 1, 4, 3].length) (baseStart_267531 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_267531 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_267531 prefixEnd_267531 := by exact prefixLift 267531
  have htrace : WordTrace (prefixWord ++ tailWord_267531) baseStart_267531 baseEnd_267531 := by
    simpa [prefixWord, tailWord_267531, baseEnd_267531] using wordTrace_append hprefix tailTrace_267531
  have hstable : (prefixWord ++ tailWord_267531).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_267531).length < 2 ^ (prefixWord ++ tailWord_267531).sum := by decide
  have hdescent : baseEnd_267531 < baseStart_267531 := by decide
  rcases family_descends (prefixWord ++ tailWord_267531) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_267534 : List Nat := [4, 1, 1, 2, 1, 4, 1, 4, 2]
def baseStart_267534 : Nat := 118140960795 + 267534 * 2 ^ 59
def prefixEnd_267534 : Nat := 4983230072969 + 3 ^ 40 * 267534 * 2
def baseEnd_267534 : Nat := 122109807484499116173013

theorem tailTrace_267534 : CollatzResearch.WordTrace tailWord_267534 prefixEnd_267534 122109807484499116173013 := by
  unfold tailWord_267534
  simp only [CollatzResearch.WordTrace]
  refine ⟨1219720826597185501831207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 6505177741851656009766437 1219720826597185501831207)
  ·
    refine ⟨1829581239895778252746811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1219720826597185501831207 1829581239895778252746811)
    ·
      refine ⟨2744371859843667379120217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1829581239895778252746811 2744371859843667379120217)
      ·
        refine ⟨2058278894882750534340163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2744371859843667379120217 2058278894882750534340163)
        ·
          refine ⟨3087418342324125801510245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2058278894882750534340163 3087418342324125801510245)
          ·
            refine ⟨578890939185773587783171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3087418342324125801510245 578890939185773587783171)
            ·
              refine ⟨868336408778660381674757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 578890939185773587783171 868336408778660381674757)
              ·
                refine ⟨162813076645998821564017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 868336408778660381674757 162813076645998821564017)
                ·
                  refine ⟨122109807484499116173013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 162813076645998821564017 122109807484499116173013)
                  ·
                    rfl

theorem cell20_267534_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 4, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 4, 1, 4, 2].length) (baseStart_267534 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_267534 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_267534 prefixEnd_267534 := by exact prefixLift 267534
  have htrace : WordTrace (prefixWord ++ tailWord_267534) baseStart_267534 baseEnd_267534 := by
    simpa [prefixWord, tailWord_267534, baseEnd_267534] using wordTrace_append hprefix tailTrace_267534
  have hstable : (prefixWord ++ tailWord_267534).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_267534).length < 2 ^ (prefixWord ++ tailWord_267534).sum := by decide
  have hdescent : baseEnd_267534 < baseStart_267534 := by decide
  rcases family_descends (prefixWord ++ tailWord_267534) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_267583 : List Nat := [1, 1, 2, 2, 4, 3, 7]
def baseStart_267583 : Nat := 118140960795 + 267583 * 2 ^ 59
def prefixEnd_267583 : Nat := 4983230072969 + 3 ^ 40 * 267583 * 2
def baseEnd_267583 : Nat := 13570241379963635948831

theorem tailTrace_267583 : CollatzResearch.WordTrace tailWord_267583 prefixEnd_267583 13570241379963635948831 := by
  unfold tailWord_267583
  simp only [CollatzResearch.WordTrace]
  refine ⟨9759553789599965383183403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6506369193066643588788935 9759553789599965383183403)
  ·
    refine ⟨14639330684399948074775105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9759553789599965383183403 14639330684399948074775105)
    ·
      refine ⟨10979498013299961056081329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14639330684399948074775105 10979498013299961056081329)
      ·
        refine ⟨8234623509974970792060997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10979498013299961056081329 8234623509974970792060997)
        ·
          refine ⟨1543991908120307023511437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 8234623509974970792060997 1543991908120307023511437)
          ·
            refine ⟨578996965545115133816789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1543991908120307023511437 578996965545115133816789)
            ·
              refine ⟨13570241379963635948831, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 578996965545115133816789 13570241379963635948831)
              ·
                rfl

theorem cell20_267583_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 3, 7].length) (baseStart_267583 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_267583 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_267583 prefixEnd_267583 := by exact prefixLift 267583
  have htrace : WordTrace (prefixWord ++ tailWord_267583) baseStart_267583 baseEnd_267583 := by
    simpa [prefixWord, tailWord_267583, baseEnd_267583] using wordTrace_append hprefix tailTrace_267583
  have hstable : (prefixWord ++ tailWord_267583).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_267583).length < 2 ^ (prefixWord ++ tailWord_267583).sum := by decide
  have hdescent : baseEnd_267583 < baseStart_267583 := by decide
  rcases family_descends (prefixWord ++ tailWord_267583) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_267593 : List Nat := [1, 2, 1, 1, 2, 3, 4, 4, 2]
def baseStart_267593 : Nat := 118140960795 + 267593 * 2 ^ 59
def prefixEnd_267593 : Nat := 4983230072969 + 3 ^ 40 * 267593 * 2
def baseEnd_267593 : Nat := 122136736692157133206105

theorem tailTrace_267593 : CollatzResearch.WordTrace tailWord_267593 prefixEnd_267593 122136736692157133206105 := by
  unfold tailWord_267593
  simp only [CollatzResearch.WordTrace]
  refine ⟨9759918519563737091047433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6506612346375824727364955 9759918519563737091047433)
  ·
    refine ⟨7319938889672802818285575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9759918519563737091047433 7319938889672802818285575)
    ·
      refine ⟨10979908334509204227428363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7319938889672802818285575 10979908334509204227428363)
      ·
        refine ⟨16469862501763806341142545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10979908334509204227428363 16469862501763806341142545)
        ·
          refine ⟨12352396876322854755856909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16469862501763806341142545 12352396876322854755856909)
          ·
            refine ⟨4632148828621070533446341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12352396876322854755856909 4632148828621070533446341)
            ·
              refine ⟨868527905366450725021189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4632148828621070533446341 868527905366450725021189)
              ·
                refine ⟨162848982256209510941473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 868527905366450725021189 162848982256209510941473)
                ·
                  refine ⟨122136736692157133206105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 162848982256209510941473 122136736692157133206105)
                  ·
                    rfl

theorem cell20_267593_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 4, 4, 2].length) (baseStart_267593 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_267593 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_267593 prefixEnd_267593 := by exact prefixLift 267593
  have htrace : WordTrace (prefixWord ++ tailWord_267593) baseStart_267593 baseEnd_267593 := by
    simpa [prefixWord, tailWord_267593, baseEnd_267593] using wordTrace_append hprefix tailTrace_267593
  have hstable : (prefixWord ++ tailWord_267593).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_267593).length < 2 ^ (prefixWord ++ tailWord_267593).sum := by decide
  have hdescent : baseEnd_267593 < baseStart_267593 := by decide
  rcases family_descends (prefixWord ++ tailWord_267593) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_267621 : List Nat := [1, 3, 1, 3, 1, 2, 3, 6]
def baseStart_267621 : Nat := 118140960795 + 267621 * 2 ^ 59
def prefixEnd_267621 : Nat := 4983230072969 + 3 ^ 40 * 267621 * 2
def baseEnd_267621 : Nat := 40716505551704493424219

theorem tailTrace_267621 : CollatzResearch.WordTrace tailWord_267621 prefixEnd_267621 40716505551704493424219 := by
  unfold tailWord_267621
  simp only [CollatzResearch.WordTrace]
  refine ⟨9760939763462297873066717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6507293175641531915377811 9760939763462297873066717)
  ·
    refine ⟨3660352411298361702400019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9760939763462297873066717 3660352411298361702400019)
    ·
      refine ⟨5490528616947542553600029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3660352411298361702400019 5490528616947542553600029)
      ·
        refine ⟨2058948231355328457600011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5490528616947542553600029 2058948231355328457600011)
        ·
          refine ⟨3088422347032992686400017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2058948231355328457600011 3088422347032992686400017)
          ·
            refine ⟨2316316760274744514800013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3088422347032992686400017 2316316760274744514800013)
            ·
              refine ⟨868618785103029193050005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2316316760274744514800013 868618785103029193050005)
              ·
                refine ⟨40716505551704493424219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 868618785103029193050005 40716505551704493424219)
                ·
                  rfl

theorem cell20_267621_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 3, 6].length) (baseStart_267621 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_267621 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_267621 prefixEnd_267621 := by exact prefixLift 267621
  have htrace : WordTrace (prefixWord ++ tailWord_267621) baseStart_267621 baseEnd_267621 := by
    simpa [prefixWord, tailWord_267621, baseEnd_267621] using wordTrace_append hprefix tailTrace_267621
  have hstable : (prefixWord ++ tailWord_267621).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_267621).length < 2 ^ (prefixWord ++ tailWord_267621).sum := by decide
  have hdescent : baseEnd_267621 < baseStart_267621 := by decide
  rcases family_descends (prefixWord ++ tailWord_267621) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_267645 : List Nat := [1, 4, 1, 1, 2, 2, 2, 4, 3]
def baseStart_267645 : Nat := 118140960795 + 267645 * 2 ^ 59
def prefixEnd_267645 : Nat := 4983230072969 + 3 ^ 40 * 267645 * 2
def baseEnd_267645 : Nat := 122160470909076063472559

theorem tailTrace_267645 : CollatzResearch.WordTrace tailWord_267645 prefixEnd_267645 122160470909076063472559 := by
  unfold tailWord_267645
  simp only [CollatzResearch.WordTrace]
  refine ⟨9761815115375349971940389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6507876743583566647960259 9761815115375349971940389)
  ·
    refine ⟨1830340334132878119738823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 9761815115375349971940389 1830340334132878119738823)
    ·
      refine ⟨2745510501199317179608235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1830340334132878119738823 2745510501199317179608235)
      ·
        refine ⟨4118265751798975769412353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2745510501199317179608235 4118265751798975769412353)
        ·
          refine ⟨3088699313849231827059265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4118265751798975769412353 3088699313849231827059265)
          ·
            refine ⟨2316524485386923870294449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3088699313849231827059265 2316524485386923870294449)
            ·
              refine ⟨1737393364040192902720837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2316524485386923870294449 1737393364040192902720837)
              ·
                refine ⟨325761255757536169260157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1737393364040192902720837 325761255757536169260157)
                ·
                  refine ⟨122160470909076063472559, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 325761255757536169260157 122160470909076063472559)
                  ·
                    rfl

theorem cell20_267645_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 2, 4, 3].length) (baseStart_267645 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_267645 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_267645 prefixEnd_267645 := by exact prefixLift 267645
  have htrace : WordTrace (prefixWord ++ tailWord_267645) baseStart_267645 baseEnd_267645 := by
    simpa [prefixWord, tailWord_267645, baseEnd_267645] using wordTrace_append hprefix tailTrace_267645
  have hstable : (prefixWord ++ tailWord_267645).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_267645).length < 2 ^ (prefixWord ++ tailWord_267645).sum := by decide
  have hdescent : baseEnd_267645 < baseStart_267645 := by decide
  rcases family_descends (prefixWord ++ tailWord_267645) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_267659 : List Nat := [1, 1, 1, 1, 4, 3, 4, 5]
def baseStart_267659 : Nat := 118140960795 + 267659 * 2 ^ 59
def prefixEnd_267659 : Nat := 4983230072969 + 3 ^ 40 * 267659 * 2
def baseEnd_267659 : Nat := 40722286963518079001945

theorem tailTrace_267659 : CollatzResearch.WordTrace tailWord_267659 prefixEnd_267659 40722286963518079001945 := by
  unfold tailWord_267659
  simp only [CollatzResearch.WordTrace]
  refine ⟨9762325737324630362950031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6508217158216420241966687 9762325737324630362950031)
  ·
    refine ⟨14643488605986945544425047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9762325737324630362950031 14643488605986945544425047)
    ·
      refine ⟨21965232908980418316637571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14643488605986945544425047 21965232908980418316637571)
      ·
        refine ⟨32947849363470627474956357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21965232908980418316637571 32947849363470627474956357)
        ·
          refine ⟨6177721755650742651554317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 32947849363470627474956357 6177721755650742651554317)
          ·
            refine ⟨2316645658369028494332869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6177721755650742651554317 2316645658369028494332869)
            ·
              refine ⟨434371060944192842687413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2316645658369028494332869 434371060944192842687413)
              ·
                refine ⟨40722286963518079001945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 434371060944192842687413 40722286963518079001945)
                ·
                  rfl

theorem cell20_267659_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 4, 5].length) (baseStart_267659 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_267659 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_267659 prefixEnd_267659 := by exact prefixLift 267659
  have htrace : WordTrace (prefixWord ++ tailWord_267659) baseStart_267659 baseEnd_267659 := by
    simpa [prefixWord, tailWord_267659, baseEnd_267659] using wordTrace_append hprefix tailTrace_267659
  have hstable : (prefixWord ++ tailWord_267659).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_267659).length < 2 ^ (prefixWord ++ tailWord_267659).sum := by decide
  have hdescent : baseEnd_267659 < baseStart_267659 := by decide
  rcases family_descends (prefixWord ++ tailWord_267659) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_267704 : List Nat := [2, 1, 2, 1, 2, 2, 2, 3, 5]
def baseStart_267704 : Nat := 118140960795 + 267704 * 2 ^ 59
def prefixEnd_267704 : Nat := 4983230072969 + 3 ^ 40 * 267704 * 2
def baseEnd_267704 : Nat := 122187400116734080505651

theorem tailTrace_267704 : CollatzResearch.WordTrace tailWord_267704 prefixEnd_267704 122187400116734080505651 := by
  unfold tailWord_267704
  simp only [CollatzResearch.WordTrace]
  refine ⟨4881983511080801524169083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6509311348107735365558777 4881983511080801524169083)
  ·
    refine ⟨7322975266621202286253625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4881983511080801524169083 7322975266621202286253625)
    ·
      refine ⟨5492231449965901714690219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7322975266621202286253625 5492231449965901714690219)
      ·
        refine ⟨8238347174948852572035329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5492231449965901714690219 8238347174948852572035329)
        ·
          refine ⟨6178760381211639429026497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8238347174948852572035329 6178760381211639429026497)
          ·
            refine ⟨4634070285908729571769873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6178760381211639429026497 4634070285908729571769873)
            ·
              refine ⟨3475552714431547178827405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4634070285908729571769873 3475552714431547178827405)
              ·
                refine ⟨1303332267911830192060277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3475552714431547178827405 1303332267911830192060277)
                ·
                  refine ⟨122187400116734080505651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1303332267911830192060277 122187400116734080505651)
                  ·
                    rfl

theorem cell20_267704_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 2, 3, 5].length) (baseStart_267704 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_267704 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_267704 prefixEnd_267704 := by exact prefixLift 267704
  have htrace : WordTrace (prefixWord ++ tailWord_267704) baseStart_267704 baseEnd_267704 := by
    simpa [prefixWord, tailWord_267704, baseEnd_267704] using wordTrace_append hprefix tailTrace_267704
  have hstable : (prefixWord ++ tailWord_267704).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_267704).length < 2 ^ (prefixWord ++ tailWord_267704).sum := by decide
  have hdescent : baseEnd_267704 < baseStart_267704 := by decide
  rcases family_descends (prefixWord ++ tailWord_267704) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_267711 : List Nat := [1, 1, 2, 2, 2, 1, 1, 2, 8]
def baseStart_267711 : Nat := 118140960795 + 267711 * 2 ^ 59
def prefixEnd_267711 : Nat := 4983230072969 + 3 ^ 40 * 267711 * 2
def baseEnd_267711 : Nat := 122190595107473167272289

theorem tailTrace_267711 : CollatzResearch.WordTrace tailWord_267711 prefixEnd_267711 122190595107473167272289 := by
  unfold tailWord_267711
  simp only [CollatzResearch.WordTrace]
  refine ⟨9764222333136243243842987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6509481555424162162561991 9764222333136243243842987)
  ·
    refine ⟨14646333499704364865764481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9764222333136243243842987 14646333499704364865764481)
    ·
      refine ⟨10984750124778273649323361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14646333499704364865764481 10984750124778273649323361)
      ·
        refine ⟨8238562593583705236992521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10984750124778273649323361 8238562593583705236992521)
        ·
          refine ⟨6178921945187778927744391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8238562593583705236992521 6178921945187778927744391)
          ·
            refine ⟨9268382917781668391616587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6178921945187778927744391 9268382917781668391616587)
            ·
              refine ⟨13902574376672502587424881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9268382917781668391616587 13902574376672502587424881)
              ·
                refine ⟨10426930782504376940568661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13902574376672502587424881 10426930782504376940568661)
                ·
                  refine ⟨122190595107473167272289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 10426930782504376940568661 122190595107473167272289)
                  ·
                    rfl

theorem cell20_267711_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 1, 2, 8].length) (baseStart_267711 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_267711 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_267711 prefixEnd_267711 := by exact prefixLift 267711
  have htrace : WordTrace (prefixWord ++ tailWord_267711) baseStart_267711 baseEnd_267711 := by
    simpa [prefixWord, tailWord_267711, baseEnd_267711] using wordTrace_append hprefix tailTrace_267711
  have hstable : (prefixWord ++ tailWord_267711).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_267711).length < 2 ^ (prefixWord ++ tailWord_267711).sum := by decide
  have hdescent : baseEnd_267711 < baseStart_267711 := by decide
  rcases family_descends (prefixWord ++ tailWord_267711) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_267745 : List Nat := [1, 2, 3, 1, 2, 3, 1, 5, 2]
def baseStart_267745 : Nat := 118140960795 + 267745 * 2 ^ 59
def prefixEnd_267745 : Nat := 4983230072969 + 3 ^ 40 * 267745 * 2
def baseEnd_267745 : Nat := 122206113633920160138817

theorem tailTrace_267745 : CollatzResearch.WordTrace tailWord_267745 prefixEnd_267745 122206113633920160138817 := by
  unfold tailWord_267745
  simp only [CollatzResearch.WordTrace]
  refine ⟨9765462415013067050580689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6510308276675378033720459 9765462415013067050580689)
  ·
    refine ⟨7324096811259800287935517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9765462415013067050580689 7324096811259800287935517)
    ·
      refine ⟨2746536304222425107975819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7324096811259800287935517 2746536304222425107975819)
      ·
        refine ⟨4119804456333637661963729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2746536304222425107975819 4119804456333637661963729)
        ·
          refine ⟨3089853342250228246472797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4119804456333637661963729 3089853342250228246472797)
          ·
            refine ⟨1158695003343835592427299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3089853342250228246472797 1158695003343835592427299)
            ·
              refine ⟨1738042505015753388640949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1158695003343835592427299 1738042505015753388640949)
              ·
                refine ⟨162941484845226880185089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1738042505015753388640949 162941484845226880185089)
                ·
                  refine ⟨122206113633920160138817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 162941484845226880185089 122206113633920160138817)
                  ·
                    rfl

theorem cell20_267745_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 3, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 3, 1, 5, 2].length) (baseStart_267745 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_267745 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_267745 prefixEnd_267745 := by exact prefixLift 267745
  have htrace : WordTrace (prefixWord ++ tailWord_267745) baseStart_267745 baseEnd_267745 := by
    simpa [prefixWord, tailWord_267745, baseEnd_267745] using wordTrace_append hprefix tailTrace_267745
  have hstable : (prefixWord ++ tailWord_267745).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_267745).length < 2 ^ (prefixWord ++ tailWord_267745).sum := by decide
  have hdescent : baseEnd_267745 < baseStart_267745 := by decide
  rcases family_descends (prefixWord ++ tailWord_267745) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_267759 : List Nat := [1, 1, 2, 1, 4, 1, 5, 2, 3]
def baseStart_267759 : Nat := 118140960795 + 267759 * 2 ^ 59
def prefixEnd_267759 : Nat := 4983230072969 + 3 ^ 40 * 267759 * 2
def baseEnd_267759 : Nat := 122212503615398333672093

theorem tailTrace_267759 : CollatzResearch.WordTrace tailWord_267759 prefixEnd_267759 122212503615398333672093 := by
  unfold tailWord_267759
  simp only [CollatzResearch.WordTrace]
  refine ⟨9765973036962347441590331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6510648691308231627726887 9765973036962347441590331)
  ·
    refine ⟨14648959555443521162385497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9765973036962347441590331 14648959555443521162385497)
    ·
      refine ⟨10986719666582640871789123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14648959555443521162385497 10986719666582640871789123)
      ·
        refine ⟨16480079499873961307683685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10986719666582640871789123 16480079499873961307683685)
        ·
          refine ⟨3090014906226367745190691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 16480079499873961307683685 3090014906226367745190691)
          ·
            refine ⟨4635022359339551617786037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3090014906226367745190691 4635022359339551617786037)
            ·
              refine ⟨434533346188082964167441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 4635022359339551617786037 434533346188082964167441)
              ·
                refine ⟨325900009641062223125581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 434533346188082964167441 325900009641062223125581)
                ·
                  refine ⟨122212503615398333672093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 325900009641062223125581 122212503615398333672093)
                  ·
                    rfl

theorem cell20_267759_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 5, 2, 3].length) (baseStart_267759 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_267759 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_267759 prefixEnd_267759 := by exact prefixLift 267759
  have htrace : WordTrace (prefixWord ++ tailWord_267759) baseStart_267759 baseEnd_267759 := by
    simpa [prefixWord, tailWord_267759, baseEnd_267759] using wordTrace_append hprefix tailTrace_267759
  have hstable : (prefixWord ++ tailWord_267759).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_267759).length < 2 ^ (prefixWord ++ tailWord_267759).sum := by decide
  have hdescent : baseEnd_267759 < baseStart_267759 := by decide
  rcases family_descends (prefixWord ++ tailWord_267759) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_267762 : List Nat := [3, 2, 1, 4, 1, 1, 2, 4, 2]
def baseStart_267762 : Nat := 118140960795 + 267762 * 2 ^ 59
def prefixEnd_267762 : Nat := 4983230072969 + 3 ^ 40 * 267762 * 2
def baseEnd_267762 : Nat := 122213872897143656572081

theorem tailTrace_267762 : CollatzResearch.WordTrace tailWord_267762 prefixEnd_267762 122213872897143656572081 := by
  unfold tailWord_267762
  simp only [CollatzResearch.WordTrace]
  refine ⟨2441520613987869738487385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6510721637300985969299693 2441520613987869738487385)
  ·
    refine ⟨1831140460490902303865539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2441520613987869738487385 1831140460490902303865539)
    ·
      refine ⟨2746710690736353455798309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1831140460490902303865539 2746710690736353455798309)
      ·
        refine ⟨515008254513066272962183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2746710690736353455798309 515008254513066272962183)
        ·
          refine ⟨772512381769599409443275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 515008254513066272962183 772512381769599409443275)
          ·
            refine ⟨1158768572654399114164913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 772512381769599409443275 1158768572654399114164913)
            ·
              refine ⟨869076429490799335623685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1158768572654399114164913 869076429490799335623685)
              ·
                refine ⟨162951830529524875429441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 869076429490799335623685 162951830529524875429441)
                ·
                  refine ⟨122213872897143656572081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 162951830529524875429441 122213872897143656572081)
                  ·
                    rfl

theorem cell20_267762_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 1, 2, 4, 2].length) (baseStart_267762 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_267762 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_267762 prefixEnd_267762 := by exact prefixLift 267762
  have htrace : WordTrace (prefixWord ++ tailWord_267762) baseStart_267762 baseEnd_267762 := by
    simpa [prefixWord, tailWord_267762, baseEnd_267762] using wordTrace_append hprefix tailTrace_267762
  have hstable : (prefixWord ++ tailWord_267762).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_267762).length < 2 ^ (prefixWord ++ tailWord_267762).sum := by decide
  have hdescent : baseEnd_267762 < baseStart_267762 := by decide
  rcases family_descends (prefixWord ++ tailWord_267762) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_267782 : List Nat := [6, 2, 1, 1, 2, 2, 2, 4]
def baseStart_267782 : Nat := 118140960795 + 267782 * 2 ^ 59
def prefixEnd_267782 : Nat := 4983230072969 + 3 ^ 40 * 267782 * 2
def baseEnd_267782 : Nat := 40741000480704158635111

theorem tailTrace_267782 : CollatzResearch.WordTrace tailWord_267782 prefixEnd_267782 40741000480704158635111 := by
  unfold tailWord_267782
  simp only [CollatzResearch.WordTrace]
  refine ⟨305212872371219449052425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 6511207943919348246451733 305212872371219449052425)
  ·
    refine ⟨228909654278414586789319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 305212872371219449052425 228909654278414586789319)
    ·
      refine ⟨343364481417621880183979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 228909654278414586789319 343364481417621880183979)
      ·
        refine ⟨515046722126432820275969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 343364481417621880183979 515046722126432820275969)
        ·
          refine ⟨386285041594824615206977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 515046722126432820275969 386285041594824615206977)
          ·
            refine ⟨289713781196118461405233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 386285041594824615206977 289713781196118461405233)
            ·
              refine ⟨217285335897088846053925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 289713781196118461405233 217285335897088846053925)
              ·
                refine ⟨40741000480704158635111, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 217285335897088846053925 40741000480704158635111)
                ·
                  rfl

theorem cell20_267782_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 2, 2, 2, 4].length) (baseStart_267782 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_267782 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_267782 prefixEnd_267782 := by exact prefixLift 267782
  have htrace : WordTrace (prefixWord ++ tailWord_267782) baseStart_267782 baseEnd_267782 := by
    simpa [prefixWord, tailWord_267782, baseEnd_267782] using wordTrace_append hprefix tailTrace_267782
  have hstable : (prefixWord ++ tailWord_267782).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_267782).length < 2 ^ (prefixWord ++ tailWord_267782).sum := by decide
  have hdescent : baseEnd_267782 < baseStart_267782 := by decide
  rcases family_descends (prefixWord ++ tailWord_267782) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_267790 : List Nat := [4, 1, 1, 2, 4, 1, 1, 6]
def baseStart_267790 : Nat := 118140960795 + 267790 * 2 ^ 59
def prefixEnd_267790 : Nat := 4983230072969 + 3 ^ 40 * 267790 * 2
def baseEnd_267790 : Nat := 40742217620033334546211

theorem tailTrace_267790 : CollatzResearch.WordTrace tailWord_267790 prefixEnd_267790 40742217620033334546211 := by
  unfold tailWord_267790
  simp only [CollatzResearch.WordTrace]
  refine ⟨1220887962481254966996103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 6511402466566693157312549 1220887962481254966996103)
  ·
    refine ⟨1831331943721882450494155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1220887962481254966996103 1831331943721882450494155)
    ·
      refine ⟨2746997915582823675741233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1831331943721882450494155 2746997915582823675741233)
      ·
        refine ⟨2060248436687117756805925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2746997915582823675741233 2060248436687117756805925)
        ·
          refine ⟨386296581878834579401111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2060248436687117756805925 386296581878834579401111)
          ·
            refine ⟨579444872818251869101667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 386296581878834579401111 579444872818251869101667)
            ·
              refine ⟨869167309227377803652501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 579444872818251869101667 869167309227377803652501)
              ·
                refine ⟨40742217620033334546211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 869167309227377803652501 40742217620033334546211)
                ·
                  rfl

theorem cell20_267790_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 4, 1, 1, 6].length) (baseStart_267790 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_267790 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_267790 prefixEnd_267790 := by exact prefixLift 267790
  have htrace : WordTrace (prefixWord ++ tailWord_267790) baseStart_267790 baseEnd_267790 := by
    simpa [prefixWord, tailWord_267790, baseEnd_267790] using wordTrace_append hprefix tailTrace_267790
  have hstable : (prefixWord ++ tailWord_267790).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_267790).length < 2 ^ (prefixWord ++ tailWord_267790).sum := by decide
  have hdescent : baseEnd_267790 < baseStart_267790 := by decide
  rcases family_descends (prefixWord ++ tailWord_267790) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_267796 : List Nat := [2, 4, 3, 1, 2, 2, 1, 3, 2]
def baseStart_267796 : Nat := 118140960795 + 267796 * 2 ^ 59
def prefixEnd_267796 : Nat := 4983230072969 + 3 ^ 40 * 267796 * 2
def baseEnd_267796 : Nat := 122229391423590649438609

theorem tailTrace_267796 : CollatzResearch.WordTrace tailWord_267796 prefixEnd_267796 122229391423590649438609 := by
  unfold tailWord_267796
  simp only [CollatzResearch.WordTrace]
  refine ⟨4883661268914151380343621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6511548358552201840458161 4883661268914151380343621)
  ·
    refine ⟨915686487921403383814429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 4883661268914151380343621 915686487921403383814429)
    ·
      refine ⟨343382432970526268930411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 915686487921403383814429 343382432970526268930411)
      ·
        refine ⟨515073649455789403395617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 343382432970526268930411 515073649455789403395617)
        ·
          refine ⟨386305237091842052546713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 515073649455789403395617 386305237091842052546713)
          ·
            refine ⟨289728927818881539410035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 386305237091842052546713 289728927818881539410035)
            ·
              refine ⟨434593391728322309115053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 289728927818881539410035 434593391728322309115053)
              ·
                refine ⟨162972521898120865918145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 434593391728322309115053 162972521898120865918145)
                ·
                  refine ⟨122229391423590649438609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 162972521898120865918145 122229391423590649438609)
                  ·
                    rfl

theorem cell20_267796_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 2, 2, 1, 3, 2].length) (baseStart_267796 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_267796 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_267796 prefixEnd_267796 := by exact prefixLift 267796
  have htrace : WordTrace (prefixWord ++ tailWord_267796) baseStart_267796 baseEnd_267796 := by
    simpa [prefixWord, tailWord_267796, baseEnd_267796] using wordTrace_append hprefix tailTrace_267796
  have hstable : (prefixWord ++ tailWord_267796).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_267796).length < 2 ^ (prefixWord ++ tailWord_267796).sum := by decide
  have hdescent : baseEnd_267796 < baseStart_267796 := by decide
  rcases family_descends (prefixWord ++ tailWord_267796) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_267862 : List Nat := [5, 2, 2, 2, 2, 7]
def baseStart_267862 : Nat := 118140960795 + 267862 * 2 ^ 59
def prefixEnd_267862 : Nat := 4983230072969 + 3 ^ 40 * 267862 * 2
def baseEnd_267862 : Nat := 4528130208221768638457

theorem tailTrace_267862 : CollatzResearch.WordTrace tailWord_267862 prefixEnd_267862 4528130208221768638457 := by
  unfold tailWord_267862
  simp only [CollatzResearch.WordTrace]
  refine ⟨610608109724324752036865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 6513153170392797355059893 610608109724324752036865)
  ·
    refine ⟨457956082293243564027649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 610608109724324752036865 457956082293243564027649)
    ·
      refine ⟨343467061719932673020737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 457956082293243564027649 343467061719932673020737)
      ·
        refine ⟨257600296289949504765553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 343467061719932673020737 257600296289949504765553)
        ·
          refine ⟨193200222217462128574165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 257600296289949504765553 193200222217462128574165)
          ·
            refine ⟨4528130208221768638457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 193200222217462128574165 4528130208221768638457)
            ·
              rfl

theorem cell20_267862_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 2, 2, 7].length) (baseStart_267862 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_267862 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_267862 prefixEnd_267862 := by exact prefixLift 267862
  have htrace : WordTrace (prefixWord ++ tailWord_267862) baseStart_267862 baseEnd_267862 := by
    simpa [prefixWord, tailWord_267862, baseEnd_267862] using wordTrace_append hprefix tailTrace_267862
  have hstable : (prefixWord ++ tailWord_267862).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_267862).length < 2 ^ (prefixWord ++ tailWord_267862).sum := by decide
  have hdescent : baseEnd_267862 < baseStart_267862 := by decide
  rcases family_descends (prefixWord ++ tailWord_267862) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_267873 : List Nat := [1, 2, 3, 1, 1, 3, 4, 2, 3]
def baseStart_267873 : Nat := 118140960795 + 267873 * 2 ^ 59
def prefixEnd_267873 : Nat := 4983230072969 + 3 ^ 40 * 267873 * 2
def baseEnd_267873 : Nat := 122264536321720603871627

theorem tailTrace_267873 : CollatzResearch.WordTrace tailWord_267873 prefixEnd_267873 122264536321720603871627 := by
  unfold tailWord_267873
  simp only [CollatzResearch.WordTrace]
  refine ⟨9770130958549344911240273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6513420639032896607493515 9770130958549344911240273)
  ·
    refine ⟨7327598218912008683430205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9770130958549344911240273 7327598218912008683430205)
    ·
      refine ⟨2747849332092003256286327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7327598218912008683430205 2747849332092003256286327)
      ·
        refine ⟨4121773998138004884429491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2747849332092003256286327 4121773998138004884429491)
        ·
          refine ⟨6182660997207007326644237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4121773998138004884429491 6182660997207007326644237)
          ·
            refine ⟨2318497873952627747491589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6182660997207007326644237 2318497873952627747491589)
            ·
              refine ⟨434718351366117702654673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2318497873952627747491589 434718351366117702654673)
              ·
                refine ⟨326038763524588276991005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 434718351366117702654673 326038763524588276991005)
                ·
                  refine ⟨122264536321720603871627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 326038763524588276991005 122264536321720603871627)
                  ·
                    rfl

theorem cell20_267873_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 4, 2, 3].length) (baseStart_267873 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_267873 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_267873 prefixEnd_267873 := by exact prefixLift 267873
  have htrace : WordTrace (prefixWord ++ tailWord_267873) baseStart_267873 baseEnd_267873 := by
    simpa [prefixWord, tailWord_267873, baseEnd_267873] using wordTrace_append hprefix tailTrace_267873
  have hstable : (prefixWord ++ tailWord_267873).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_267873).length < 2 ^ (prefixWord ++ tailWord_267873).sum := by decide
  have hdescent : baseEnd_267873 < baseStart_267873 := by decide
  rcases family_descends (prefixWord ++ tailWord_267873) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_267876 : List Nat := [2, 3, 1, 1, 2, 3, 4, 2, 2]
def baseStart_267876 : Nat := 118140960795 + 267876 * 2 ^ 59
def prefixEnd_267876 : Nat := 4983230072969 + 3 ^ 40 * 267876 * 2
def baseEnd_267876 : Nat := 122265905603465926771615

theorem tailTrace_267876 : CollatzResearch.WordTrace tailWord_267876 prefixEnd_267876 122265905603465926771615 := by
  unfold tailWord_267876
  simp only [CollatzResearch.WordTrace]
  refine ⟨4885120188769238211799741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6513493585025650949066321 4885120188769238211799741)
  ·
    refine ⟨1831920070788464329424903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4885120188769238211799741 1831920070788464329424903)
    ·
      refine ⟨2747880106182696494137355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1831920070788464329424903 2747880106182696494137355)
      ·
        refine ⟨4121820159274044741206033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2747880106182696494137355 4121820159274044741206033)
        ·
          refine ⟨3091365119455533555904525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4121820159274044741206033 3091365119455533555904525)
          ·
            refine ⟨1159261919795825083464197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3091365119455533555904525 1159261919795825083464197)
            ·
              refine ⟨217361609961717203149537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1159261919795825083464197 217361609961717203149537)
              ·
                refine ⟨163021207471287902362153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 217361609961717203149537 163021207471287902362153)
                ·
                  refine ⟨122265905603465926771615, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 163021207471287902362153 122265905603465926771615)
                  ·
                    rfl

theorem cell20_267876_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 3, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 3, 4, 2, 2].length) (baseStart_267876 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_267876 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_267876 prefixEnd_267876 := by exact prefixLift 267876
  have htrace : WordTrace (prefixWord ++ tailWord_267876) baseStart_267876 baseEnd_267876 := by
    simpa [prefixWord, tailWord_267876, baseEnd_267876] using wordTrace_append hprefix tailTrace_267876
  have hstable : (prefixWord ++ tailWord_267876).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_267876).length < 2 ^ (prefixWord ++ tailWord_267876).sum := by decide
  have hdescent : baseEnd_267876 < baseStart_267876 := by decide
  rcases family_descends (prefixWord ++ tailWord_267876) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_267914 : List Nat := [3, 1, 2, 3, 2, 2, 2, 3, 2]
def baseStart_267914 : Nat := 118140960795 + 267914 * 2 ^ 59
def prefixEnd_267914 : Nat := 4983230072969 + 3 ^ 40 * 267914 * 2
def baseEnd_267914 : Nat := 122283249838906683504793

theorem tailTrace_267914 : CollatzResearch.WordTrace tailWord_267914 prefixEnd_267914 122283249838906683504793 := by
  unfold tailWord_267914
  simp only [CollatzResearch.WordTrace]
  refine ⟨2442906587850202228370699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6514417567600539275655197 2442906587850202228370699)
  ·
    refine ⟨3664359881775303342556049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2442906587850202228370699 3664359881775303342556049)
    ·
      refine ⟨2748269911331477506917037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3664359881775303342556049 2748269911331477506917037)
      ·
        refine ⟨1030601216749304065093889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2748269911331477506917037 1030601216749304065093889)
        ·
          refine ⟨772950912561978048820417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1030601216749304065093889 772950912561978048820417)
          ·
            refine ⟨579713184421483536615313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 772950912561978048820417 579713184421483536615313)
            ·
              refine ⟨434784888316112652461485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 579713184421483536615313 434784888316112652461485)
              ·
                refine ⟨163044333118542244673057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 434784888316112652461485 163044333118542244673057)
                ·
                  refine ⟨122283249838906683504793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 163044333118542244673057 122283249838906683504793)
                  ·
                    rfl

theorem cell20_267914_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 2, 2, 3, 2].length) (baseStart_267914 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_267914 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_267914 prefixEnd_267914 := by exact prefixLift 267914
  have htrace : WordTrace (prefixWord ++ tailWord_267914) baseStart_267914 baseEnd_267914 := by
    simpa [prefixWord, tailWord_267914, baseEnd_267914] using wordTrace_append hprefix tailTrace_267914
  have hstable : (prefixWord ++ tailWord_267914).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_267914).length < 2 ^ (prefixWord ++ tailWord_267914).sum := by decide
  have hdescent : baseEnd_267914 < baseStart_267914 := by decide
  rcases family_descends (prefixWord ++ tailWord_267914) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_267924 : List Nat := [2, 4, 2, 2, 3, 1, 1, 2, 3]
def baseStart_267924 : Nat := 118140960795 + 267924 * 2 ^ 59
def prefixEnd_267924 : Nat := 4983230072969 + 3 ^ 40 * 267924 * 2
def baseEnd_267924 : Nat := 122287814111391093171419

theorem tailTrace_267924 : CollatzResearch.WordTrace tailWord_267924 prefixEnd_267924 122287814111391093171419 := by
  unfold tailWord_267924
  simp only [CollatzResearch.WordTrace]
  refine ⟨4885995540682290310673413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6514660720909720414231217 4885995540682290310673413)
  ·
    refine ⟨916124163877929433251265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 4885995540682290310673413 916124163877929433251265)
    ·
      refine ⟨687093122908447074938449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 916124163877929433251265 687093122908447074938449)
      ·
        refine ⟨515319842181335306203837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 687093122908447074938449 515319842181335306203837)
        ·
          refine ⟨193244940818000739826439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 515319842181335306203837 193244940818000739826439)
          ·
            refine ⟨289867411227001109739659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 193244940818000739826439 289867411227001109739659)
            ·
              refine ⟨434801116840501664609489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 289867411227001109739659 434801116840501664609489)
              ·
                refine ⟨326100837630376248457117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 434801116840501664609489 326100837630376248457117)
                ·
                  refine ⟨122287814111391093171419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 326100837630376248457117 122287814111391093171419)
                  ·
                    rfl

theorem cell20_267924_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 3, 1, 1, 2, 3].length) (baseStart_267924 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_267924 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_267924 prefixEnd_267924 := by exact prefixLift 267924
  have htrace : WordTrace (prefixWord ++ tailWord_267924) baseStart_267924 baseEnd_267924 := by
    simpa [prefixWord, tailWord_267924, baseEnd_267924] using wordTrace_append hprefix tailTrace_267924
  have hstable : (prefixWord ++ tailWord_267924).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_267924).length < 2 ^ (prefixWord ++ tailWord_267924).sum := by decide
  have hdescent : baseEnd_267924 < baseStart_267924 := by decide
  rcases family_descends (prefixWord ++ tailWord_267924) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_267928 : List Nat := [2, 1, 2, 4, 1, 4, 1, 2, 3]
def baseStart_267928 : Nat := 118140960795 + 267928 * 2 ^ 59
def prefixEnd_267928 : Nat := 4983230072969 + 3 ^ 40 * 267928 * 2
def baseEnd_267928 : Nat := 122289639820384857038069

theorem tailTrace_267928 : CollatzResearch.WordTrace tailWord_267928 prefixEnd_267928 122289639820384857038069 := by
  unfold tailWord_267928
  simp only [CollatzResearch.WordTrace]
  refine ⟨4886068486675044652246219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6514757982233392869661625 4886068486675044652246219)
  ·
    refine ⟨7329102730012566978369329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4886068486675044652246219 7329102730012566978369329)
    ·
      refine ⟨5496827047509425233776997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7329102730012566978369329 5496827047509425233776997)
      ·
        refine ⟨1030655071408017231333187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 5496827047509425233776997 1030655071408017231333187)
        ·
          refine ⟨1545982607112025846999781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1030655071408017231333187 1545982607112025846999781)
          ·
            refine ⟨289871738833504846312459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1545982607112025846999781 289871738833504846312459)
            ·
              refine ⟨434807608250257269468689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 289871738833504846312459 434807608250257269468689)
              ·
                refine ⟨326105706187692952101517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 434807608250257269468689 326105706187692952101517)
                ·
                  refine ⟨122289639820384857038069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 326105706187692952101517 122289639820384857038069)
                  ·
                    rfl

theorem cell20_267928_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 4, 1, 2, 3].length) (baseStart_267928 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_267928 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_267928 prefixEnd_267928 := by exact prefixLift 267928
  have htrace : WordTrace (prefixWord ++ tailWord_267928) baseStart_267928 baseEnd_267928 := by
    simpa [prefixWord, tailWord_267928, baseEnd_267928] using wordTrace_append hprefix tailTrace_267928
  have hstable : (prefixWord ++ tailWord_267928).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_267928).length < 2 ^ (prefixWord ++ tailWord_267928).sum := by decide
  have hdescent : baseEnd_267928 < baseStart_267928 := by decide
  rcases family_descends (prefixWord ++ tailWord_267928) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_267980 : List Nat := [2, 2, 1, 5, 2, 2, 6]
def baseStart_267980 : Nat := 118140960795 + 267980 * 2 ^ 59
def prefixEnd_267980 : Nat := 4983230072969 + 3 ^ 40 * 267980 * 2
def baseEnd_267980 : Nat := 13590374893033754144947

theorem tailTrace_267980 : CollatzResearch.WordTrace tailWord_267980 prefixEnd_267980 13590374893033754144947 := by
  unfold tailWord_267980
  simp only [CollatzResearch.WordTrace]
  refine ⟨4887016784580851092692697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6516022379441134790256929 4887016784580851092692697)
  ·
    refine ⟨3665262588435638319519523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4887016784580851092692697 3665262588435638319519523)
    ·
      refine ⟨5497893882653457479279285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3665262588435638319519523 5497893882653457479279285)
      ·
        refine ⟨515427551498761638682433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 5497893882653457479279285 515427551498761638682433)
        ·
          refine ⟨386570663624071229011825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 515427551498761638682433 386570663624071229011825)
          ·
            refine ⟨289927997718053421758869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 386570663624071229011825 289927997718053421758869)
            ·
              refine ⟨13590374893033754144947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 289927997718053421758869 13590374893033754144947)
              ·
                rfl

theorem cell20_267980_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 2, 2, 6].length) (baseStart_267980 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_267980 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_267980 prefixEnd_267980 := by exact prefixLift 267980
  have htrace : WordTrace (prefixWord ++ tailWord_267980) baseStart_267980 baseEnd_267980 := by
    simpa [prefixWord, tailWord_267980, baseEnd_267980] using wordTrace_append hprefix tailTrace_267980
  have hstable : (prefixWord ++ tailWord_267980).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_267980).length < 2 ^ (prefixWord ++ tailWord_267980).sum := by decide
  have hdescent : baseEnd_267980 < baseStart_267980 := by decide
  rcases family_descends (prefixWord ++ tailWord_267980) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_267994 : List Nat := [3, 1, 1, 2, 2, 3, 3, 1, 4]
def baseStart_267994 : Nat := 118140960795 + 267994 * 2 ^ 59
def prefixEnd_267994 : Nat := 4983230072969 + 3 ^ 40 * 267994 * 2
def baseEnd_267994 : Nat := 122319764018781960837799

theorem tailTrace_267994 : CollatzResearch.WordTrace tailWord_267994 prefixEnd_267994 122319764018781960837799 := by
  unfold tailWord_267994
  simp only [CollatzResearch.WordTrace]
  refine ⟨2443636047777745644098759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6516362794073988384263357 2443636047777745644098759)
  ·
    refine ⟨3665454071666618466148139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2443636047777745644098759 3665454071666618466148139)
    ·
      refine ⟨5498181107499927699222209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3665454071666618466148139 5498181107499927699222209)
      ·
        refine ⟨4123635830624945774416657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5498181107499927699222209 4123635830624945774416657)
        ·
          refine ⟨3092726872968709330812493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4123635830624945774416657 3092726872968709330812493)
          ·
            refine ⟨1159772577363265999054685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3092726872968709330812493 1159772577363265999054685)
            ·
              refine ⟨434914716511224749645507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1159772577363265999054685 434914716511224749645507)
              ·
                refine ⟨652372074766837124468261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 434914716511224749645507 652372074766837124468261)
                ·
                  refine ⟨122319764018781960837799, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 652372074766837124468261 122319764018781960837799)
                  ·
                    rfl

theorem cell20_267994_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 3, 3, 1, 4].length) (baseStart_267994 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_267994 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_267994 prefixEnd_267994 := by exact prefixLift 267994
  have htrace : WordTrace (prefixWord ++ tailWord_267994) baseStart_267994 baseEnd_267994 := by
    simpa [prefixWord, tailWord_267994, baseEnd_267994] using wordTrace_append hprefix tailTrace_267994
  have hstable : (prefixWord ++ tailWord_267994).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_267994).length < 2 ^ (prefixWord ++ tailWord_267994).sum := by decide
  have hdescent : baseEnd_267994 < baseStart_267994 := by decide
  rcases family_descends (prefixWord ++ tailWord_267994) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_267997 : List Nat := [1, 4, 3, 3, 1, 1, 2, 5]
def baseStart_267997 : Nat := 118140960795 + 267997 * 2 ^ 59
def prefixEnd_267997 : Nat := 4983230072969 + 3 ^ 40 * 267997 * 2
def baseEnd_267997 : Nat := 40773711100175761245929

theorem tailTrace_267997 : CollatzResearch.WordTrace tailWord_267997 prefixEnd_267997 40773711100175761245929 := by
  unfold tailWord_267997
  simp only [CollatzResearch.WordTrace]
  refine ⟨9774653610100114088754245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6516435740066742725836163 9774653610100114088754245)
  ·
    refine ⟨1832747551893771391641421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 9774653610100114088754245 1832747551893771391641421)
    ·
      refine ⟨687280331960164271865533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1832747551893771391641421 687280331960164271865533)
      ·
        refine ⟨257730124485061601949575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 687280331960164271865533 257730124485061601949575)
        ·
          refine ⟨386595186727592402924363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 257730124485061601949575 386595186727592402924363)
          ·
            refine ⟨579892780091388604386545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 386595186727592402924363 579892780091388604386545)
            ·
              refine ⟨434919585068541453289909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 579892780091388604386545 434919585068541453289909)
              ·
                refine ⟨40773711100175761245929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 434919585068541453289909 40773711100175761245929)
                ·
                  rfl

theorem cell20_267997_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 3, 1, 1, 2, 5].length) (baseStart_267997 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_267997 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_267997 prefixEnd_267997 := by exact prefixLift 267997
  have htrace : WordTrace (prefixWord ++ tailWord_267997) baseStart_267997 baseEnd_267997 := by
    simpa [prefixWord, tailWord_267997, baseEnd_267997] using wordTrace_append hprefix tailTrace_267997
  have hstable : (prefixWord ++ tailWord_267997).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_267997).length < 2 ^ (prefixWord ++ tailWord_267997).sum := by decide
  have hdescent : baseEnd_267997 < baseStart_267997 := by decide
  rcases family_descends (prefixWord ++ tailWord_267997) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_268015 : List Nat := [1, 1, 2, 1, 5, 1, 2, 1, 6]
def baseStart_268015 : Nat := 118140960795 + 268015 * 2 ^ 59
def prefixEnd_268015 : Nat := 4983230072969 + 3 ^ 40 * 268015 * 2
def baseEnd_268015 : Nat := 122329348990999221137713

theorem tailTrace_268015 : CollatzResearch.WordTrace tailWord_268015 prefixEnd_268015 122329348990999221137713 := by
  unfold tailWord_268015
  simp only [CollatzResearch.WordTrace]
  refine ⟨9775310124034903162909499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6516873416023268775272999 9775310124034903162909499)
  ·
    refine ⟨14662965186052354744364249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9775310124034903162909499 14662965186052354744364249)
    ·
      refine ⟨10997223889539266058273187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14662965186052354744364249 10997223889539266058273187)
      ·
        refine ⟨16495835834308899087409781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10997223889539266058273187 16495835834308899087409781)
        ·
          refine ⟨1546484609466459289444667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 16495835834308899087409781 1546484609466459289444667)
          ·
            refine ⟨2319726914199688934167001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1546484609466459289444667 2319726914199688934167001)
            ·
              refine ⟨1739795185649766700625251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2319726914199688934167001 1739795185649766700625251)
              ·
                refine ⟨2609692778474650050937877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1739795185649766700625251 2609692778474650050937877)
                ·
                  refine ⟨122329348990999221137713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2609692778474650050937877 122329348990999221137713)
                  ·
                    rfl

theorem cell20_268015_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 2, 1, 6].length) (baseStart_268015 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_268015 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_268015 prefixEnd_268015 := by exact prefixLift 268015
  have htrace : WordTrace (prefixWord ++ tailWord_268015) baseStart_268015 baseEnd_268015 := by
    simpa [prefixWord, tailWord_268015, baseEnd_268015] using wordTrace_append hprefix tailTrace_268015
  have hstable : (prefixWord ++ tailWord_268015).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_268015).length < 2 ^ (prefixWord ++ tailWord_268015).sum := by decide
  have hdescent : baseEnd_268015 < baseStart_268015 := by decide
  rcases family_descends (prefixWord ++ tailWord_268015) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_268039 : List Nat := [1, 1, 4, 4, 2, 8]
def baseStart_268039 : Nat := 118140960795 + 268039 * 2 ^ 59
def prefixEnd_268039 : Nat := 4983230072969 + 3 ^ 40 * 268039 * 2
def baseEnd_268039 : Nat := 4531122342405992753245

theorem tailTrace_268039 : CollatzResearch.WordTrace tailWord_268039 prefixEnd_268039 4531122342405992753245 := by
  unfold tailWord_268039
  simp only [CollatzResearch.WordTrace]
  refine ⟨9776185475947955261783171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6517456983965303507855447 9776185475947955261783171)
  ·
    refine ⟨14664278213921932892674757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9776185475947955261783171 14664278213921932892674757)
    ·
      refine ⟨2749552165110362417376517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 14664278213921932892674757 2749552165110362417376517)
      ·
        refine ⟨515541030958192953258097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2749552165110362417376517 515541030958192953258097)
        ·
          refine ⟨386655773218644714943573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 515541030958192953258097 386655773218644714943573)
          ·
            refine ⟨4531122342405992753245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 386655773218644714943573 4531122342405992753245)
            ·
              rfl

theorem cell20_268039_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 2, 8].length) (baseStart_268039 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_268039 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_268039 prefixEnd_268039 := by exact prefixLift 268039
  have htrace : WordTrace (prefixWord ++ tailWord_268039) baseStart_268039 baseEnd_268039 := by
    simpa [prefixWord, tailWord_268039, baseEnd_268039] using wordTrace_append hprefix tailTrace_268039
  have hstable : (prefixWord ++ tailWord_268039).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_268039).length < 2 ^ (prefixWord ++ tailWord_268039).sum := by decide
  have hdescent : baseEnd_268039 < baseStart_268039 := by decide
  rcases family_descends (prefixWord ++ tailWord_268039) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_268046 : List Nat := [4, 1, 1, 2, 1, 1, 2, 3, 5]
def baseStart_268046 : Nat := 118140960795 + 268046 * 2 ^ 59
def prefixEnd_268046 : Nat := 4983230072969 + 3 ^ 40 * 268046 * 2
def baseEnd_268046 : Nat := 122343498235700891104253

theorem tailTrace_268046 : CollatzResearch.WordTrace tailWord_268046 prefixEnd_268046 122343498235700891104253 := by
  unfold tailWord_268046
  simp only [CollatzResearch.WordTrace]
  refine ⟨1222055098365324432160999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 6517627191281730304858661 1222055098365324432160999)
  ·
    refine ⟨1833082647547986648241499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1222055098365324432160999 1833082647547986648241499)
    ·
      refine ⟨2749623971321979972362249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1833082647547986648241499 2749623971321979972362249)
      ·
        refine ⟨2062217978491484979271687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2749623971321979972362249 2062217978491484979271687)
        ·
          refine ⟨3093326967737227468907531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2062217978491484979271687 3093326967737227468907531)
          ·
            refine ⟨4639990451605841203361297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3093326967737227468907531 4639990451605841203361297)
            ·
              refine ⟨3479992838704380902520973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4639990451605841203361297 3479992838704380902520973)
              ·
                refine ⟨1304997314514142838445365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3479992838704380902520973 1304997314514142838445365)
                ·
                  refine ⟨122343498235700891104253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1304997314514142838445365 122343498235700891104253)
                  ·
                    rfl

theorem cell20_268046_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 2, 3, 5].length) (baseStart_268046 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_268046 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_268046 prefixEnd_268046 := by exact prefixLift 268046
  have htrace : WordTrace (prefixWord ++ tailWord_268046) baseStart_268046 baseEnd_268046 := by
    simpa [prefixWord, tailWord_268046, baseEnd_268046] using wordTrace_append hprefix tailTrace_268046
  have hstable : (prefixWord ++ tailWord_268046).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_268046).length < 2 ^ (prefixWord ++ tailWord_268046).sum := by decide
  have hdescent : baseEnd_268046 < baseStart_268046 := by decide
  rcases family_descends (prefixWord ++ tailWord_268046) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_268129 : List Nat := [1, 2, 3, 1, 1, 1, 3, 4, 4]
def baseStart_268129 : Nat := 118140960795 + 268129 * 2 ^ 59
def prefixEnd_268129 : Nat := 4983230072969 + 3 ^ 40 * 268129 * 2
def baseEnd_268129 : Nat := 122381381697321491337247

theorem tailTrace_268129 : CollatzResearch.WordTrace tailWord_268129 prefixEnd_268129 122381381697321491337247 := by
  unfold tailWord_268129
  simp only [CollatzResearch.WordTrace]
  refine ⟨9779468045621900632559441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6519645363747933755039627 9779468045621900632559441)
  ·
    refine ⟨7334601034216425474419581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9779468045621900632559441 7334601034216425474419581)
    ·
      refine ⟨2750475387831159552907343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7334601034216425474419581 2750475387831159552907343)
      ·
        refine ⟨4125713081746739329361015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2750475387831159552907343 4125713081746739329361015)
        ·
          refine ⟨6188569622620108994041523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4125713081746739329361015 6188569622620108994041523)
          ·
            refine ⟨9282854433930163491062285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6188569622620108994041523 9282854433930163491062285)
            ·
              refine ⟨3481070412723811309148357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9282854433930163491062285 3481070412723811309148357)
              ·
                refine ⟨652700702385714620465317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3481070412723811309148357 652700702385714620465317)
                ·
                  refine ⟨122381381697321491337247, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 652700702385714620465317 122381381697321491337247)
                  ·
                    rfl

theorem cell20_268129_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 3, 4, 4].length) (baseStart_268129 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_268129 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_268129 prefixEnd_268129 := by exact prefixLift 268129
  have htrace : WordTrace (prefixWord ++ tailWord_268129) baseStart_268129 baseEnd_268129 := by
    simpa [prefixWord, tailWord_268129, baseEnd_268129] using wordTrace_append hprefix tailTrace_268129
  have hstable : (prefixWord ++ tailWord_268129).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_268129).length < 2 ^ (prefixWord ++ tailWord_268129).sum := by decide
  have hdescent : baseEnd_268129 < baseStart_268129 := by decide
  rcases family_descends (prefixWord ++ tailWord_268129) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_268138 : List Nat := [3, 1, 3, 4, 2, 1, 1, 3, 2]
def baseStart_268138 : Nat := 118140960795 + 268138 * 2 ^ 59
def prefixEnd_268138 : Nat := 4983230072969 + 3 ^ 40 * 268138 * 2
def baseEnd_268138 : Nat := 122385489542557460037211

theorem tailTrace_268138 : CollatzResearch.WordTrace tailWord_268138 prefixEnd_268138 122385489542557460037211 := by
  unfold tailWord_268138
  simp only [CollatzResearch.WordTrace]
  refine ⟨2444949075647323792409267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6519864201726196779758045 2444949075647323792409267)
  ·
    refine ⟨3667423613470985688613901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2444949075647323792409267 3667423613470985688613901)
    ·
      refine ⟨1375283855051619633230213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3667423613470985688613901 1375283855051619633230213)
      ·
        refine ⟨257865722822178681230665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1375283855051619633230213 257865722822178681230665)
        ·
          refine ⟨193399292116634010922999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 257865722822178681230665 193399292116634010922999)
          ·
            refine ⟨290098938174951016384499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 193399292116634010922999 290098938174951016384499)
            ·
              refine ⟨435148407262426524576749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 290098938174951016384499 435148407262426524576749)
              ·
                refine ⟨163180652723409946716281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 435148407262426524576749 163180652723409946716281)
                ·
                  refine ⟨122385489542557460037211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 163180652723409946716281 122385489542557460037211)
                  ·
                    rfl

theorem cell20_268138_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 4, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 4, 2, 1, 1, 3, 2].length) (baseStart_268138 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_268138 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_268138 prefixEnd_268138 := by exact prefixLift 268138
  have htrace : WordTrace (prefixWord ++ tailWord_268138) baseStart_268138 baseEnd_268138 := by
    simpa [prefixWord, tailWord_268138, baseEnd_268138] using wordTrace_append hprefix tailTrace_268138
  have hstable : (prefixWord ++ tailWord_268138).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_268138).length < 2 ^ (prefixWord ++ tailWord_268138).sum := by decide
  have hdescent : baseEnd_268138 < baseStart_268138 := by decide
  rcases family_descends (prefixWord ++ tailWord_268138) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_268142 : List Nat := [4, 1, 2, 3, 1, 1, 3, 3, 2]
def baseStart_268142 : Nat := 118140960795 + 268142 * 2 ^ 59
def prefixEnd_268142 : Nat := 4983230072969 + 3 ^ 40 * 268142 * 2
def baseEnd_268142 : Nat := 122387315251551223903861

theorem tailTrace_268142 : CollatzResearch.WordTrace tailWord_268142 prefixEnd_268142 122387315251551223903861 := by
  unfold tailWord_268142
  simp only [CollatzResearch.WordTrace]
  refine ⟨1222492774321850481597835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 6519961463049869235188453 1222492774321850481597835)
  ·
    refine ⟨1833739161482775722396753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1222492774321850481597835 1833739161482775722396753)
    ·
      refine ⟨1375304371112081791797565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1833739161482775722396753 1375304371112081791797565)
      ·
        refine ⟨515739139167030671924087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1375304371112081791797565 515739139167030671924087)
        ·
          refine ⟨773608708750546007886131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 515739139167030671924087 773608708750546007886131)
          ·
            refine ⟨1160413063125819011829197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 773608708750546007886131 1160413063125819011829197)
            ·
              refine ⟨435154898672182129435949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1160413063125819011829197 435154898672182129435949)
              ·
                refine ⟨163183087002068298538481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 435154898672182129435949 163183087002068298538481)
                ·
                  refine ⟨122387315251551223903861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 163183087002068298538481 122387315251551223903861)
                  ·
                    rfl

theorem cell20_268142_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 1, 3, 3, 2].length) (baseStart_268142 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_268142 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_268142 prefixEnd_268142 := by exact prefixLift 268142
  have htrace : WordTrace (prefixWord ++ tailWord_268142) baseStart_268142 baseEnd_268142 := by
    simpa [prefixWord, tailWord_268142, baseEnd_268142] using wordTrace_append hprefix tailTrace_268142
  have hstable : (prefixWord ++ tailWord_268142).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_268142).length < 2 ^ (prefixWord ++ tailWord_268142).sum := by decide
  have hdescent : baseEnd_268142 < baseStart_268142 := by decide
  rcases family_descends (prefixWord ++ tailWord_268142) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_268160 : List Nat := [2, 1, 1, 2, 1, 2, 4, 4, 3]
def baseStart_268160 : Nat := 118140960795 + 268160 * 2 ^ 59
def prefixEnd_268160 : Nat := 4983230072969 + 3 ^ 40 * 268160 * 2
def baseEnd_268160 : Nat := 122395530942023161303787

theorem tailTrace_268160 : CollatzResearch.WordTrace tailWord_268160 prefixEnd_268160 122395530942023161303787 := by
  unfold tailWord_268160
  simp only [CollatzResearch.WordTrace]
  refine ⟨4890299354254796463468967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6520399139006395284625289 4890299354254796463468967)
  ·
    refine ⟨7335449031382194695203451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4890299354254796463468967 7335449031382194695203451)
    ·
      refine ⟨11003173547073292042805177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7335449031382194695203451 11003173547073292042805177)
      ·
        refine ⟨8252380160304969032103883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11003173547073292042805177 8252380160304969032103883)
        ·
          refine ⟨12378570240457453548155825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8252380160304969032103883 12378570240457453548155825)
          ·
            refine ⟨9283927680343090161116869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12378570240457453548155825 9283927680343090161116869)
            ·
              refine ⟨1740736440064329405209413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9283927680343090161116869 1740736440064329405209413)
              ·
                refine ⟨326388082512061763476765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1740736440064329405209413 326388082512061763476765)
                ·
                  refine ⟨122395530942023161303787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 326388082512061763476765 122395530942023161303787)
                  ·
                    rfl

theorem cell20_268160_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 4, 4, 3].length) (baseStart_268160 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_268160 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_268160 prefixEnd_268160 := by exact prefixLift 268160
  have htrace : WordTrace (prefixWord ++ tailWord_268160) baseStart_268160 baseEnd_268160 := by
    simpa [prefixWord, tailWord_268160, baseEnd_268160] using wordTrace_append hprefix tailTrace_268160
  have hstable : (prefixWord ++ tailWord_268160).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_268160).length < 2 ^ (prefixWord ++ tailWord_268160).sum := by decide
  have hdescent : baseEnd_268160 < baseStart_268160 := by decide
  rcases family_descends (prefixWord ++ tailWord_268160) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_268170 : List Nat := [3, 1, 2, 4, 2, 1, 2, 5]
def baseStart_268170 : Nat := 118140960795 + 268170 * 2 ^ 59
def prefixEnd_268170 : Nat := 4983230072969 + 3 ^ 40 * 268170 * 2
def baseEnd_268170 : Nat := 40800031738169190323471

theorem tailTrace_268170 : CollatzResearch.WordTrace tailWord_268170 prefixEnd_268170 40800031738169190323471 := by
  unfold tailWord_268170
  simp only [CollatzResearch.WordTrace]
  refine ⟨2445240859618341158700491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6520642292315576423201309 2445240859618341158700491)
  ·
    refine ⟨3667861289427511738050737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2445240859618341158700491 3667861289427511738050737)
    ·
      refine ⟨2750895967070633803538053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3667861289427511738050737 2750895967070633803538053)
      ·
        refine ⟨515792993825743838163385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2750895967070633803538053 515792993825743838163385)
        ·
          refine ⟨386844745369307878622539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 515792993825743838163385 386844745369307878622539)
          ·
            refine ⟨580267118053961817933809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 386844745369307878622539 580267118053961817933809)
            ·
              refine ⟨435200338540471363450357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 580267118053961817933809 435200338540471363450357)
              ·
                refine ⟨40800031738169190323471, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 435200338540471363450357 40800031738169190323471)
                ·
                  rfl

theorem cell20_268170_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 2, 1, 2, 5].length) (baseStart_268170 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_268170 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_268170 prefixEnd_268170 := by exact prefixLift 268170
  have htrace : WordTrace (prefixWord ++ tailWord_268170) baseStart_268170 baseEnd_268170 := by
    simpa [prefixWord, tailWord_268170, baseEnd_268170] using wordTrace_append hprefix tailTrace_268170
  have hstable : (prefixWord ++ tailWord_268170).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_268170).length < 2 ^ (prefixWord ++ tailWord_268170).sum := by decide
  have hdescent : baseEnd_268170 < baseStart_268170 := by decide
  rcases family_descends (prefixWord ++ tailWord_268170) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_268177 : List Nat := [1, 2, 2, 1, 1, 1, 8, 1, 3]
def baseStart_268177 : Nat := 118140960795 + 268177 * 2 ^ 59
def prefixEnd_268177 : Nat := 4983230072969 + 3 ^ 40 * 268177 * 2
def baseEnd_268177 : Nat := 122403290205246657737051

theorem tailTrace_268177 : CollatzResearch.WordTrace tailWord_268177 prefixEnd_268177 122403290205246657737051 := by
  unfold tailWord_268177
  simp only [CollatzResearch.WordTrace]
  refine ⟨9781218749448004830306785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6520812499632003220204523 9781218749448004830306785)
  ·
    refine ⟨7335914062086003622730089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9781218749448004830306785 7335914062086003622730089)
    ·
      refine ⟨5501935546564502717047567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7335914062086003622730089 5501935546564502717047567)
      ·
        refine ⟨8252903319846754075571351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5501935546564502717047567 8252903319846754075571351)
        ·
          refine ⟨12379354979770131113357027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8252903319846754075571351 12379354979770131113357027)
          ·
            refine ⟨18569032469655196670035541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12379354979770131113357027 18569032469655196670035541)
            ·
              refine ⟨217605849253771835976979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 18569032469655196670035541 217605849253771835976979)
              ·
                refine ⟨326408773880657753965469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 217605849253771835976979 326408773880657753965469)
                ·
                  refine ⟨122403290205246657737051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 326408773880657753965469 122403290205246657737051)
                  ·
                    rfl

theorem cell20_268177_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 8, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 8, 1, 3].length) (baseStart_268177 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_268177 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_268177 prefixEnd_268177 := by exact prefixLift 268177
  have htrace : WordTrace (prefixWord ++ tailWord_268177) baseStart_268177 baseEnd_268177 := by
    simpa [prefixWord, tailWord_268177, baseEnd_268177] using wordTrace_append hprefix tailTrace_268177
  have hstable : (prefixWord ++ tailWord_268177).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_268177).length < 2 ^ (prefixWord ++ tailWord_268177).sum := by decide
  have hdescent : baseEnd_268177 < baseStart_268177 := by decide
  rcases family_descends (prefixWord ++ tailWord_268177) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_268252 : List Nat := [2, 2, 6, 1, 1, 1, 2, 3, 2]
def baseStart_268252 : Nat := 118140960795 + 268252 * 2 ^ 59
def prefixEnd_268252 : Nat := 4983230072969 + 3 ^ 40 * 268252 * 2
def baseEnd_268252 : Nat := 122437522248879730236745

theorem tailTrace_268252 : CollatzResearch.WordTrace tailWord_268252 prefixEnd_268252 122437522248879730236745 := by
  unfold tailWord_268252
  simp only [CollatzResearch.WordTrace]
  refine ⟨4891977112088146319643505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6522636149450861759524673 4891977112088146319643505)
  ·
    refine ⟨3668982834066109739732629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4891977112088146319643505 3668982834066109739732629)
    ·
      refine ⟨171983570346848894049967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 3668982834066109739732629 171983570346848894049967)
      ·
        refine ⟨257975355520273341074951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 171983570346848894049967 257975355520273341074951)
        ·
          refine ⟨386963033280410011612427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 257975355520273341074951 386963033280410011612427)
          ·
            refine ⟨580444549920615017418641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 386963033280410011612427 580444549920615017418641)
            ·
              refine ⟨435333412440461263063981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 580444549920615017418641 435333412440461263063981)
              ·
                refine ⟨163250029665172973648993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 435333412440461263063981 163250029665172973648993)
                ·
                  refine ⟨122437522248879730236745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 163250029665172973648993 122437522248879730236745)
                  ·
                    rfl

theorem cell20_268252_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 6, 1, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 6, 1, 1, 1, 2, 3, 2].length) (baseStart_268252 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_268252 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_268252 prefixEnd_268252 := by exact prefixLift 268252
  have htrace : WordTrace (prefixWord ++ tailWord_268252) baseStart_268252 baseEnd_268252 := by
    simpa [prefixWord, tailWord_268252, baseEnd_268252] using wordTrace_append hprefix tailTrace_268252
  have hstable : (prefixWord ++ tailWord_268252).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_268252).length < 2 ^ (prefixWord ++ tailWord_268252).sum := by decide
  have hdescent : baseEnd_268252 < baseStart_268252 := by decide
  rcases family_descends (prefixWord ++ tailWord_268252) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_268270 : List Nat := [4, 1, 2, 1, 3, 3, 1, 2, 3]
def baseStart_268270 : Nat := 118140960795 + 268270 * 2 ^ 59
def prefixEnd_268270 : Nat := 4983230072969 + 3 ^ 40 * 268270 * 2
def baseEnd_268270 : Nat := 122445737939351667636671

theorem tailTrace_268270 : CollatzResearch.WordTrace tailWord_268270 prefixEnd_268270 122445737939351667636671 := by
  unfold tailWord_268270
  simp only [CollatzResearch.WordTrace]
  refine ⟨1223076342263885214180283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 6523073825407387808961509 1223076342263885214180283)
  ·
    refine ⟨1834614513395827821270425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1223076342263885214180283 1834614513395827821270425)
    ·
      refine ⟨1375960885046870865952819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1834614513395827821270425 1375960885046870865952819)
      ·
        refine ⟨2063941327570306298929229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1375960885046870865952819 2063941327570306298929229)
        ·
          refine ⟨773977997838864862098461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2063941327570306298929229 773977997838864862098461)
          ·
            refine ⟨290241749189574323286923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 773977997838864862098461 290241749189574323286923)
            ·
              refine ⟨435362623784361484930385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 290241749189574323286923 435362623784361484930385)
              ·
                refine ⟨326521967838271113697789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 435362623784361484930385 326521967838271113697789)
                ·
                  refine ⟨122445737939351667636671, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 326521967838271113697789 122445737939351667636671)
                  ·
                    rfl

theorem cell20_268270_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 3, 1, 2, 3].length) (baseStart_268270 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_268270 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_268270 prefixEnd_268270 := by exact prefixLift 268270
  have htrace : WordTrace (prefixWord ++ tailWord_268270) baseStart_268270 baseEnd_268270 := by
    simpa [prefixWord, tailWord_268270, baseEnd_268270] using wordTrace_append hprefix tailTrace_268270
  have hstable : (prefixWord ++ tailWord_268270).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_268270).length < 2 ^ (prefixWord ++ tailWord_268270).sum := by decide
  have hdescent : baseEnd_268270 < baseStart_268270 := by decide
  rcases family_descends (prefixWord ++ tailWord_268270) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_268281 : List Nat := [1, 2, 1, 3, 1, 4, 1, 3, 4]
def baseStart_268281 : Nat := 118140960795 + 268281 * 2 ^ 59
def prefixEnd_268281 : Nat := 4983230072969 + 3 ^ 40 * 268281 * 2
def baseEnd_268281 : Nat := 122450758639084518269959

theorem tailTrace_268281 : CollatzResearch.WordTrace tailWord_268281 prefixEnd_268281 122450758639084518269959 := by
  unfold tailWord_268281
  simp only [CollatzResearch.WordTrace]
  refine ⟨9785011941071230592092697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6523341294047487061395131 9785011941071230592092697)
  ·
    refine ⟨7338758955803422944069523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9785011941071230592092697 7338758955803422944069523)
    ·
      refine ⟨11008138433705134416104285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7338758955803422944069523 11008138433705134416104285)
      ·
        refine ⟨4128051912639425406039107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11008138433705134416104285 4128051912639425406039107)
        ·
          refine ⟨6192077868959138109058661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4128051912639425406039107 6192077868959138109058661)
          ·
            refine ⟨1161014600429838395448499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 6192077868959138109058661 1161014600429838395448499)
            ·
              refine ⟨1741521900644757593172749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1161014600429838395448499 1741521900644757593172749)
              ·
                refine ⟨653070712741784097439781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1741521900644757593172749 653070712741784097439781)
                ·
                  refine ⟨122450758639084518269959, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 653070712741784097439781 122450758639084518269959)
                  ·
                    rfl

theorem cell20_268281_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 4, 1, 3, 4].length) (baseStart_268281 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_268281 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_268281 prefixEnd_268281 := by exact prefixLift 268281
  have htrace : WordTrace (prefixWord ++ tailWord_268281) baseStart_268281 baseEnd_268281 := by
    simpa [prefixWord, tailWord_268281, baseEnd_268281] using wordTrace_append hprefix tailTrace_268281
  have hstable : (prefixWord ++ tailWord_268281).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_268281).length < 2 ^ (prefixWord ++ tailWord_268281).sum := by decide
  have hdescent : baseEnd_268281 < baseStart_268281 := by decide
  rcases family_descends (prefixWord ++ tailWord_268281) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_268311 : List Nat := [1, 1, 3, 5, 3, 1, 1, 3, 2]
def baseStart_268311 : Nat := 118140960795 + 268311 * 2 ^ 59
def prefixEnd_268311 : Nat := 4983230072969 + 3 ^ 40 * 268311 * 2
def baseEnd_268311 : Nat := 122464451456537747269837

theorem tailTrace_268311 : CollatzResearch.WordTrace tailWord_268311 prefixEnd_268311 122464451456537747269837 := by
  unfold tailWord_268311
  simp only [CollatzResearch.WordTrace]
  refine ⟨9786106130962545715684787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6524070753975030477123191 9786106130962545715684787)
  ·
    refine ⟨14679159196443818573527181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9786106130962545715684787 14679159196443818573527181)
    ·
      refine ⟨5504684698666431965072693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14679159196443818573527181 5504684698666431965072693)
      ·
        refine ⟨516064190499977996725565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 5504684698666431965072693 516064190499977996725565)
        ·
          refine ⟨193524071437491748772087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 516064190499977996725565 193524071437491748772087)
          ·
            refine ⟨290286107156237623158131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 193524071437491748772087 290286107156237623158131)
            ·
              refine ⟨435429160734356434737197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 290286107156237623158131 435429160734356434737197)
              ·
                refine ⟨163285935275383663026449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 435429160734356434737197 163285935275383663026449)
                ·
                  refine ⟨122464451456537747269837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 163285935275383663026449 122464451456537747269837)
                  ·
                    rfl

theorem cell20_268311_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 3, 1, 1, 3, 2].length) (baseStart_268311 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_268311 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_268311 prefixEnd_268311 := by exact prefixLift 268311
  have htrace : WordTrace (prefixWord ++ tailWord_268311) baseStart_268311 baseEnd_268311 := by
    simpa [prefixWord, tailWord_268311, baseEnd_268311] using wordTrace_append hprefix tailTrace_268311
  have hstable : (prefixWord ++ tailWord_268311).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_268311).length < 2 ^ (prefixWord ++ tailWord_268311).sum := by decide
  have hdescent : baseEnd_268311 < baseStart_268311 := by decide
  rcases family_descends (prefixWord ++ tailWord_268311) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_268336 : List Nat := [2, 1, 1, 1, 2, 7, 1, 1, 4]
def baseStart_268336 : Nat := 118140960795 + 268336 * 2 ^ 59
def prefixEnd_268336 : Nat := 4983230072969 + 3 ^ 40 * 268336 * 2
def baseEnd_268336 : Nat := 122475862137748771436401

theorem tailTrace_268336 : CollatzResearch.WordTrace tailWord_268336 prefixEnd_268336 122475862137748771436401 := by
  unfold tailWord_268336
  simp only [CollatzResearch.WordTrace]
  refine ⟨4893508977935987492672431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6524678637247983323563241 4893508977935987492672431)
  ·
    refine ⟨7340263466903981239008647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4893508977935987492672431 7340263466903981239008647)
    ·
      refine ⟨11010395200355971858512971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7340263466903981239008647 11010395200355971858512971)
      ·
        refine ⟨16515592800533957787769457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11010395200355971858512971 16515592800533957787769457)
        ·
          refine ⟨12386694600400468340827093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16515592800533957787769457 12386694600400468340827093)
          ·
            refine ⟨290313154696885976738135, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 12386694600400468340827093 290313154696885976738135)
            ·
              refine ⟨435469732045328965107203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 290313154696885976738135 435469732045328965107203)
              ·
                refine ⟨653204598067993447660805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 435469732045328965107203 653204598067993447660805)
                ·
                  refine ⟨122475862137748771436401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 653204598067993447660805 122475862137748771436401)
                  ·
                    rfl

theorem cell20_268336_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 7, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 7, 1, 1, 4].length) (baseStart_268336 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_268336 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_268336 prefixEnd_268336 := by exact prefixLift 268336
  have htrace : WordTrace (prefixWord ++ tailWord_268336) baseStart_268336 baseEnd_268336 := by
    simpa [prefixWord, tailWord_268336, baseEnd_268336] using wordTrace_append hprefix tailTrace_268336
  have hstable : (prefixWord ++ tailWord_268336).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_268336).length < 2 ^ (prefixWord ++ tailWord_268336).sum := by decide
  have hdescent : baseEnd_268336 < baseStart_268336 := by decide
  rcases family_descends (prefixWord ++ tailWord_268336) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_268364 : List Nat := [2, 2, 1, 3, 1, 1, 4, 6]
def baseStart_268364 : Nat := 118140960795 + 268364 * 2 ^ 59
def prefixEnd_268364 : Nat := 4983230072969 + 3 ^ 40 * 268364 * 2
def baseEnd_268364 : Nat := 40829547366901706167651

theorem tailTrace_268364 : CollatzResearch.WordTrace tailWord_268364 prefixEnd_268364 40829547366901706167651 := by
  unfold tailWord_268364
  simp only [CollatzResearch.WordTrace]
  refine ⟨4894019599885267883682073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6525359466513690511576097 4894019599885267883682073)
  ·
    refine ⟨3670514699913950912761555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4894019599885267883682073 3670514699913950912761555)
    ·
      refine ⟨5505772049870926369142333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3670514699913950912761555 5505772049870926369142333)
      ·
        refine ⟨2064664518701597388428375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5505772049870926369142333 2064664518701597388428375)
        ·
          refine ⟨3096996778052396082642563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2064664518701597388428375 3096996778052396082642563)
          ·
            refine ⟨4645495167078594123963845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3096996778052396082642563 4645495167078594123963845)
            ·
              refine ⟨871030343827236398243221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4645495167078594123963845 871030343827236398243221)
              ·
                refine ⟨40829547366901706167651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 871030343827236398243221 40829547366901706167651)
                ·
                  rfl

theorem cell20_268364_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 4, 6].length) (baseStart_268364 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_268364 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_268364 prefixEnd_268364 := by exact prefixLift 268364
  have htrace : WordTrace (prefixWord ++ tailWord_268364) baseStart_268364 baseEnd_268364 := by
    simpa [prefixWord, tailWord_268364, baseEnd_268364] using wordTrace_append hprefix tailTrace_268364
  have hstable : (prefixWord ++ tailWord_268364).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_268364).length < 2 ^ (prefixWord ++ tailWord_268364).sum := by decide
  have hdescent : baseEnd_268364 < baseStart_268364 := by decide
  rcases family_descends (prefixWord ++ tailWord_268364) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_268381 : List Nat := [1, 4, 4, 1, 1, 9]
def baseStart_268381 : Nat := 118140960795 + 268381 * 2 ^ 59
def prefixEnd_268381 : Nat := 4983230072969 + 3 ^ 40 * 268381 * 2
def baseEnd_268381 : Nat := 4536903754219578330971

theorem tailTrace_268381 : CollatzResearch.WordTrace tailWord_268381 prefixEnd_268381 4536903754219578330971 := by
  unfold tailWord_268381
  simp only [CollatzResearch.WordTrace]
  refine ⟨9788659240708947670732997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6525772827139298447155331 9788659240708947670732997)
  ·
    refine ⟨1835373607632927688262437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 9788659240708947670732997 1835373607632927688262437)
    ·
      refine ⟨344132551431173941549207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1835373607632927688262437 344132551431173941549207)
      ·
        refine ⟨516198827146760912323811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 344132551431173941549207 516198827146760912323811)
        ·
          refine ⟨774298240720141368485717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 516198827146760912323811 774298240720141368485717)
          ·
            refine ⟨4536903754219578330971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 774298240720141368485717 4536903754219578330971)
            ·
              rfl

theorem cell20_268381_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 9].length) (baseStart_268381 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_268381 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_268381 prefixEnd_268381 := by exact prefixLift 268381
  have htrace : WordTrace (prefixWord ++ tailWord_268381) baseStart_268381 baseEnd_268381 := by
    simpa [prefixWord, tailWord_268381, baseEnd_268381] using wordTrace_append hprefix tailTrace_268381
  have hstable : (prefixWord ++ tailWord_268381).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_268381).length < 2 ^ (prefixWord ++ tailWord_268381).sum := by decide
  have hdescent : baseEnd_268381 < baseStart_268381 := by decide
  rcases family_descends (prefixWord ++ tailWord_268381) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_268388 : List Nat := [2, 3, 1, 1, 2, 1, 3, 4, 3]
def baseStart_268388 : Nat := 118140960795 + 268388 * 2 ^ 59
def prefixEnd_268388 : Nat := 4983230072969 + 3 ^ 40 * 268388 * 2
def baseEnd_268388 : Nat := 122499596354667701702855

theorem tailTrace_268388 : CollatzResearch.WordTrace tailWord_268388 prefixEnd_268388 122499596354667701702855 := by
  unfold tailWord_268388
  simp only [CollatzResearch.WordTrace]
  refine ⟨4894457275841793933118909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6525943034455725244158545 4894457275841793933118909)
  ·
    refine ⟨1835421478440672724919591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4894457275841793933118909 1835421478440672724919591)
    ·
      refine ⟨2753132217661009087379387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1835421478440672724919591 2753132217661009087379387)
      ·
        refine ⟨4129698326491513631069081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2753132217661009087379387 4129698326491513631069081)
        ·
          refine ⟨3097273744868635223301811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4129698326491513631069081 3097273744868635223301811)
          ·
            refine ⟨4645910617302952834952717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3097273744868635223301811 4645910617302952834952717)
            ·
              refine ⟨1742216481488607313107269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4645910617302952834952717 1742216481488607313107269)
              ·
                refine ⟨326665590279113871207613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1742216481488607313107269 326665590279113871207613)
                ·
                  refine ⟨122499596354667701702855, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 326665590279113871207613 122499596354667701702855)
                  ·
                    rfl

theorem cell20_268388_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 3, 4, 3].length) (baseStart_268388 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_268388 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_268388 prefixEnd_268388 := by exact prefixLift 268388
  have htrace : WordTrace (prefixWord ++ tailWord_268388) baseStart_268388 baseEnd_268388 := by
    simpa [prefixWord, tailWord_268388, baseEnd_268388] using wordTrace_append hprefix tailTrace_268388
  have hstable : (prefixWord ++ tailWord_268388).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_268388).length < 2 ^ (prefixWord ++ tailWord_268388).sum := by decide
  have hdescent : baseEnd_268388 < baseStart_268388 := by decide
  rcases family_descends (prefixWord ++ tailWord_268388) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_268419 : List Nat := [1, 1, 1, 3, 3, 4, 3, 4]
def baseStart_268419 : Nat := 118140960795 + 268419 * 2 ^ 59
def prefixEnd_268419 : Nat := 4983230072969 + 3 ^ 40 * 268419 * 2
def baseEnd_268419 : Nat := 40837915199789790556465

theorem tailTrace_268419 : CollatzResearch.WordTrace tailWord_268419 prefixEnd_268419 40837915199789790556465 := by
  unfold tailWord_268419
  simp only [CollatzResearch.WordTrace]
  refine ⟨9790045214571280160616311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6526696809714186773744207 9790045214571280160616311)
  ·
    refine ⟨14685067821856920240924467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9790045214571280160616311 14685067821856920240924467)
    ·
      refine ⟨22027601732785380361386701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14685067821856920240924467 22027601732785380361386701)
      ·
        refine ⟨8260350649794517635520013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 22027601732785380361386701 8260350649794517635520013)
        ·
          refine ⟨3097631493672944113320005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8260350649794517635520013 3097631493672944113320005)
          ·
            refine ⟨580805905063677021247501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3097631493672944113320005 580805905063677021247501)
            ·
              refine ⟨217802214398878882967813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 580805905063677021247501 217802214398878882967813)
              ·
                refine ⟨40837915199789790556465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 217802214398878882967813 40837915199789790556465)
                ·
                  rfl

theorem cell20_268419_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 4, 3, 4].length) (baseStart_268419 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_268419 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_268419 prefixEnd_268419 := by exact prefixLift 268419
  have htrace : WordTrace (prefixWord ++ tailWord_268419) baseStart_268419 baseEnd_268419 := by
    simpa [prefixWord, tailWord_268419, baseEnd_268419] using wordTrace_append hprefix tailTrace_268419
  have hstable : (prefixWord ++ tailWord_268419).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_268419).length < 2 ^ (prefixWord ++ tailWord_268419).sum := by decide
  have hdescent : baseEnd_268419 < baseStart_268419 := by decide
  rcases family_descends (prefixWord ++ tailWord_268419) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_268436 : List Nat := [2, 4, 2, 3, 1, 1, 7]
def baseStart_268436 : Nat := 118140960795 + 268436 * 2 ^ 59
def prefixEnd_268436 : Nat := 4983230072969 + 3 ^ 40 * 268436 * 2
def baseEnd_268436 : Nat := 13613500540288096455851

theorem tailTrace_268436 : CollatzResearch.WordTrace tailWord_268436 prefixEnd_268436 13613500540288096455851 := by
  unfold tailWord_268436
  simp only [CollatzResearch.WordTrace]
  refine ⟨4895332627754846031992581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6527110170339794709323441 4895332627754846031992581)
  ·
    refine ⟨917874867704033630998609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 4895332627754846031992581 917874867704033630998609)
    ·
      refine ⟨688406150778025223248957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 917874867704033630998609 688406150778025223248957)
      ·
        refine ⟨258152306541759458718359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 688406150778025223248957 258152306541759458718359)
        ·
          refine ⟨387228459812639188077539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 258152306541759458718359 387228459812639188077539)
          ·
            refine ⟨580842689718958782116309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 387228459812639188077539 580842689718958782116309)
            ·
              refine ⟨13613500540288096455851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 580842689718958782116309 13613500540288096455851)
              ·
                rfl

theorem cell20_268436_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 3, 1, 1, 7].length) (baseStart_268436 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_268436 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_268436 prefixEnd_268436 := by exact prefixLift 268436
  have htrace : WordTrace (prefixWord ++ tailWord_268436) baseStart_268436 baseEnd_268436 := by
    simpa [prefixWord, tailWord_268436, baseEnd_268436] using wordTrace_append hprefix tailTrace_268436
  have hstable : (prefixWord ++ tailWord_268436).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_268436).length < 2 ^ (prefixWord ++ tailWord_268436).sum := by decide
  have hdescent : baseEnd_268436 < baseStart_268436 := by decide
  rcases family_descends (prefixWord ++ tailWord_268436) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_268450 : List Nat := [3, 3, 1, 3, 1, 1, 1, 3, 4]
def baseStart_268450 : Nat := 118140960795 + 268450 * 2 ^ 59
def prefixEnd_268450 : Nat := 4983230072969 + 3 ^ 40 * 268450 * 2
def baseEnd_268450 : Nat := 122527894844071041635935

theorem tailTrace_268450 : CollatzResearch.WordTrace tailWord_268450 prefixEnd_268450 122527894844071041635935 := by
  unfold tailWord_268450
  simp only [CollatzResearch.WordTrace]
  refine ⟨2447793969364743113748701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6527450584972648303329869 2447793969364743113748701)
  ·
    refine ⟨917922738511778667655763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2447793969364743113748701 917922738511778667655763)
    ·
      refine ⟨1376884107767668001483645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 917922738511778667655763 1376884107767668001483645)
      ·
        refine ⟨516331540412875500556367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1376884107767668001483645 516331540412875500556367)
        ·
          refine ⟨774497310619313250834551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 516331540412875500556367 774497310619313250834551)
          ·
            refine ⟨1161745965928969876251827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 774497310619313250834551 1161745965928969876251827)
            ·
              refine ⟨1742618948893454814377741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1161745965928969876251827 1742618948893454814377741)
              ·
                refine ⟨653482105835045555391653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1742618948893454814377741 653482105835045555391653)
                ·
                  refine ⟨122527894844071041635935, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 653482105835045555391653 122527894844071041635935)
                  ·
                    rfl

theorem cell20_268450_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 1, 1, 3, 4].length) (baseStart_268450 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_268450 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_268450 prefixEnd_268450 := by exact prefixLift 268450
  have htrace : WordTrace (prefixWord ++ tailWord_268450) baseStart_268450 baseEnd_268450 := by
    simpa [prefixWord, tailWord_268450, baseEnd_268450] using wordTrace_append hprefix tailTrace_268450
  have hstable : (prefixWord ++ tailWord_268450).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_268450).length < 2 ^ (prefixWord ++ tailWord_268450).sum := by decide
  have hdescent : baseEnd_268450 < baseStart_268450 := by decide
  rcases family_descends (prefixWord ++ tailWord_268450) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_268471 : List Nat := [1, 1, 3, 1, 4, 2, 2, 2, 4]
def baseStart_268471 : Nat := 118140960795 + 268471 * 2 ^ 59
def prefixEnd_268471 : Nat := 4983230072969 + 3 ^ 40 * 268471 * 2
def baseEnd_268471 : Nat := 122537479816288301935849

theorem tailTrace_268471 : CollatzResearch.WordTrace tailWord_268471 prefixEnd_268471 122537479816288301935849 := by
  unfold tailWord_268471
  simp only [CollatzResearch.WordTrace]
  refine ⟨9791941810382893041509267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6527961206921928694339511 9791941810382893041509267)
  ·
    refine ⟨14687912715574339562263901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9791941810382893041509267 14687912715574339562263901)
    ·
      refine ⟨5507967268340377335848963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14687912715574339562263901 5507967268340377335848963)
      ·
        refine ⟨8261950902510566003773445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5507967268340377335848963 8261950902510566003773445)
        ·
          refine ⟨1549115794220731125707521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 8261950902510566003773445 1549115794220731125707521)
          ·
            refine ⟨1161836845665548344280641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1549115794220731125707521 1161836845665548344280641)
            ·
              refine ⟨871377634249161258210481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1161836845665548344280641 871377634249161258210481)
              ·
                refine ⟨653533225686870943657861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 871377634249161258210481 653533225686870943657861)
                ·
                  refine ⟨122537479816288301935849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 653533225686870943657861 122537479816288301935849)
                  ·
                    rfl

theorem cell20_268471_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 2, 2, 2, 4].length) (baseStart_268471 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_268471 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_268471 prefixEnd_268471 := by exact prefixLift 268471
  have htrace : WordTrace (prefixWord ++ tailWord_268471) baseStart_268471 baseEnd_268471 := by
    simpa [prefixWord, tailWord_268471, baseEnd_268471] using wordTrace_append hprefix tailTrace_268471
  have hstable : (prefixWord ++ tailWord_268471).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_268471).length < 2 ^ (prefixWord ++ tailWord_268471).sum := by decide
  have hdescent : baseEnd_268471 < baseStart_268471 := by decide
  rcases family_descends (prefixWord ++ tailWord_268471) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_268484 : List Nat := [2, 3, 3, 1, 2, 3, 1, 3, 2]
def baseStart_268484 : Nat := 118140960795 + 268484 * 2 ^ 59
def prefixEnd_268484 : Nat := 4983230072969 + 3 ^ 40 * 268484 * 2
def baseEnd_268484 : Nat := 122543413370518034502463

theorem tailTrace_268484 : CollatzResearch.WordTrace tailWord_268484 prefixEnd_268484 122543413370518034502463 := by
  unfold tailWord_268484
  simp only [CollatzResearch.WordTrace]
  refine ⟨4896207979667898130866253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6528277306223864174488337 4896207979667898130866253)
  ·
    refine ⟨1836077992375461799074845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4896207979667898130866253 1836077992375461799074845)
    ·
      refine ⟨688529247140798174653067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1836077992375461799074845 688529247140798174653067)
      ·
        refine ⟨1032793870711197261979601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 688529247140798174653067 1032793870711197261979601)
        ·
          refine ⟨774595403033397946484701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1032793870711197261979601 774595403033397946484701)
          ·
            refine ⟨290473276137524229931763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 774595403033397946484701 290473276137524229931763)
            ·
              refine ⟨435709914206286344897645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 290473276137524229931763 435709914206286344897645)
              ·
                refine ⟨163391217827357379336617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 435709914206286344897645 163391217827357379336617)
                ·
                  refine ⟨122543413370518034502463, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 163391217827357379336617 122543413370518034502463)
                  ·
                    rfl

theorem cell20_268484_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 3, 1, 3, 2].length) (baseStart_268484 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_268484 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_268484 prefixEnd_268484 := by exact prefixLift 268484
  have htrace : WordTrace (prefixWord ++ tailWord_268484) baseStart_268484 baseEnd_268484 := by
    simpa [prefixWord, tailWord_268484, baseEnd_268484] using wordTrace_append hprefix tailTrace_268484
  have hstable : (prefixWord ++ tailWord_268484).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_268484).length < 2 ^ (prefixWord ++ tailWord_268484).sum := by decide
  have hdescent : baseEnd_268484 < baseStart_268484 := by decide
  rcases family_descends (prefixWord ++ tailWord_268484) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_268485 : List Nat := [1, 3, 1, 1, 1, 1, 5, 2, 5]
def baseStart_268485 : Nat := 118140960795 + 268485 * 2 ^ 59
def prefixEnd_268485 : Nat := 4983230072969 + 3 ^ 40 * 268485 * 2
def baseEnd_268485 : Nat := 122543869797766475469125

theorem tailTrace_268485 : CollatzResearch.WordTrace tailWord_268485 prefixEnd_268485 122543869797766475469125 := by
  unfold tailWord_268485
  simp only [CollatzResearch.WordTrace]
  refine ⟨9792452432332173432518909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6528301621554782288345939 9792452432332173432518909)
  ·
    refine ⟨3672169662124565037194591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9792452432332173432518909 3672169662124565037194591)
    ·
      refine ⟨5508254493186847555791887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3672169662124565037194591 5508254493186847555791887)
      ·
        refine ⟨8262381739780271333687831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5508254493186847555791887 8262381739780271333687831)
        ·
          refine ⟨12393572609670407000531747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8262381739780271333687831 12393572609670407000531747)
          ·
            refine ⟨18590358914505610500797621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12393572609670407000531747 18590358914505610500797621)
            ·
              refine ⟨1742846148234900984449777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 18590358914505610500797621 1742846148234900984449777)
              ·
                refine ⟨1307134611176175738337333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1742846148234900984449777 1307134611176175738337333)
                ·
                  refine ⟨122543869797766475469125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1307134611176175738337333 122543869797766475469125)
                  ·
                    rfl

theorem cell20_268485_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 5, 2, 5].length) (baseStart_268485 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_268485 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_268485 prefixEnd_268485 := by exact prefixLift 268485
  have htrace : WordTrace (prefixWord ++ tailWord_268485) baseStart_268485 baseEnd_268485 := by
    simpa [prefixWord, tailWord_268485, baseEnd_268485] using wordTrace_append hprefix tailTrace_268485
  have hstable : (prefixWord ++ tailWord_268485).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_268485).length < 2 ^ (prefixWord ++ tailWord_268485).sum := by decide
  have hdescent : baseEnd_268485 < baseStart_268485 := by decide
  rcases family_descends (prefixWord ++ tailWord_268485) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_268515 : List Nat := [1, 1, 1, 8, 1, 2, 2, 1, 3]
def baseStart_268515 : Nat := 118140960795 + 268515 * 2 ^ 59
def prefixEnd_268515 : Nat := 4983230072969 + 3 ^ 40 * 268515 * 2
def baseEnd_268515 : Nat := 122557562615219704469003

theorem tailTrace_268515 : CollatzResearch.WordTrace tailWord_268515 prefixEnd_268515 122557562615219704469003 := by
  unfold tailWord_268515
  simp only [CollatzResearch.WordTrace]
  refine ⟨9793546622223488556110999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6529031081482325704073999 9793546622223488556110999)
  ·
    refine ⟨14690319933335232834166499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9793546622223488556110999 14690319933335232834166499)
    ·
      refine ⟨22035479900002849251249749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14690319933335232834166499 22035479900002849251249749)
      ·
        refine ⟨258228280078158389663083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 8 22035479900002849251249749 258228280078158389663083)
        ·
          refine ⟨387342420117237584494625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 258228280078158389663083 387342420117237584494625)
          ·
            refine ⟨290506815087928188370969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 387342420117237584494625 290506815087928188370969)
            ·
              refine ⟨217880111315946141278227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 290506815087928188370969 217880111315946141278227)
              ·
                refine ⟨326820166973919211917341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 217880111315946141278227 326820166973919211917341)
                ·
                  refine ⟨122557562615219704469003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 326820166973919211917341 122557562615219704469003)
                  ·
                    rfl

theorem cell20_268515_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 8, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 8, 1, 2, 2, 1, 3].length) (baseStart_268515 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_268515 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_268515 prefixEnd_268515 := by exact prefixLift 268515
  have htrace : WordTrace (prefixWord ++ tailWord_268515) baseStart_268515 baseEnd_268515 := by
    simpa [prefixWord, tailWord_268515, baseEnd_268515] using wordTrace_append hprefix tailTrace_268515
  have hstable : (prefixWord ++ tailWord_268515).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_268515).length < 2 ^ (prefixWord ++ tailWord_268515).sum := by decide
  have hdescent : baseEnd_268515 < baseStart_268515 := by decide
  rcases family_descends (prefixWord ++ tailWord_268515) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_268519 : List Nat := [1, 1, 5, 3, 1, 2, 1, 3, 3]
def baseStart_268519 : Nat := 118140960795 + 268519 * 2 ^ 59
def prefixEnd_268519 : Nat := 4983230072969 + 3 ^ 40 * 268519 * 2
def baseEnd_268519 : Nat := 122559388324213468335653

theorem tailTrace_268519 : CollatzResearch.WordTrace tailWord_268519 prefixEnd_268519 122559388324213468335653 := by
  unfold tailWord_268519
  simp only [CollatzResearch.WordTrace]
  refine ⟨9793692514208997239256611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6529128342805998159504407 9793692514208997239256611)
  ·
    refine ⟨14690538771313495858884917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9793692514208997239256611 14690538771313495858884917)
    ·
      refine ⟨1377238009810640236770461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 14690538771313495858884917 1377238009810640236770461)
      ·
        refine ⟨516464253678990088788923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1377238009810640236770461 516464253678990088788923)
        ·
          refine ⟨774696380518485133183385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 516464253678990088788923 774696380518485133183385)
          ·
            refine ⟨581022285388863849887539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 774696380518485133183385 581022285388863849887539)
            ·
              refine ⟨871533428083295774831309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 581022285388863849887539 871533428083295774831309)
              ·
                refine ⟨326825035531235915561741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 871533428083295774831309 326825035531235915561741)
                ·
                  refine ⟨122559388324213468335653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 326825035531235915561741 122559388324213468335653)
                  ·
                    rfl

theorem cell20_268519_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 2, 1, 3, 3].length) (baseStart_268519 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_268519 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_268519 prefixEnd_268519 := by exact prefixLift 268519
  have htrace : WordTrace (prefixWord ++ tailWord_268519) baseStart_268519 baseEnd_268519 := by
    simpa [prefixWord, tailWord_268519, baseEnd_268519] using wordTrace_append hprefix tailTrace_268519
  have hstable : (prefixWord ++ tailWord_268519).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_268519).length < 2 ^ (prefixWord ++ tailWord_268519).sum := by decide
  have hdescent : baseEnd_268519 < baseStart_268519 := by decide
  rcases family_descends (prefixWord ++ tailWord_268519) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_268574 : List Nat := [4, 3, 2, 1, 1, 1, 2, 3, 3]
def baseStart_268574 : Nat := 118140960795 + 268574 * 2 ^ 59
def prefixEnd_268574 : Nat := 4983230072969 + 3 ^ 40 * 268574 * 2
def baseEnd_268574 : Nat := 122584491822877721502095

theorem tailTrace_268574 : CollatzResearch.WordTrace tailWord_268574 prefixEnd_268574 122584491822877721502095 := by
  unfold tailWord_268574
  simp only [CollatzResearch.WordTrace]
  refine ⟨1224462316126217704063597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 6530465686006494421672517 1224462316126217704063597)
  ·
    refine ⟨459173368547331639023849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1224462316126217704063597 459173368547331639023849)
    ·
      refine ⟨344380026410498729267887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 459173368547331639023849 344380026410498729267887)
      ·
        refine ⟨516570039615748093901831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 344380026410498729267887 516570039615748093901831)
        ·
          refine ⟨774855059423622140852747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 516570039615748093901831 774855059423622140852747)
          ·
            refine ⟨1162282589135433211279121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 774855059423622140852747 1162282589135433211279121)
            ·
              refine ⟨871711941851574908459341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1162282589135433211279121 871711941851574908459341)
              ·
                refine ⟨326891978194340590672253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 871711941851574908459341 326891978194340590672253)
                ·
                  refine ⟨122584491822877721502095, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 326891978194340590672253 122584491822877721502095)
                  ·
                    rfl

theorem cell20_268574_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 1, 2, 3, 3].length) (baseStart_268574 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_268574 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_268574 prefixEnd_268574 := by exact prefixLift 268574
  have htrace : WordTrace (prefixWord ++ tailWord_268574) baseStart_268574 baseEnd_268574 := by
    simpa [prefixWord, tailWord_268574, baseEnd_268574] using wordTrace_append hprefix tailTrace_268574
  have hstable : (prefixWord ++ tailWord_268574).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_268574).length < 2 ^ (prefixWord ++ tailWord_268574).sum := by decide
  have hdescent : baseEnd_268574 < baseStart_268574 := by decide
  rcases family_descends (prefixWord ++ tailWord_268574) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_268602 : List Nat := [3, 1, 1, 1, 4, 2, 1, 5, 2]
def baseStart_268602 : Nat := 118140960795 + 268602 * 2 ^ 59
def prefixEnd_268602 : Nat := 4983230072969 + 3 ^ 40 * 268602 * 2
def baseEnd_268602 : Nat := 122597271785834068568647

theorem tailTrace_268602 : CollatzResearch.WordTrace tailWord_268602 prefixEnd_268602 122597271785834068568647 := by
  unfold tailWord_268602
  simp only [CollatzResearch.WordTrace]
  refine ⟨2449179943227075603632015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6531146515272201609685373 2449179943227075603632015)
  ·
    refine ⟨3673769914840613405448023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2449179943227075603632015 3673769914840613405448023)
    ·
      refine ⟨5510654872260920108172035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3673769914840613405448023 5510654872260920108172035)
      ·
        refine ⟨8265982308391380162258053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5510654872260920108172035 8265982308391380162258053)
        ·
          refine ⟨1549871682823383780423385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 8265982308391380162258053 1549871682823383780423385)
          ·
            refine ⟨1162403762117537835317539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1549871682823383780423385 1162403762117537835317539)
            ·
              refine ⟨1743605643176306752976309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1162403762117537835317539 1743605643176306752976309)
              ·
                refine ⟨163463029047778758091529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1743605643176306752976309 163463029047778758091529)
                ·
                  refine ⟨122597271785834068568647, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 163463029047778758091529 122597271785834068568647)
                  ·
                    rfl

theorem cell20_268602_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 2, 1, 5, 2].length) (baseStart_268602 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_268602 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_268602 prefixEnd_268602 := by exact prefixLift 268602
  have htrace : WordTrace (prefixWord ++ tailWord_268602) baseStart_268602 baseEnd_268602 := by
    simpa [prefixWord, tailWord_268602, baseEnd_268602] using wordTrace_append hprefix tailTrace_268602
  have hstable : (prefixWord ++ tailWord_268602).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_268602).length < 2 ^ (prefixWord ++ tailWord_268602).sum := by decide
  have hdescent : baseEnd_268602 < baseStart_268602 := by decide
  rcases family_descends (prefixWord ++ tailWord_268602) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_268609 : List Nat := [1, 2, 5, 2, 2, 1, 7]
def baseStart_268609 : Nat := 118140960795 + 268609 * 2 ^ 59
def prefixEnd_268609 : Nat := 4983230072969 + 3 ^ 40 * 268609 * 2
def baseEnd_268609 : Nat := 13622274086285906148365

theorem tailTrace_268609 : CollatzResearch.WordTrace tailWord_268609 prefixEnd_268609 13622274086285906148365 := by
  unfold tailWord_268609
  simp only [CollatzResearch.WordTrace]
  refine ⟨9796975083882942610032881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6531316722588628406688587 9796975083882942610032881)
  ·
    refine ⟨7347731312912206957524661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9796975083882942610032881 7347731312912206957524661)
    ·
      refine ⟨688849810585519402267937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 7347731312912206957524661 688849810585519402267937)
      ·
        refine ⟨516637357939139551700953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 688849810585519402267937 516637357939139551700953)
        ·
          refine ⟨387478018454354663775715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 516637357939139551700953 387478018454354663775715)
          ·
            refine ⟨581217027681531995663573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 387478018454354663775715 581217027681531995663573)
            ·
              refine ⟨13622274086285906148365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 581217027681531995663573 13622274086285906148365)
              ·
                rfl

theorem cell20_268609_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 2, 1, 7].length) (baseStart_268609 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_268609 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_268609 prefixEnd_268609 := by exact prefixLift 268609
  have htrace : WordTrace (prefixWord ++ tailWord_268609) baseStart_268609 baseEnd_268609 := by
    simpa [prefixWord, tailWord_268609, baseEnd_268609] using wordTrace_append hprefix tailTrace_268609
  have hstable : (prefixWord ++ tailWord_268609).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_268609).length < 2 ^ (prefixWord ++ tailWord_268609).sum := by decide
  have hdescent : baseEnd_268609 < baseStart_268609 := by decide
  rcases family_descends (prefixWord ++ tailWord_268609) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_268616 : List Nat := [2, 1, 3, 1, 1, 2, 5, 2, 3]
def baseStart_268616 : Nat := 118140960795 + 268616 * 2 ^ 59
def prefixEnd_268616 : Nat := 4983230072969 + 3 ^ 40 * 268616 * 2
def baseEnd_268616 : Nat := 122603661767312242101923

theorem tailTrace_268616 : CollatzResearch.WordTrace tailWord_268616 prefixEnd_268616 122603661767312242101923 := by
  unfold tailWord_268616
  simp only [CollatzResearch.WordTrace]
  refine ⟨4898615197428791402768851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6531486929905055203691801 4898615197428791402768851)
  ·
    refine ⟨7347922796143187104153277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4898615197428791402768851 7347922796143187104153277)
    ·
      refine ⟨2755471048553695164057479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7347922796143187104153277 2755471048553695164057479)
      ·
        refine ⟨4133206572830542746086219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2755471048553695164057479 4133206572830542746086219)
        ·
          refine ⟨6199809859245814119129329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4133206572830542746086219 6199809859245814119129329)
          ·
            refine ⟨4649857394434360589346997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6199809859245814119129329 4649857394434360589346997)
            ·
              refine ⟨435924130728221305251281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 4649857394434360589346997 435924130728221305251281)
              ·
                refine ⟨326943098046165978938461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 435924130728221305251281 326943098046165978938461)
                ·
                  refine ⟨122603661767312242101923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 326943098046165978938461 122603661767312242101923)
                  ·
                    rfl

theorem cell20_268616_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 5, 2, 3].length) (baseStart_268616 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_268616 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_268616 prefixEnd_268616 := by exact prefixLift 268616
  have htrace : WordTrace (prefixWord ++ tailWord_268616) baseStart_268616 baseEnd_268616 := by
    simpa [prefixWord, tailWord_268616, baseEnd_268616] using wordTrace_append hprefix tailTrace_268616
  have hstable : (prefixWord ++ tailWord_268616).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_268616).length < 2 ^ (prefixWord ++ tailWord_268616).sum := by decide
  have hdescent : baseEnd_268616 < baseStart_268616 := by decide
  rcases family_descends (prefixWord ++ tailWord_268616) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_268647 : List Nat := [1, 1, 5, 1, 3, 1, 4, 4]
def baseStart_268647 : Nat := 118140960795 + 268647 * 2 ^ 59
def prefixEnd_268647 : Nat := 4983230072969 + 3 ^ 40 * 268647 * 2
def baseEnd_268647 : Nat := 40872603670671304022821

theorem tailTrace_268647 : CollatzResearch.WordTrace tailWord_268647 prefixEnd_268647 40872603670671304022821 := by
  unfold tailWord_268647
  simp only [CollatzResearch.WordTrace]
  refine ⟨9798361057745275099916195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6532240705163516733277463 9798361057745275099916195)
  ·
    refine ⟨14697541586617912649874293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9798361057745275099916195 14697541586617912649874293)
    ·
      refine ⟨1377894523745429310925715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 14697541586617912649874293 1377894523745429310925715)
      ·
        refine ⟨2066841785618143966388573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1377894523745429310925715 2066841785618143966388573)
        ·
          refine ⟨775065669606803987395715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2066841785618143966388573 775065669606803987395715)
          ·
            refine ⟨1162598504410205981093573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 775065669606803987395715 1162598504410205981093573)
            ·
              refine ⟨217987219576913621455045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1162598504410205981093573 217987219576913621455045)
              ·
                refine ⟨40872603670671304022821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 217987219576913621455045 40872603670671304022821)
                ·
                  rfl

theorem cell20_268647_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 1, 4, 4].length) (baseStart_268647 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_268647 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_268647 prefixEnd_268647 := by exact prefixLift 268647
  have htrace : WordTrace (prefixWord ++ tailWord_268647) baseStart_268647 baseEnd_268647 := by
    simpa [prefixWord, tailWord_268647, baseEnd_268647] using wordTrace_append hprefix tailTrace_268647
  have hstable : (prefixWord ++ tailWord_268647).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_268647).length < 2 ^ (prefixWord ++ tailWord_268647).sum := by decide
  have hdescent : baseEnd_268647 < baseStart_268647 := by decide
  rcases family_descends (prefixWord ++ tailWord_268647) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_268651 : List Nat := [1, 1, 1, 1, 2, 2, 2, 10]
def baseStart_268651 : Nat := 118140960795 + 268651 * 2 ^ 59
def prefixEnd_268651 : Nat := 4983230072969 + 3 ^ 40 * 268651 * 2
def baseEnd_268651 : Nat := 40873212240335891978371

theorem tailTrace_268651 : CollatzResearch.WordTrace tailWord_268651 prefixEnd_268651 40873212240335891978371 := by
  unfold tailWord_268651
  simp only [CollatzResearch.WordTrace]
  refine ⟨9798506949730783783061807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6532337966487189188707871 9798506949730783783061807)
  ·
    refine ⟨14697760424596175674592711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9798506949730783783061807 14697760424596175674592711)
    ·
      refine ⟨22046640636894263511889067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14697760424596175674592711 22046640636894263511889067)
      ·
        refine ⟨33069960955341395267833601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22046640636894263511889067 33069960955341395267833601)
        ·
          refine ⟨24802470716506046450875201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33069960955341395267833601 24802470716506046450875201)
          ·
            refine ⟨18601853037379534838156401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24802470716506046450875201 18601853037379534838156401)
            ·
              refine ⟨13951389778034651128617301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18601853037379534838156401 13951389778034651128617301)
              ·
                refine ⟨40873212240335891978371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 13951389778034651128617301 40873212240335891978371)
                ·
                  rfl

theorem cell20_268651_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 2, 10].length) (baseStart_268651 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_268651 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_268651 prefixEnd_268651 := by exact prefixLift 268651
  have htrace : WordTrace (prefixWord ++ tailWord_268651) baseStart_268651 baseEnd_268651 := by
    simpa [prefixWord, tailWord_268651, baseEnd_268651] using wordTrace_append hprefix tailTrace_268651
  have hstable : (prefixWord ++ tailWord_268651).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_268651).length < 2 ^ (prefixWord ++ tailWord_268651).sum := by decide
  have hdescent : baseEnd_268651 < baseStart_268651 := by decide
  rcases family_descends (prefixWord ++ tailWord_268651) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_268674 : List Nat := [3, 4, 2, 1, 2, 2, 1, 1, 4]
def baseStart_268674 : Nat := 118140960795 + 268674 * 2 ^ 59
def prefixEnd_268674 : Nat := 4983230072969 + 3 ^ 40 * 268674 * 2
def baseEnd_268674 : Nat := 122630134547721818168353

theorem tailTrace_268674 : CollatzResearch.WordTrace tailWord_268674 prefixEnd_268674 122630134547721818168353 := by
  unfold tailWord_268674
  simp only [CollatzResearch.WordTrace]
  refine ⟨2449836457161864677787269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6532897219098305807432717 2449836457161864677787269)
  ·
    refine ⟨459344335717849627085113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 2449836457161864677787269 459344335717849627085113)
    ·
      refine ⟨344508251788387220313835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 459344335717849627085113 344508251788387220313835)
      ·
        refine ⟨516762377682580830470753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 344508251788387220313835 516762377682580830470753)
        ·
          refine ⟨387571783261935622853065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 516762377682580830470753 387571783261935622853065)
          ·
            refine ⟨290678837446451717139799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 387571783261935622853065 290678837446451717139799)
            ·
              refine ⟨436018256169677575709699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 290678837446451717139799 436018256169677575709699)
              ·
                refine ⟨654027384254516363564549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 436018256169677575709699 654027384254516363564549)
                ·
                  refine ⟨122630134547721818168353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 654027384254516363564549 122630134547721818168353)
                  ·
                    rfl

theorem cell20_268674_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 2, 2, 1, 1, 4].length) (baseStart_268674 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_268674 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_268674 prefixEnd_268674 := by exact prefixLift 268674
  have htrace : WordTrace (prefixWord ++ tailWord_268674) baseStart_268674 baseEnd_268674 := by
    simpa [prefixWord, tailWord_268674, baseEnd_268674] using wordTrace_append hprefix tailTrace_268674
  have hstable : (prefixWord ++ tailWord_268674).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_268674).length < 2 ^ (prefixWord ++ tailWord_268674).sum := by decide
  have hdescent : baseEnd_268674 < baseStart_268674 := by decide
  rcases family_descends (prefixWord ++ tailWord_268674) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_268706 : List Nat := [3, 3, 1, 2, 1, 1, 1, 8]
def baseStart_268706 : Nat := 118140960795 + 268706 * 2 ^ 59
def prefixEnd_268706 : Nat := 4983230072969 + 3 ^ 40 * 268706 * 2
def baseEnd_268706 : Nat := 40881580073223976367185

theorem tailTrace_268706 : CollatzResearch.WordTrace tailWord_268706 prefixEnd_268706 40881580073223976367185 := by
  unfold tailWord_268706
  simp only [CollatzResearch.WordTrace]
  refine ⟨2450128241132882044078493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6533675309687685450875981 2450128241132882044078493)
  ·
    refine ⟨918798090424830766529435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2450128241132882044078493 918798090424830766529435)
    ·
      refine ⟨1378197135637246149794153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 918798090424830766529435 1378197135637246149794153)
      ·
        refine ⟨1033647851727934612345615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1378197135637246149794153 1033647851727934612345615)
        ·
          refine ⟨1550471777591901918518423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1033647851727934612345615 1550471777591901918518423)
          ·
            refine ⟨2325707666387852877777635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1550471777591901918518423 2325707666387852877777635)
            ·
              refine ⟨3488561499581779316666453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2325707666387852877777635 3488561499581779316666453)
              ·
                refine ⟨40881580073223976367185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 3488561499581779316666453 40881580073223976367185)
                ·
                  rfl

theorem cell20_268706_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 1, 8].length) (baseStart_268706 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_268706 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_268706 prefixEnd_268706 := by exact prefixLift 268706
  have htrace : WordTrace (prefixWord ++ tailWord_268706) baseStart_268706 baseEnd_268706 := by
    simpa [prefixWord, tailWord_268706, baseEnd_268706] using wordTrace_append hprefix tailTrace_268706
  have hstable : (prefixWord ++ tailWord_268706).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_268706).length < 2 ^ (prefixWord ++ tailWord_268706).sum := by decide
  have hdescent : baseEnd_268706 < baseStart_268706 := by decide
  rcases family_descends (prefixWord ++ tailWord_268706) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_268727 : List Nat := [1, 1, 3, 1, 3, 11]
def baseStart_268727 : Nat := 118140960795 + 268727 * 2 ^ 59
def prefixEnd_268727 : Nat := 4983230072969 + 3 ^ 40 * 268727 * 2
def baseEnd_268727 : Nat := 4542752784884784792647

theorem tailTrace_268727 : CollatzResearch.WordTrace tailWord_268727 prefixEnd_268727 4542752784884784792647 := by
  unfold tailWord_268727
  simp only [CollatzResearch.WordTrace]
  refine ⟨9801278897455448762828435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6534185931636965841885623 9801278897455448762828435)
  ·
    refine ⟨14701918346183173144242653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9801278897455448762828435 14701918346183173144242653)
    ·
      refine ⟨5513219379818689929090995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14701918346183173144242653 5513219379818689929090995)
      ·
        refine ⟨8269829069728034893636493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5513219379818689929090995 8269829069728034893636493)
        ·
          refine ⟨3101185901148013085113685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8269829069728034893636493 3101185901148013085113685)
          ·
            refine ⟨4542752784884784792647, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 3101185901148013085113685 4542752784884784792647)
            ·
              rfl

theorem cell20_268727_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 11].length) (baseStart_268727 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_268727 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_268727 prefixEnd_268727 := by exact prefixLift 268727
  have htrace : WordTrace (prefixWord ++ tailWord_268727) baseStart_268727 baseEnd_268727 := by
    simpa [prefixWord, tailWord_268727, baseEnd_268727] using wordTrace_append hprefix tailTrace_268727
  have hstable : (prefixWord ++ tailWord_268727).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_268727).length < 2 ^ (prefixWord ++ tailWord_268727).sum := by decide
  have hdescent : baseEnd_268727 < baseStart_268727 := by decide
  rcases family_descends (prefixWord ++ tailWord_268727) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_268733 : List Nat := [1, 4, 1, 2, 2, 2, 4, 2, 2]
def baseStart_268733 : Nat := 118140960795 + 268733 * 2 ^ 59
def prefixEnd_268733 : Nat := 4983230072969 + 3 ^ 40 * 268733 * 2
def baseEnd_268733 : Nat := 122657063755379835201445

theorem tailTrace_268733 : CollatzResearch.WordTrace tailWord_268733 prefixEnd_268733 122657063755379835201445 := by
  unfold tailWord_268733
  simp only [CollatzResearch.WordTrace]
  refine ⟨9801497735433711787546853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6534331823622474525031235 9801497735433711787546853)
  ·
    refine ⟨1837780825393820960165035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 9801497735433711787546853 1837780825393820960165035)
    ·
      refine ⟨2756671238090731440247553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1837780825393820960165035 2756671238090731440247553)
      ·
        refine ⟨2067503428568048580185665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2756671238090731440247553 2067503428568048580185665)
        ·
          refine ⟨1550627571426036435139249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2067503428568048580185665 1550627571426036435139249)
          ·
            refine ⟨1162970678569527326354437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1550627571426036435139249 1162970678569527326354437)
            ·
              refine ⟨218057002231786373691457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1162970678569527326354437 218057002231786373691457)
              ·
                refine ⟨163542751673839780268593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 218057002231786373691457 163542751673839780268593)
                ·
                  refine ⟨122657063755379835201445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 163542751673839780268593 122657063755379835201445)
                  ·
                    rfl

theorem cell20_268733_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 2, 4, 2, 2].length) (baseStart_268733 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_268733 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_268733 prefixEnd_268733 := by exact prefixLift 268733
  have htrace : WordTrace (prefixWord ++ tailWord_268733) baseStart_268733 baseEnd_268733 := by
    simpa [prefixWord, tailWord_268733, baseEnd_268733] using wordTrace_append hprefix tailTrace_268733
  have hstable : (prefixWord ++ tailWord_268733).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_268733).length < 2 ^ (prefixWord ++ tailWord_268733).sum := by decide
  have hdescent : baseEnd_268733 < baseStart_268733 := by decide
  rcases family_descends (prefixWord ++ tailWord_268733) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_268740 : List Nat := [2, 3, 3, 2, 2, 2, 1, 5]
def baseStart_268740 : Nat := 118140960795 + 268740 * 2 ^ 59
def prefixEnd_268740 : Nat := 4983230072969 + 3 ^ 40 * 268740 * 2
def baseEnd_268740 : Nat := 40886752915372973989361

theorem tailTrace_268740 : CollatzResearch.WordTrace tailWord_268740 prefixEnd_268740 40886752915372973989361 := by
  unfold tailWord_268740
  simp only [CollatzResearch.WordTrace]
  refine ⟨4900876523204175991525837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6534502030938901322034449 4900876523204175991525837)
  ·
    refine ⟨1837828696201565996822189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4900876523204175991525837 1837828696201565996822189)
    ·
      refine ⟨689185761075587248808321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1837828696201565996822189 689185761075587248808321)
      ·
        refine ⟨516889320806690436606241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 689185761075587248808321 516889320806690436606241)
        ·
          refine ⟨387666990605017827454681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 516889320806690436606241 387666990605017827454681)
          ·
            refine ⟨290750242953763370591011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 387666990605017827454681 290750242953763370591011)
            ·
              refine ⟨436125364430645055886517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 290750242953763370591011 436125364430645055886517)
              ·
                refine ⟨40886752915372973989361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 436125364430645055886517 40886752915372973989361)
                ·
                  rfl

theorem cell20_268740_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 2, 2, 1, 5].length) (baseStart_268740 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_268740 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_268740 prefixEnd_268740 := by exact prefixLift 268740
  have htrace : WordTrace (prefixWord ++ tailWord_268740) baseStart_268740 baseEnd_268740 := by
    simpa [prefixWord, tailWord_268740, baseEnd_268740] using wordTrace_append hprefix tailTrace_268740
  have hstable : (prefixWord ++ tailWord_268740).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_268740).length < 2 ^ (prefixWord ++ tailWord_268740).sum := by decide
  have hdescent : baseEnd_268740 < baseStart_268740 := by decide
  rcases family_descends (prefixWord ++ tailWord_268740) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_268744 : List Nat := [2, 1, 3, 1, 3, 2, 3, 5]
def baseStart_268744 : Nat := 118140960795 + 268744 * 2 ^ 59
def prefixEnd_268744 : Nat := 4983230072969 + 3 ^ 40 * 268744 * 2
def baseEnd_268744 : Nat := 40887361485037561944911

theorem tailTrace_268744 : CollatzResearch.WordTrace tailWord_268744 prefixEnd_268744 40887361485037561944911 := by
  unfold tailWord_268744
  simp only [CollatzResearch.WordTrace]
  refine ⟨4900949469196930333098643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6534599292262573777464857 4900949469196930333098643)
  ·
    refine ⟨7351424203795395499647965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4900949469196930333098643 7351424203795395499647965)
    ·
      refine ⟨2756784076423273312367987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7351424203795395499647965 2756784076423273312367987)
      ·
        refine ⟨4135176114634909968551981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2756784076423273312367987 4135176114634909968551981)
        ·
          refine ⟨1550691042988091238206993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4135176114634909968551981 1550691042988091238206993)
          ·
            refine ⟨1163018282241068428655245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1550691042988091238206993 1163018282241068428655245)
            ·
              refine ⟨436131855840400660745717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1163018282241068428655245 436131855840400660745717)
              ·
                refine ⟨40887361485037561944911, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 436131855840400660745717 40887361485037561944911)
                ·
                  rfl

theorem cell20_268744_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 2, 3, 5].length) (baseStart_268744 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_268744 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_268744 prefixEnd_268744 := by exact prefixLift 268744
  have htrace : WordTrace (prefixWord ++ tailWord_268744) baseStart_268744 baseEnd_268744 := by
    simpa [prefixWord, tailWord_268744, baseEnd_268744] using wordTrace_append hprefix tailTrace_268744
  have hstable : (prefixWord ++ tailWord_268744).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_268744).length < 2 ^ (prefixWord ++ tailWord_268744).sum := by decide
  have hdescent : baseEnd_268744 < baseStart_268744 := by decide
  rcases family_descends (prefixWord ++ tailWord_268744) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_268771 : List Nat := [1, 1, 1, 6, 3, 1, 2, 3, 2]
def baseStart_268771 : Nat := 118140960795 + 268771 * 2 ^ 59
def prefixEnd_268771 : Nat := 4983230072969 + 3 ^ 40 * 268771 * 2
def baseEnd_268771 : Nat := 122674407990820591934623

theorem tailTrace_268771 : CollatzResearch.WordTrace tailWord_268771 prefixEnd_268771 122674407990820591934623 := by
  unfold tailWord_268771
  simp only [CollatzResearch.WordTrace]
  refine ⟨9802883709296044277430167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6535255806197362851620111 9802883709296044277430167)
  ·
    refine ⟨14704325563944066416145251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9802883709296044277430167 14704325563944066416145251)
    ·
      refine ⟨22056488345916099624217877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14704325563944066416145251 22056488345916099624217877)
      ·
        refine ⟨1033897891214817169885213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 22056488345916099624217877 1033897891214817169885213)
        ·
          refine ⟨387711709205556438706955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1033897891214817169885213 387711709205556438706955)
          ·
            refine ⟨581567563808334658060433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 387711709205556438706955 581567563808334658060433)
            ·
              refine ⟨436175672856250993545325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 581567563808334658060433 436175672856250993545325)
              ·
                refine ⟨163565877321094122579497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 436175672856250993545325 163565877321094122579497)
                ·
                  refine ⟨122674407990820591934623, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 163565877321094122579497 122674407990820591934623)
                  ·
                    rfl

theorem cell20_268771_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 3, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 3, 1, 2, 3, 2].length) (baseStart_268771 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_268771 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_268771 prefixEnd_268771 := by exact prefixLift 268771
  have htrace : WordTrace (prefixWord ++ tailWord_268771) baseStart_268771 baseEnd_268771 := by
    simpa [prefixWord, tailWord_268771, baseEnd_268771] using wordTrace_append hprefix tailTrace_268771
  have hstable : (prefixWord ++ tailWord_268771).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_268771).length < 2 ^ (prefixWord ++ tailWord_268771).sum := by decide
  have hdescent : baseEnd_268771 < baseStart_268771 := by decide
  rcases family_descends (prefixWord ++ tailWord_268771) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_268782 : List Nat := [4, 1, 2, 1, 2, 3, 7]
def baseStart_268782 : Nat := 118140960795 + 268782 * 2 ^ 59
def prefixEnd_268782 : Nat := 4983230072969 + 3 ^ 40 * 268782 * 2
def baseEnd_268782 : Nat := 13631047632283715840879

theorem tailTrace_268782 : CollatzResearch.WordTrace tailWord_268782 prefixEnd_268782 13631047632283715840879 := by
  unfold tailWord_268782
  simp only [CollatzResearch.WordTrace]
  refine ⟨1225410614032024144510075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 6535523274837462104053733 1225410614032024144510075)
  ·
    refine ⟨1838115921048036216765113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1225410614032024144510075 1838115921048036216765113)
    ·
      refine ⟨1378586940786027162573835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1838115921048036216765113 1378586940786027162573835)
      ·
        refine ⟨2067880411179040743860753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1378586940786027162573835 2067880411179040743860753)
        ·
          refine ⟨1550910308384280557895565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2067880411179040743860753 1550910308384280557895565)
          ·
            refine ⟨581591365644105209210837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1550910308384280557895565 581591365644105209210837)
            ·
              refine ⟨13631047632283715840879, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 581591365644105209210837 13631047632283715840879)
              ·
                rfl

theorem cell20_268782_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 3, 7].length) (baseStart_268782 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_268782 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_268782 prefixEnd_268782 := by exact prefixLift 268782
  have htrace : WordTrace (prefixWord ++ tailWord_268782) baseStart_268782 baseEnd_268782 := by
    simpa [prefixWord, tailWord_268782, baseEnd_268782] using wordTrace_append hprefix tailTrace_268782
  have hstable : (prefixWord ++ tailWord_268782).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_268782).length < 2 ^ (prefixWord ++ tailWord_268782).sum := by decide
  have hdescent : baseEnd_268782 < baseStart_268782 := by decide
  rcases family_descends (prefixWord ++ tailWord_268782) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_268803 : List Nat := [1, 1, 1, 3, 2, 1, 4, 7]
def baseStart_268803 : Nat := 118140960795 + 268803 * 2 ^ 59
def prefixEnd_268803 : Nat := 4983230072969 + 3 ^ 40 * 268803 * 2
def baseEnd_268803 : Nat := 40896337887590234289275

theorem tailTrace_268803 : CollatzResearch.WordTrace tailWord_268803 prefixEnd_268803 40896337887590234289275 := by
  unfold tailWord_268803
  simp only [CollatzResearch.WordTrace]
  refine ⟨9804050845180113742595063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6536033896786742495063375 9804050845180113742595063)
  ·
    refine ⟨14706076267770170613892595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9804050845180113742595063 14706076267770170613892595)
    ·
      refine ⟨22059114401655255920838893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14706076267770170613892595 22059114401655255920838893)
      ·
        refine ⟨8272167900620720970314585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 22059114401655255920838893 8272167900620720970314585)
        ·
          refine ⟨6204125925465540727735939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8272167900620720970314585 6204125925465540727735939)
          ·
            refine ⟨9306188888198311091603909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6204125925465540727735939 9306188888198311091603909)
            ·
              refine ⟨1744910416537183329675733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9306188888198311091603909 1744910416537183329675733)
              ·
                refine ⟨40896337887590234289275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1744910416537183329675733 40896337887590234289275)
                ·
                  rfl

theorem cell20_268803_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 4, 7].length) (baseStart_268803 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_268803 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_268803 prefixEnd_268803 := by exact prefixLift 268803
  have htrace : WordTrace (prefixWord ++ tailWord_268803) baseStart_268803 baseEnd_268803 := by
    simpa [prefixWord, tailWord_268803, baseEnd_268803] using wordTrace_append hprefix tailTrace_268803
  have hstable : (prefixWord ++ tailWord_268803).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_268803).length < 2 ^ (prefixWord ++ tailWord_268803).sum := by decide
  have hdescent : baseEnd_268803 < baseStart_268803 := by decide
  rcases family_descends (prefixWord ++ tailWord_268803) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_268858 : List Nat := [3, 1, 1, 1, 3, 4, 2, 5]
def baseStart_268858 : Nat := 118140960795 + 268858 * 2 ^ 59
def prefixEnd_268858 : Nat := 4983230072969 + 3 ^ 40 * 268858 * 2
def baseEnd_268858 : Nat := 40904705720478318678089

theorem tailTrace_268858 : CollatzResearch.WordTrace tailWord_268858 prefixEnd_268858 40904705720478318678089 := by
  unfold tailWord_268858
  simp only [CollatzResearch.WordTrace]
  refine ⟨2451514214995214533961807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6537371239987238757231485 2451514214995214533961807)
  ·
    refine ⟨3677271322492821800942711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2451514214995214533961807 3677271322492821800942711)
    ·
      refine ⟨5515906983739232701414067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3677271322492821800942711 5515906983739232701414067)
      ·
        refine ⟨8273860475608849052121101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5515906983739232701414067 8273860475608849052121101)
        ·
          refine ⟨3102697678353318394545413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8273860475608849052121101 3102697678353318394545413)
          ·
            refine ⟨581755814691247198977265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3102697678353318394545413 581755814691247198977265)
            ·
              refine ⟨436316861018435399232949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 581755814691247198977265 436316861018435399232949)
              ·
                refine ⟨40904705720478318678089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 436316861018435399232949 40904705720478318678089)
                ·
                  rfl

theorem cell20_268858_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 4, 2, 5].length) (baseStart_268858 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_268858 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_268858 prefixEnd_268858 := by exact prefixLift 268858
  have htrace : WordTrace (prefixWord ++ tailWord_268858) baseStart_268858 baseEnd_268858 := by
    simpa [prefixWord, tailWord_268858, baseEnd_268858] using wordTrace_append hprefix tailTrace_268858
  have hstable : (prefixWord ++ tailWord_268858).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_268858).length < 2 ^ (prefixWord ++ tailWord_268858).sum := by decide
  have hdescent : baseEnd_268858 < baseStart_268858 := by decide
  rcases family_descends (prefixWord ++ tailWord_268858) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_268861 : List Nat := [1, 4, 1, 3, 2, 1, 4, 1, 3]
def baseStart_268861 : Nat := 118140960795 + 268861 * 2 ^ 59
def prefixEnd_268861 : Nat := 4983230072969 + 3 ^ 40 * 268861 * 2
def baseEnd_268861 : Nat := 122715486443180278934255

theorem tailTrace_268861 : CollatzResearch.WordTrace tailWord_268861 prefixEnd_268861 122715486443180278934255 := by
  unfold tailWord_268861
  simp only [CollatzResearch.WordTrace]
  refine ⟨9806166278969989648206437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6537444185979993098804291 9806166278969989648206437)
  ·
    refine ⟨1838656177306873059038707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 9806166278969989648206437 1838656177306873059038707)
    ·
      refine ⟨2757984265960309588558061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1838656177306873059038707 2757984265960309588558061)
      ·
        refine ⟨1034244099735116095709273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2757984265960309588558061 1034244099735116095709273)
        ·
          refine ⟨775683074801337071781955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1034244099735116095709273 775683074801337071781955)
          ·
            refine ⟨1163524612202005607672933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 775683074801337071781955 1163524612202005607672933)
            ·
              refine ⟨218160864787876051438675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1163524612202005607672933 218160864787876051438675)
              ·
                refine ⟨327241297181814077158013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 218160864787876051438675 327241297181814077158013)
                ·
                  refine ⟨122715486443180278934255, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 327241297181814077158013 122715486443180278934255)
                  ·
                    rfl

theorem cell20_268861_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 1, 4, 1, 3].length) (baseStart_268861 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_268861 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_268861 prefixEnd_268861 := by exact prefixLift 268861
  have htrace : WordTrace (prefixWord ++ tailWord_268861) baseStart_268861 baseEnd_268861 := by
    simpa [prefixWord, tailWord_268861, baseEnd_268861] using wordTrace_append hprefix tailTrace_268861
  have hstable : (prefixWord ++ tailWord_268861).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_268861).length < 2 ^ (prefixWord ++ tailWord_268861).sum := by decide
  have hdescent : baseEnd_268861 < baseStart_268861 := by decide
  rcases family_descends (prefixWord ++ tailWord_268861) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_268872 : List Nat := [2, 1, 3, 1, 1, 1, 1, 6, 4]
def baseStart_268872 : Nat := 118140960795 + 268872 * 2 ^ 59
def prefixEnd_268872 : Nat := 4983230072969 + 3 ^ 40 * 268872 * 2
def baseEnd_268872 : Nat := 122720507142913129567543

theorem tailTrace_268872 : CollatzResearch.WordTrace tailWord_268872 prefixEnd_268872 122720507142913129567543 := by
  unfold tailWord_268872
  simp only [CollatzResearch.WordTrace]
  refine ⟨4903283740965069263428435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6537711654620092351237913 4903283740965069263428435)
  ·
    refine ⟨7354925611447603895142653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4903283740965069263428435 7354925611447603895142653)
    ·
      refine ⟨2758097104292851460678495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7354925611447603895142653 2758097104292851460678495)
      ·
        refine ⟨4137145656439277191017743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2758097104292851460678495 4137145656439277191017743)
        ·
          refine ⟨6205718484658915786526615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4137145656439277191017743 6205718484658915786526615)
          ·
            refine ⟨9308577726988373679789923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6205718484658915786526615 9308577726988373679789923)
            ·
              refine ⟨13962866590482560519684885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9308577726988373679789923 13962866590482560519684885)
              ·
                refine ⟨654509371428870024360229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 13962866590482560519684885 654509371428870024360229)
                ·
                  refine ⟨122720507142913129567543, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 654509371428870024360229 122720507142913129567543)
                  ·
                    rfl

theorem cell20_268872_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 1, 6, 4].length) (baseStart_268872 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_268872 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_268872 prefixEnd_268872 := by exact prefixLift 268872
  have htrace : WordTrace (prefixWord ++ tailWord_268872) baseStart_268872 baseEnd_268872 := by
    simpa [prefixWord, tailWord_268872, baseEnd_268872] using wordTrace_append hprefix tailTrace_268872
  have hstable : (prefixWord ++ tailWord_268872).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_268872).length < 2 ^ (prefixWord ++ tailWord_268872).sum := by decide
  have hdescent : baseEnd_268872 < baseStart_268872 := by decide
  rcases family_descends (prefixWord ++ tailWord_268872) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_268879 : List Nat := [1, 1, 2, 1, 1, 2, 6, 6]
def baseStart_268879 : Nat := 118140960795 + 268879 * 2 ^ 59
def prefixEnd_268879 : Nat := 4983230072969 + 3 ^ 40 * 268879 * 2
def baseEnd_268879 : Nat := 40907900711217405444727

theorem tailTrace_268879 : CollatzResearch.WordTrace tailWord_268879 prefixEnd_268879 40907900711217405444727 := by
  unfold tailWord_268879
  simp only [CollatzResearch.WordTrace]
  refine ⟨9806822792904778722361691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6537881861936519148241127 9806822792904778722361691)
  ·
    refine ⟨14710234189357168083542537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9806822792904778722361691 14710234189357168083542537)
    ·
      refine ⟨11032675642017876062656903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14710234189357168083542537 11032675642017876062656903)
      ·
        refine ⟨16549013463026814093985355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11032675642017876062656903 16549013463026814093985355)
        ·
          refine ⟨24823520194540221140978033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16549013463026814093985355 24823520194540221140978033)
          ·
            refine ⟨18617640145905165855733525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24823520194540221140978033 18617640145905165855733525)
            ·
              refine ⟨872701881839304649487509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 18617640145905165855733525 872701881839304649487509)
              ·
                refine ⟨40907900711217405444727, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 872701881839304649487509 40907900711217405444727)
                ·
                  rfl

theorem cell20_268879_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 6, 6].length) (baseStart_268879 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_268879 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_268879 prefixEnd_268879 := by exact prefixLift 268879
  have htrace : WordTrace (prefixWord ++ tailWord_268879) baseStart_268879 baseEnd_268879 := by
    simpa [prefixWord, tailWord_268879, baseEnd_268879] using wordTrace_append hprefix tailTrace_268879
  have hstable : (prefixWord ++ tailWord_268879).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_268879).length < 2 ^ (prefixWord ++ tailWord_268879).sum := by decide
  have hdescent : baseEnd_268879 < baseStart_268879 := by decide
  rcases family_descends (prefixWord ++ tailWord_268879) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_268898 : List Nat := [3, 3, 2, 3, 2, 1, 2, 2, 2]
def baseStart_268898 : Nat := 118140960795 + 268898 * 2 ^ 59
def prefixEnd_268898 : Nat := 4983230072969 + 3 ^ 40 * 268898 * 2
def baseEnd_268898 : Nat := 122732374251372594700771

theorem tailTrace_268898 : CollatzResearch.WordTrace tailWord_268898 prefixEnd_268898 122732374251372594700771 := by
  unfold tailWord_268898
  simp only [CollatzResearch.WordTrace]
  refine ⟨2451878944958986241825837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6538343853223963311535565 2451878944958986241825837)
  ·
    refine ⟨919454604359619840684689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2451878944958986241825837 919454604359619840684689)
    ·
      refine ⟨689590953269714880513517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 919454604359619840684689 689590953269714880513517)
      ·
        refine ⟨258596607476143080192569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 689590953269714880513517 258596607476143080192569)
        ·
          refine ⟨193947455607107310144427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 258596607476143080192569 193947455607107310144427)
          ·
            refine ⟨290921183410660965216641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 193947455607107310144427 290921183410660965216641)
            ·
              refine ⟨218190887557995723912481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 290921183410660965216641 218190887557995723912481)
              ·
                refine ⟨163643165668496792934361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 218190887557995723912481 163643165668496792934361)
                ·
                  refine ⟨122732374251372594700771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 163643165668496792934361 122732374251372594700771)
                  ·
                    rfl

theorem cell20_268898_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 3, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 3, 2, 1, 2, 2, 2].length) (baseStart_268898 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_268898 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_268898 prefixEnd_268898 := by exact prefixLift 268898
  have htrace : WordTrace (prefixWord ++ tailWord_268898) baseStart_268898 baseEnd_268898 := by
    simpa [prefixWord, tailWord_268898, baseEnd_268898] using wordTrace_append hprefix tailTrace_268898
  have hstable : (prefixWord ++ tailWord_268898).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_268898).length < 2 ^ (prefixWord ++ tailWord_268898).sum := by decide
  have hdescent : baseEnd_268898 < baseStart_268898 := by decide
  rcases family_descends (prefixWord ++ tailWord_268898) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_268906 : List Nat := [3, 1, 3, 2, 1, 1, 3, 4, 2]
def baseStart_268906 : Nat := 118140960795 + 268906 * 2 ^ 59
def prefixEnd_268906 : Nat := 4983230072969 + 3 ^ 40 * 268906 * 2
def baseEnd_268906 : Nat := 122736025669360122434071

theorem tailTrace_268906 : CollatzResearch.WordTrace tailWord_268906 prefixEnd_268906 122736025669360122434071 := by
  unfold tailWord_268906
  simp only [CollatzResearch.WordTrace]
  refine ⟨2451951890951740583398643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6538538375871308222396381 2451951890951740583398643)
  ·
    refine ⟨3677927836427610875097965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2451951890951740583398643 3677927836427610875097965)
    ·
      refine ⟨1379222938660354078161737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3677927836427610875097965 1379222938660354078161737)
      ·
        refine ⟨1034417203995265558621303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1379222938660354078161737 1034417203995265558621303)
        ·
          refine ⟨1551625805992898337931955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1034417203995265558621303 1551625805992898337931955)
          ·
            refine ⟨2327438708989347506897933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1551625805992898337931955 2327438708989347506897933)
            ·
              refine ⟨872789515871005315086725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2327438708989347506897933 872789515871005315086725)
              ·
                refine ⟨163648034225813496578761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 872789515871005315086725 163648034225813496578761)
                ·
                  refine ⟨122736025669360122434071, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 163648034225813496578761 122736025669360122434071)
                  ·
                    rfl

theorem cell20_268906_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 3, 4, 2].length) (baseStart_268906 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_268906 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_268906 prefixEnd_268906 := by exact prefixLift 268906
  have htrace : WordTrace (prefixWord ++ tailWord_268906) baseStart_268906 baseEnd_268906 := by
    simpa [prefixWord, tailWord_268906, baseEnd_268906] using wordTrace_append hprefix tailTrace_268906
  have hstable : (prefixWord ++ tailWord_268906).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_268906).length < 2 ^ (prefixWord ++ tailWord_268906).sum := by decide
  have hdescent : baseEnd_268906 < baseStart_268906 := by decide
  rcases family_descends (prefixWord ++ tailWord_268906) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_268954 : List Nat := [3, 1, 1, 6, 1, 2, 1, 2, 3]
def baseStart_268954 : Nat := 118140960795 + 268954 * 2 ^ 59
def prefixEnd_268954 : Nat := 4983230072969 + 3 ^ 40 * 268954 * 2
def baseEnd_268954 : Nat := 122757934177285288833875

theorem tailTrace_268954 : CollatzResearch.WordTrace tailWord_268954 prefixEnd_268954 122757934177285288833875 := by
  unfold tailWord_268954
  simp only [CollatzResearch.WordTrace]
  refine ⟨2452389566908266632835479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6539705511755377687561277 2452389566908266632835479)
  ·
    refine ⟨3678584350362399949253219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2452389566908266632835479 3678584350362399949253219)
    ·
      refine ⟨5517876525543599923879829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3678584350362399949253219 5517876525543599923879829)
      ·
        refine ⟨258650462134856246431867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 5517876525543599923879829 258650462134856246431867)
        ·
          refine ⟨387975693202284369647801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 258650462134856246431867 387975693202284369647801)
          ·
            refine ⟨290981769901713277235851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 387975693202284369647801 290981769901713277235851)
            ·
              refine ⟨436472654852569915853777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 290981769901713277235851 436472654852569915853777)
              ·
                refine ⟨327354491139427436890333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 436472654852569915853777 327354491139427436890333)
                ·
                  refine ⟨122757934177285288833875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 327354491139427436890333 122757934177285288833875)
                  ·
                    rfl

theorem cell20_268954_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 6, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 6, 1, 2, 1, 2, 3].length) (baseStart_268954 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_268954 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_268954 prefixEnd_268954 := by exact prefixLift 268954
  have htrace : WordTrace (prefixWord ++ tailWord_268954) baseStart_268954 baseEnd_268954 := by
    simpa [prefixWord, tailWord_268954, baseEnd_268954] using wordTrace_append hprefix tailTrace_268954
  have hstable : (prefixWord ++ tailWord_268954).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_268954).length < 2 ^ (prefixWord ++ tailWord_268954).sum := by decide
  have hdescent : baseEnd_268954 < baseStart_268954 := by decide
  rcases family_descends (prefixWord ++ tailWord_268954) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_268958 : List Nat := [4, 3, 1, 1, 1, 1, 3, 1, 5]
def baseStart_268958 : Nat := 118140960795 + 268958 * 2 ^ 59
def prefixEnd_268958 : Nat := 4983230072969 + 3 ^ 40 * 268958 * 2
def baseEnd_268958 : Nat := 122759759886279052700525

theorem tailTrace_268958 : CollatzResearch.WordTrace tailWord_268958 prefixEnd_268958 122759759886279052700525 := by
  unfold tailWord_268958
  simp only [CollatzResearch.WordTrace]
  refine ⟨1226213019952321901810941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 6539802773079050142991685 1226213019952321901810941)
  ·
    refine ⟨459829882482120713179103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1226213019952321901810941 459829882482120713179103)
    ·
      refine ⟨689744823723181069768655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 459829882482120713179103 689744823723181069768655)
      ·
        refine ⟨1034617235584771604652983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 689744823723181069768655 1034617235584771604652983)
        ·
          refine ⟨1551925853377157406979475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1034617235584771604652983 1551925853377157406979475)
          ·
            refine ⟨2327888780065736110469213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1551925853377157406979475 2327888780065736110469213)
            ·
              refine ⟨872958292524651041425955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2327888780065736110469213 872958292524651041425955)
              ·
                refine ⟨1309437438786976562138933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 872958292524651041425955 1309437438786976562138933)
                ·
                  refine ⟨122759759886279052700525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1309437438786976562138933 122759759886279052700525)
                  ·
                    rfl

theorem cell20_268958_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 3, 1, 5].length) (baseStart_268958 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_268958 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_268958 prefixEnd_268958 := by exact prefixLift 268958
  have htrace : WordTrace (prefixWord ++ tailWord_268958) baseStart_268958 baseEnd_268958 := by
    simpa [prefixWord, tailWord_268958, baseEnd_268958] using wordTrace_append hprefix tailTrace_268958
  have hstable : (prefixWord ++ tailWord_268958).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_268958).length < 2 ^ (prefixWord ++ tailWord_268958).sum := by decide
  have hdescent : baseEnd_268958 < baseStart_268958 := by decide
  rcases family_descends (prefixWord ++ tailWord_268958) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_268986 : List Nat := [3, 1, 1, 1, 2, 3, 1, 4, 4]
def baseStart_268986 : Nat := 118140960795 + 268986 * 2 ^ 59
def prefixEnd_268986 : Nat := 4983230072969 + 3 ^ 40 * 268986 * 2
def baseEnd_268986 : Nat := 122772539849235399767077

theorem tailTrace_268986 : CollatzResearch.WordTrace tailWord_268986 prefixEnd_268986 122772539849235399767077 := by
  unfold tailWord_268986
  simp only [CollatzResearch.WordTrace]
  refine ⟨2452681350879283999126703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6540483602344757331004541 2452681350879283999126703)
  ·
    refine ⟨3679022026318925998690055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2452681350879283999126703 3679022026318925998690055)
    ·
      refine ⟨5518533039478388998035083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3679022026318925998690055 5518533039478388998035083)
      ·
        refine ⟨8277799559217583497052625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5518533039478388998035083 8277799559217583497052625)
        ·
          refine ⟨6208349669413187622789469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8277799559217583497052625 6208349669413187622789469)
          ·
            refine ⟨2328131126029945358546051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6208349669413187622789469 2328131126029945358546051)
            ·
              refine ⟨3492196689044918037819077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2328131126029945358546051 3492196689044918037819077)
              ·
                refine ⟨654786879195922132091077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3492196689044918037819077 654786879195922132091077)
                ·
                  refine ⟨122772539849235399767077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 654786879195922132091077 122772539849235399767077)
                  ·
                    rfl

theorem cell20_268986_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 1, 4, 4].length) (baseStart_268986 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_268986 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_268986 prefixEnd_268986 := by exact prefixLift 268986
  have htrace : WordTrace (prefixWord ++ tailWord_268986) baseStart_268986 baseEnd_268986 := by
    simpa [prefixWord, tailWord_268986, baseEnd_268986] using wordTrace_append hprefix tailTrace_268986
  have hstable : (prefixWord ++ tailWord_268986).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_268986).length < 2 ^ (prefixWord ++ tailWord_268986).sum := by decide
  have hdescent : baseEnd_268986 < baseStart_268986 := by decide
  rcases family_descends (prefixWord ++ tailWord_268986) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_268989 : List Nat := [1, 4, 1, 2, 1, 5, 2, 4]
def baseStart_268989 : Nat := 118140960795 + 268989 * 2 ^ 59
def prefixEnd_268989 : Nat := 4983230072969 + 3 ^ 40 * 268989 * 2
def baseEnd_268989 : Nat := 40924636376993574222355

theorem tailTrace_268989 : CollatzResearch.WordTrace tailWord_268989 prefixEnd_268989 40924636376993574222355 := by
  unfold tailWord_268989
  simp only [CollatzResearch.WordTrace]
  refine ⟨9810834822506267508866021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6540556548337511672577347 9810834822506267508866021)
  ·
    refine ⟨1839531529219925157912379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 9810834822506267508866021 1839531529219925157912379)
    ·
      refine ⟨2759297293829887736868569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1839531529219925157912379 2759297293829887736868569)
      ·
        refine ⟨2069472970372415802651427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2759297293829887736868569 2069472970372415802651427)
        ·
          refine ⟨3104209455558623703977141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2069472970372415802651427 3104209455558623703977141)
          ·
            refine ⟨291019636458620972247857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 3104209455558623703977141 291019636458620972247857)
            ·
              refine ⟨218264727343965729185893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 291019636458620972247857 218264727343965729185893)
              ·
                refine ⟨40924636376993574222355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 218264727343965729185893 40924636376993574222355)
                ·
                  rfl

theorem cell20_268989_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 5, 2, 4].length) (baseStart_268989 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_268989 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_268989 prefixEnd_268989 := by exact prefixLift 268989
  have htrace : WordTrace (prefixWord ++ tailWord_268989) baseStart_268989 baseEnd_268989 := by
    simpa [prefixWord, tailWord_268989, baseEnd_268989] using wordTrace_append hprefix tailTrace_268989
  have hstable : (prefixWord ++ tailWord_268989).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_268989).length < 2 ^ (prefixWord ++ tailWord_268989).sum := by decide
  have hdescent : baseEnd_268989 < baseStart_268989 := by decide
  rcases family_descends (prefixWord ++ tailWord_268989) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_269017 : List Nat := [1, 2, 1, 2, 3, 2, 2, 4, 3]
def baseStart_269017 : Nat := 118140960795 + 269017 * 2 ^ 59
def prefixEnd_269017 : Nat := 4983230072969 + 3 ^ 40 * 269017 * 2
def baseEnd_269017 : Nat := 122786689093937069733617

theorem tailTrace_269017 : CollatzResearch.WordTrace tailWord_269017 prefixEnd_269017 122786689093937069733617 := by
  unfold tailWord_269017
  simp only [CollatzResearch.WordTrace]
  refine ⟨9811856066404828290885305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6541237377603218860590203 9811856066404828290885305)
  ·
    refine ⟨7358892049803621218163979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9811856066404828290885305 7358892049803621218163979)
    ·
      refine ⟨11038338074705431827245969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7358892049803621218163979 11038338074705431827245969)
      ·
        refine ⟨8278753556029073870434477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11038338074705431827245969 8278753556029073870434477)
        ·
          refine ⟨3104532583510902701412929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8278753556029073870434477 3104532583510902701412929)
          ·
            refine ⟨2328399437633177026059697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3104532583510902701412929 2328399437633177026059697)
            ·
              refine ⟨1746299578224882769544773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2328399437633177026059697 1746299578224882769544773)
              ·
                refine ⟨327431170917165519289645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1746299578224882769544773 327431170917165519289645)
                ·
                  refine ⟨122786689093937069733617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 327431170917165519289645 122786689093937069733617)
                  ·
                    rfl

theorem cell20_269017_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 2, 4, 3].length) (baseStart_269017 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_269017 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_269017 prefixEnd_269017 := by exact prefixLift 269017
  have htrace : WordTrace (prefixWord ++ tailWord_269017) baseStart_269017 baseEnd_269017 := by
    simpa [prefixWord, tailWord_269017, baseEnd_269017] using wordTrace_append hprefix tailTrace_269017
  have hstable : (prefixWord ++ tailWord_269017).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_269017).length < 2 ^ (prefixWord ++ tailWord_269017).sum := by decide
  have hdescent : baseEnd_269017 < baseStart_269017 := by decide
  rcases family_descends (prefixWord ++ tailWord_269017) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_269020 : List Nat := [2, 2, 5, 1, 1, 1, 3, 1, 4]
def baseStart_269020 : Nat := 118140960795 + 269020 * 2 ^ 59
def prefixEnd_269020 : Nat := 4983230072969 + 3 ^ 40 * 269020 * 2
def baseEnd_269020 : Nat := 122788058375682392633605

theorem tailTrace_269020 : CollatzResearch.WordTrace tailWord_269020 prefixEnd_269020 122788058375682392633605 := by
  unfold tailWord_269020
  simp only [CollatzResearch.WordTrace]
  refine ⟨4905982742696979901622257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6541310323595973202163009 4905982742696979901622257)
  ·
    refine ⟨3679487057022734926216693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4905982742696979901622257 3679487057022734926216693)
    ·
      refine ⟨344951911595881399332815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 3679487057022734926216693 344951911595881399332815)
      ·
        refine ⟨517427867393822098999223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 344951911595881399332815 517427867393822098999223)
        ·
          refine ⟨776141801090733148498835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 517427867393822098999223 776141801090733148498835)
          ·
            refine ⟨1164212701636099722748253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 776141801090733148498835 1164212701636099722748253)
            ·
              refine ⟨436579763113537396030595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1164212701636099722748253 436579763113537396030595)
              ·
                refine ⟨654869644670306094045893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 436579763113537396030595 654869644670306094045893)
                ·
                  refine ⟨122788058375682392633605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 654869644670306094045893 122788058375682392633605)
                  ·
                    rfl

theorem cell20_269020_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 1, 3, 1, 4].length) (baseStart_269020 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_269020 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_269020 prefixEnd_269020 := by exact prefixLift 269020
  have htrace : WordTrace (prefixWord ++ tailWord_269020) baseStart_269020 baseEnd_269020 := by
    simpa [prefixWord, tailWord_269020, baseEnd_269020] using wordTrace_append hprefix tailTrace_269020
  have hstable : (prefixWord ++ tailWord_269020).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_269020).length < 2 ^ (prefixWord ++ tailWord_269020).sum := by decide
  have hdescent : baseEnd_269020 < baseStart_269020 := by decide
  rcases family_descends (prefixWord ++ tailWord_269020) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_269093 : List Nat := [1, 3, 1, 2, 3, 1, 1, 5, 3]
def baseStart_269093 : Nat := 118140960795 + 269093 * 2 ^ 59
def prefixEnd_269093 : Nat := 4983230072969 + 3 ^ 40 * 269093 * 2
def baseEnd_269093 : Nat := 122821377564818583199973

theorem tailTrace_269093 : CollatzResearch.WordTrace tailWord_269093 prefixEnd_269093 122821377564818583199973 := by
  unfold tailWord_269093
  simp only [CollatzResearch.WordTrace]
  refine ⟨9814628014129493270651933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6543085342752995513767955 9814628014129493270651933)
  ·
    refine ⟨3680485505298559976494475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9814628014129493270651933 3680485505298559976494475)
    ·
      refine ⟨5520728257947839964741713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3680485505298559976494475 5520728257947839964741713)
      ·
        refine ⟨4140546193460879973556285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5520728257947839964741713 4140546193460879973556285)
        ·
          refine ⟨1552704822547829990083607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4140546193460879973556285 1552704822547829990083607)
          ·
            refine ⟨2329057233821744985125411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1552704822547829990083607 2329057233821744985125411)
            ·
              refine ⟨3493585850732617477688117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2329057233821744985125411 3493585850732617477688117)
              ·
                refine ⟨327523673506182888533261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 3493585850732617477688117 327523673506182888533261)
                ·
                  refine ⟨122821377564818583199973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 327523673506182888533261 122821377564818583199973)
                  ·
                    rfl

theorem cell20_269093_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 1, 5, 3].length) (baseStart_269093 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_269093 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_269093 prefixEnd_269093 := by exact prefixLift 269093
  have htrace : WordTrace (prefixWord ++ tailWord_269093) baseStart_269093 baseEnd_269093 := by
    simpa [prefixWord, tailWord_269093, baseEnd_269093] using wordTrace_append hprefix tailTrace_269093
  have hstable : (prefixWord ++ tailWord_269093).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_269093).length < 2 ^ (prefixWord ++ tailWord_269093).sum := by decide
  have hdescent : baseEnd_269093 < baseStart_269093 := by decide
  rcases family_descends (prefixWord ++ tailWord_269093) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_269100 : List Nat := [2, 2, 1, 1, 1, 4, 3, 2, 4]
def baseStart_269100 : Nat := 118140960795 + 269100 * 2 ^ 59
def prefixEnd_269100 : Nat := 4983230072969 + 3 ^ 40 * 269100 * 2
def baseEnd_269100 : Nat := 122824572555557669966611

theorem tailTrace_269100 : CollatzResearch.WordTrace tailWord_269100 prefixEnd_269100 122824572555557669966611 := by
  unfold tailWord_269100
  simp only [CollatzResearch.WordTrace]
  refine ⟨4907441662552066733078377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6543255550069422310771169 4907441662552066733078377)
  ·
    refine ⟨3680581246914050049808783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4907441662552066733078377 3680581246914050049808783)
    ·
      refine ⟨5520871870371075074713175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3680581246914050049808783 5520871870371075074713175)
      ·
        refine ⟨8281307805556612612069763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5520871870371075074713175 8281307805556612612069763)
        ·
          refine ⟨12421961708334918918104645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8281307805556612612069763 12421961708334918918104645)
          ·
            refine ⟨2329117820312797297144621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 12421961708334918918104645 2329117820312797297144621)
            ·
              refine ⟨873419182617298986429233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2329117820312797297144621 873419182617298986429233)
              ·
                refine ⟨655064386962974239821925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 873419182617298986429233 655064386962974239821925)
                ·
                  refine ⟨122824572555557669966611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 655064386962974239821925 122824572555557669966611)
                  ·
                    rfl

theorem cell20_269100_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 4].length) (baseStart_269100 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_269100 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_269100 prefixEnd_269100 := by exact prefixLift 269100
  have htrace : WordTrace (prefixWord ++ tailWord_269100) baseStart_269100 baseEnd_269100 := by
    simpa [prefixWord, tailWord_269100, baseEnd_269100] using wordTrace_append hprefix tailTrace_269100
  have hstable : (prefixWord ++ tailWord_269100).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_269100).length < 2 ^ (prefixWord ++ tailWord_269100).sum := by decide
  have hdescent : baseEnd_269100 < baseStart_269100 := by decide
  rcases family_descends (prefixWord ++ tailWord_269100) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_269193 : List Nat := [1, 2, 1, 1, 5, 4, 1, 1, 4]
def baseStart_269193 : Nat := 118140960795 + 269193 * 2 ^ 59
def prefixEnd_269193 : Nat := 4983230072969 + 3 ^ 40 * 269193 * 2
def baseEnd_269193 : Nat := 122867020289662679866231

theorem tailTrace_269193 : CollatzResearch.WordTrace tailWord_269193 prefixEnd_269193 122867020289662679866231 := by
  unfold tailWord_269193
  simp only [CollatzResearch.WordTrace]
  refine ⟨9818275313767210349292233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6545516875844806899528155 9818275313767210349292233)
  ·
    refine ⟨7363706485325407761969175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9818275313767210349292233 7363706485325407761969175)
    ·
      refine ⟨11045559727988111642953763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7363706485325407761969175 11045559727988111642953763)
      ·
        refine ⟨16568339591982167464430645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11045559727988111642953763 16568339591982167464430645)
        ·
          refine ⟨1553281836748328199790373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 16568339591982167464430645 1553281836748328199790373)
          ·
            refine ⟨291240344390311537460695, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1553281836748328199790373 291240344390311537460695)
            ·
              refine ⟨436860516585467306191043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 291240344390311537460695 436860516585467306191043)
              ·
                refine ⟨655290774878200959286565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 436860516585467306191043 655290774878200959286565)
                ·
                  refine ⟨122867020289662679866231, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 655290774878200959286565 122867020289662679866231)
                  ·
                    rfl

theorem cell20_269193_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 4, 1, 1, 4].length) (baseStart_269193 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_269193 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_269193 prefixEnd_269193 := by exact prefixLift 269193
  have htrace : WordTrace (prefixWord ++ tailWord_269193) baseStart_269193 baseEnd_269193 := by
    simpa [prefixWord, tailWord_269193, baseEnd_269193] using wordTrace_append hprefix tailTrace_269193
  have hstable : (prefixWord ++ tailWord_269193).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_269193).length < 2 ^ (prefixWord ++ tailWord_269193).sum := by decide
  have hdescent : baseEnd_269193 < baseStart_269193 := by decide
  rcases family_descends (prefixWord ++ tailWord_269193) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_269207 : List Nat := [1, 1, 3, 3, 1, 2, 3, 3, 3]
def baseStart_269207 : Nat := 118140960795 + 269207 * 2 ^ 59
def prefixEnd_269207 : Nat := 4983230072969 + 3 ^ 40 * 269207 * 2
def baseEnd_269207 : Nat := 122873410271140853399507

theorem tailTrace_269207 : CollatzResearch.WordTrace tailWord_269207 prefixEnd_269207 122873410271140853399507 := by
  unfold tailWord_269207
  simp only [CollatzResearch.WordTrace]
  refine ⟨9818785935716490740301875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6545857290477660493534583 9818785935716490740301875)
  ·
    refine ⟨14728178903574736110452813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9818785935716490740301875 14728178903574736110452813)
    ·
      refine ⟨5523067088840526041419805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14728178903574736110452813 5523067088840526041419805)
      ·
        refine ⟨2071150158315197265532427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5523067088840526041419805 2071150158315197265532427)
        ·
          refine ⟨3106725237472795898298641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2071150158315197265532427 3106725237472795898298641)
          ·
            refine ⟨2330043928104596923723981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3106725237472795898298641 2330043928104596923723981)
            ·
              refine ⟨873766473039223846396493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2330043928104596923723981 873766473039223846396493)
              ·
                refine ⟨327662427389708942398685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 873766473039223846396493 327662427389708942398685)
                ·
                  refine ⟨122873410271140853399507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 327662427389708942398685 122873410271140853399507)
                  ·
                    rfl

theorem cell20_269207_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 3, 3, 3].length) (baseStart_269207 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_269207 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_269207 prefixEnd_269207 := by exact prefixLift 269207
  have htrace : WordTrace (prefixWord ++ tailWord_269207) baseStart_269207 baseEnd_269207 := by
    simpa [prefixWord, tailWord_269207, baseEnd_269207] using wordTrace_append hprefix tailTrace_269207
  have hstable : (prefixWord ++ tailWord_269207).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_269207).length < 2 ^ (prefixWord ++ tailWord_269207).sum := by decide
  have hdescent : baseEnd_269207 < baseStart_269207 := by decide
  rcases family_descends (prefixWord ++ tailWord_269207) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_269235 : List Nat := [1, 1, 1, 2, 3, 1, 2, 1, 8]
def baseStart_269235 : Nat := 118140960795 + 269235 * 2 ^ 59
def prefixEnd_269235 : Nat := 4983230072969 + 3 ^ 40 * 269235 * 2
def baseEnd_269235 : Nat := 122886190234097200466059

theorem tailTrace_269235 : CollatzResearch.WordTrace tailWord_269235 prefixEnd_269235 122886190234097200466059 := by
  unfold tailWord_269235
  simp only [CollatzResearch.WordTrace]
  refine ⟨9819807179615051522321159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6546538119743367681547439 9819807179615051522321159)
  ·
    refine ⟨14729710769422577283481739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9819807179615051522321159 14729710769422577283481739)
    ·
      refine ⟨22094566154133865925222609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14729710769422577283481739 22094566154133865925222609)
      ·
        refine ⟨16570924615600399443916957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22094566154133865925222609 16570924615600399443916957)
        ·
          refine ⟨6214096730850149791468859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16570924615600399443916957 6214096730850149791468859)
          ·
            refine ⟨9321145096275224687203289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6214096730850149791468859 9321145096275224687203289)
            ·
              refine ⟨6990858822206418515402467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9321145096275224687203289 6990858822206418515402467)
              ·
                refine ⟨10486288233309627773103701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6990858822206418515402467 10486288233309627773103701)
                ·
                  refine ⟨122886190234097200466059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 10486288233309627773103701 122886190234097200466059)
                  ·
                    rfl

theorem cell20_269235_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 2, 1, 8].length) (baseStart_269235 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_269235 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_269235 prefixEnd_269235 := by exact prefixLift 269235
  have htrace : WordTrace (prefixWord ++ tailWord_269235) baseStart_269235 baseEnd_269235 := by
    simpa [prefixWord, tailWord_269235, baseEnd_269235] using wordTrace_append hprefix tailTrace_269235
  have hstable : (prefixWord ++ tailWord_269235).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_269235).length < 2 ^ (prefixWord ++ tailWord_269235).sum := by decide
  have hdescent : baseEnd_269235 < baseStart_269235 := by decide
  rcases family_descends (prefixWord ++ tailWord_269235) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_269248 : List Nat := [2, 1, 1, 2, 3, 3, 4, 2, 2]
def baseStart_269248 : Nat := 118140960795 + 269248 * 2 ^ 59
def prefixEnd_269248 : Nat := 4983230072969 + 3 ^ 40 * 269248 * 2
def baseEnd_269248 : Nat := 122892123788326933032673

theorem tailTrace_269248 : CollatzResearch.WordTrace tailWord_269248 prefixEnd_269248 122892123788326933032673 := by
  unfold tailWord_269248
  simp only [CollatzResearch.WordTrace]
  refine ⟨4910140664283977371272199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6546854219045303161696265 4910140664283977371272199)
  ·
    refine ⟨7365210996425966056908299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4910140664283977371272199 7365210996425966056908299)
    ·
      refine ⟨11047816494638949085362449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7365210996425966056908299 11047816494638949085362449)
      ·
        refine ⟨8285862370979211814021837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11047816494638949085362449 8285862370979211814021837)
        ·
          refine ⟨3107198389117204430258189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8285862370979211814021837 3107198389117204430258189)
          ·
            refine ⟨1165199395918951661346821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3107198389117204430258189 1165199395918951661346821)
            ·
              refine ⟨218474886734803436502529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1165199395918951661346821 218474886734803436502529)
              ·
                refine ⟨163856165051102577376897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 218474886734803436502529 163856165051102577376897)
                ·
                  refine ⟨122892123788326933032673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 163856165051102577376897 122892123788326933032673)
                  ·
                    rfl

theorem cell20_269248_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 3, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 3, 4, 2, 2].length) (baseStart_269248 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_269248 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_269248 prefixEnd_269248 := by exact prefixLift 269248
  have htrace : WordTrace (prefixWord ++ tailWord_269248) baseStart_269248 baseEnd_269248 := by
    simpa [prefixWord, tailWord_269248, baseEnd_269248] using wordTrace_append hprefix tailTrace_269248
  have hstable : (prefixWord ++ tailWord_269248).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_269248).length < 2 ^ (prefixWord ++ tailWord_269248).sum := by decide
  have hdescent : baseEnd_269248 < baseStart_269248 := by decide
  rcases family_descends (prefixWord ++ tailWord_269248) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_269259 : List Nat := [1, 1, 1, 1, 3, 5, 3, 5]
def baseStart_269259 : Nat := 118140960795 + 269259 * 2 ^ 59
def prefixEnd_269259 : Nat := 4983230072969 + 3 ^ 40 * 269259 * 2
def baseEnd_269259 : Nat := 40965714829353261221987

theorem tailTrace_269259 : CollatzResearch.WordTrace tailWord_269259 prefixEnd_269259 40965714829353261221987 := by
  unfold tailWord_269259
  simp only [CollatzResearch.WordTrace]
  refine ⟨9820682531528103621194831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6547121687685402414129887 9820682531528103621194831)
  ·
    refine ⟨14731023797292155431792247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9820682531528103621194831 14731023797292155431792247)
    ·
      refine ⟨22096535695938233147688371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14731023797292155431792247 22096535695938233147688371)
      ·
        refine ⟨33144803543907349721532557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22096535695938233147688371 33144803543907349721532557)
        ·
          refine ⟨12429301328965256145574709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 33144803543907349721532557 12429301328965256145574709)
          ·
            refine ⟨1165246999590492763647629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 12429301328965256145574709 1165246999590492763647629)
            ·
              refine ⟨436967624846434786367861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1165246999590492763647629 436967624846434786367861)
              ·
                refine ⟨40965714829353261221987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 436967624846434786367861 40965714829353261221987)
                ·
                  rfl

theorem cell20_269259_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 5, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 5, 3, 5].length) (baseStart_269259 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_269259 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_269259 prefixEnd_269259 := by exact prefixLift 269259
  have htrace : WordTrace (prefixWord ++ tailWord_269259) baseStart_269259 baseEnd_269259 := by
    simpa [prefixWord, tailWord_269259, baseEnd_269259] using wordTrace_append hprefix tailTrace_269259
  have hstable : (prefixWord ++ tailWord_269259).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_269259).length < 2 ^ (prefixWord ++ tailWord_269259).sum := by decide
  have hdescent : baseEnd_269259 < baseStart_269259 := by decide
  rcases family_descends (prefixWord ++ tailWord_269259) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_269269 : List Nat := [1, 3, 2, 3, 3, 1, 1, 2, 4]
def baseStart_269269 : Nat := 118140960795 + 269269 * 2 ^ 59
def prefixEnd_269269 : Nat := 4983230072969 + 3 ^ 40 * 269269 * 2
def baseEnd_269269 : Nat := 122901708760544193332587

theorem tailTrace_269269 : CollatzResearch.WordTrace tailWord_269269 prefixEnd_269269 122901708760544193332587 := by
  unfold tailWord_269269
  simp only [CollatzResearch.WordTrace]
  refine ⟨9821047261491875329058861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6547364840994583552705907 9821047261491875329058861)
  ·
    refine ⟨3682892723059453248397073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9821047261491875329058861 3682892723059453248397073)
    ·
      refine ⟨2762169542294589936297805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3682892723059453248397073 2762169542294589936297805)
      ·
        refine ⟨1035813578360471226111677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2762169542294589936297805 1035813578360471226111677)
        ·
          refine ⟨388430091885176709791879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1035813578360471226111677 388430091885176709791879)
          ·
            refine ⟨582645137827765064687819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 388430091885176709791879 582645137827765064687819)
            ·
              refine ⟨873967706741647597031729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 582645137827765064687819 873967706741647597031729)
              ·
                refine ⟨655475780056235697773797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 873967706741647597031729 655475780056235697773797)
                ·
                  refine ⟨122901708760544193332587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 655475780056235697773797 122901708760544193332587)
                  ·
                    rfl

theorem cell20_269269_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 3, 1, 1, 2, 4].length) (baseStart_269269 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_269269 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_269269 prefixEnd_269269 := by exact prefixLift 269269
  have htrace : WordTrace (prefixWord ++ tailWord_269269) baseStart_269269 baseEnd_269269 := by
    simpa [prefixWord, tailWord_269269, baseEnd_269269] using wordTrace_append hprefix tailTrace_269269
  have hstable : (prefixWord ++ tailWord_269269).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_269269).length < 2 ^ (prefixWord ++ tailWord_269269).sum := by decide
  have hdescent : baseEnd_269269 < baseStart_269269 := by decide
  rcases family_descends (prefixWord ++ tailWord_269269) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_269297 : List Nat := [1, 2, 2, 2, 4, 2, 7]
def baseStart_269297 : Nat := 118140960795 + 269297 * 2 ^ 59
def prefixEnd_269297 : Nat := 4983230072969 + 3 ^ 40 * 269297 * 2
def baseEnd_269297 : Nat := 13657165413722282266571

theorem tailTrace_269297 : CollatzResearch.WordTrace tailWord_269297 prefixEnd_269297 13657165413722282266571 := by
  unfold tailWord_269297
  simp only [CollatzResearch.WordTrace]
  refine ⟨9822068505390436111078145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6548045670260290740718763 9822068505390436111078145)
  ·
    refine ⟨7366551379042827083308609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9822068505390436111078145 7366551379042827083308609)
    ·
      refine ⟨5524913534282120312481457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7366551379042827083308609 5524913534282120312481457)
      ·
        refine ⟨4143685150711590234361093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5524913534282120312481457 4143685150711590234361093)
        ·
          refine ⟨776940965758423168942705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4143685150711590234361093 776940965758423168942705)
          ·
            refine ⟨582705724318817376707029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 776940965758423168942705 582705724318817376707029)
            ·
              refine ⟨13657165413722282266571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 582705724318817376707029 13657165413722282266571)
              ·
                rfl

theorem cell20_269297_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 2, 7].length) (baseStart_269297 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_269297 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_269297 prefixEnd_269297 := by exact prefixLift 269297
  have htrace : WordTrace (prefixWord ++ tailWord_269297) baseStart_269297 baseEnd_269297 := by
    simpa [prefixWord, tailWord_269297, baseEnd_269297] using wordTrace_append hprefix tailTrace_269297
  have hstable : (prefixWord ++ tailWord_269297).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_269297).length < 2 ^ (prefixWord ++ tailWord_269297).sum := by decide
  have hdescent : baseEnd_269297 < baseStart_269297 := by decide
  rcases family_descends (prefixWord ++ tailWord_269297) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_269341 : List Nat := [1, 4, 2, 2, 3, 2, 1, 3, 2]
def baseStart_269341 : Nat := 118140960795 + 269341 * 2 ^ 59
def prefixEnd_269341 : Nat := 4983230072969 + 3 ^ 40 * 269341 * 2
def baseEnd_269341 : Nat := 122934571522431942932293

theorem tailTrace_269341 : CollatzResearch.WordTrace tailWord_269341 prefixEnd_269341 122934571522431942932293 := by
  unfold tailWord_269341
  simp only [CollatzResearch.WordTrace]
  refine ⟨9823673317231031625679877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6549115544820687750453251 9823673317231031625679877)
  ·
    refine ⟨1841938746980818429814977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 9823673317231031625679877 1841938746980818429814977)
    ·
      refine ⟨1381454060235613822361233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1841938746980818429814977 1381454060235613822361233)
      ·
        refine ⟨1036090545176710366770925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1381454060235613822361233 1036090545176710366770925)
        ·
          refine ⟨388533954441266387539097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1036090545176710366770925 388533954441266387539097)
          ·
            refine ⟨291400465830949790654323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 388533954441266387539097 291400465830949790654323)
            ·
              refine ⟨437100698746424685981485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 291400465830949790654323 437100698746424685981485)
              ·
                refine ⟨163912762029909257243057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 437100698746424685981485 163912762029909257243057)
                ·
                  refine ⟨122934571522431942932293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 163912762029909257243057 122934571522431942932293)
                  ·
                    rfl

theorem cell20_269341_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 3, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 3, 2, 1, 3, 2].length) (baseStart_269341 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_269341 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_269341 prefixEnd_269341 := by exact prefixLift 269341
  have htrace : WordTrace (prefixWord ++ tailWord_269341) baseStart_269341 baseEnd_269341 := by
    simpa [prefixWord, tailWord_269341, baseEnd_269341] using wordTrace_append hprefix tailTrace_269341
  have hstable : (prefixWord ++ tailWord_269341).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_269341).length < 2 ^ (prefixWord ++ tailWord_269341).sum := by decide
  have hdescent : baseEnd_269341 < baseStart_269341 := by decide
  rcases family_descends (prefixWord ++ tailWord_269341) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_269362 : List Nat := [3, 2, 1, 1, 2, 2, 5, 2, 2]
def baseStart_269362 : Nat := 118140960795 + 269362 * 2 ^ 59
def prefixEnd_269362 : Nat := 4983230072969 + 3 ^ 40 * 269362 * 2
def baseEnd_269362 : Nat := 122944156494649203232207

theorem tailTrace_269362 : CollatzResearch.WordTrace tailWord_269362 prefixEnd_269362 122944156494649203232207 := by
  unfold tailWord_269362
  simp only [CollatzResearch.WordTrace]
  refine ⟨2456109812538738053048585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6549626166769968141462893 2456109812538738053048585)
  ·
    refine ⟨1842082359404053539786439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2456109812538738053048585 1842082359404053539786439)
    ·
      refine ⟨2763123539106080309679659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1842082359404053539786439 2763123539106080309679659)
      ·
        refine ⟨4144685308659120464519489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2763123539106080309679659 4144685308659120464519489)
        ·
          refine ⟨3108513981494340348389617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4144685308659120464519489 3108513981494340348389617)
          ·
            refine ⟨2331385486120755261292213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3108513981494340348389617 2331385486120755261292213)
            ·
              refine ⟨218567389323820805746145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 2331385486120755261292213 218567389323820805746145)
              ·
                refine ⟨163925541992865604309609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 218567389323820805746145 163925541992865604309609)
                ·
                  refine ⟨122944156494649203232207, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 163925541992865604309609 122944156494649203232207)
                  ·
                    rfl

theorem cell20_269362_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 5, 2, 2].length) (baseStart_269362 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_269362 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_269362 prefixEnd_269362 := by exact prefixLift 269362
  have htrace : WordTrace (prefixWord ++ tailWord_269362) baseStart_269362 baseEnd_269362 := by
    simpa [prefixWord, tailWord_269362, baseEnd_269362] using wordTrace_append hprefix tailTrace_269362
  have hstable : (prefixWord ++ tailWord_269362).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_269362).length < 2 ^ (prefixWord ++ tailWord_269362).sum := by decide
  have hdescent : baseEnd_269362 < baseStart_269362 := by decide
  rcases family_descends (prefixWord ++ tailWord_269362) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_269373 : List Nat := [1, 4, 1, 3, 1, 2, 1, 7]
def baseStart_269373 : Nat := 118140960795 + 269373 * 2 ^ 59
def prefixEnd_269373 : Nat := 4983230072969 + 3 ^ 40 * 269373 * 2
def baseEnd_269373 : Nat := 40983059064794017955165

theorem tailTrace_269373 : CollatzResearch.WordTrace tailWord_269373 prefixEnd_269373 40983059064794017955165 := by
  unfold tailWord_269373
  simp only [CollatzResearch.WordTrace]
  refine ⟨9824840453115101090844773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6549893635410067393896515 9824840453115101090844773)
  ·
    refine ⟨1842157584959081454533395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 9824840453115101090844773 1842157584959081454533395)
    ·
      refine ⟨2763236377438622181800093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1842157584959081454533395 2763236377438622181800093)
      ·
        refine ⟨1036213641539483318175035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2763236377438622181800093 1036213641539483318175035)
        ·
          refine ⟨1554320462309224977262553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1036213641539483318175035 1554320462309224977262553)
          ·
            refine ⟨1165740346731918732946915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1554320462309224977262553 1165740346731918732946915)
            ·
              refine ⟨1748610520097878099420373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1165740346731918732946915 1748610520097878099420373)
              ·
                refine ⟨40983059064794017955165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1748610520097878099420373 40983059064794017955165)
                ·
                  rfl

theorem cell20_269373_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 2, 1, 7].length) (baseStart_269373 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_269373 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_269373 prefixEnd_269373 := by exact prefixLift 269373
  have htrace : WordTrace (prefixWord ++ tailWord_269373) baseStart_269373 baseEnd_269373 := by
    simpa [prefixWord, tailWord_269373, baseEnd_269373] using wordTrace_append hprefix tailTrace_269373
  have hstable : (prefixWord ++ tailWord_269373).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_269373).length < 2 ^ (prefixWord ++ tailWord_269373).sum := by decide
  have hdescent : baseEnd_269373 < baseStart_269373 := by decide
  rcases family_descends (prefixWord ++ tailWord_269373) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_269490 : List Nat := [3, 2, 1, 1, 1, 5, 3, 1, 3]
def baseStart_269490 : Nat := 118140960795 + 269490 * 2 ^ 59
def prefixEnd_269490 : Nat := 4983230072969 + 3 ^ 40 * 269490 * 2
def baseEnd_269490 : Nat := 123002579182449646965017

theorem tailTrace_269490 : CollatzResearch.WordTrace tailWord_269490 prefixEnd_269490 123002579182449646965017 := by
  unfold tailWord_269490
  simp only [CollatzResearch.WordTrace]
  refine ⟨2457276948422807518213481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6552738529127486715235949 2457276948422807518213481)
  ·
    refine ⟨1842957711317105638660111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2457276948422807518213481 1842957711317105638660111)
    ·
      refine ⟨2764436566975658457990167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1842957711317105638660111 2764436566975658457990167)
      ·
        refine ⟨4146654850463487686985251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2764436566975658457990167 4146654850463487686985251)
        ·
          refine ⟨6219982275695231530477877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4146654850463487686985251 6219982275695231530477877)
          ·
            refine ⟨583123338346427955982301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 6219982275695231530477877 583123338346427955982301)
            ·
              refine ⟨218671251879910483493363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 583123338346427955982301 218671251879910483493363)
              ·
                refine ⟨328006877819865725240045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 218671251879910483493363 328006877819865725240045)
                ·
                  refine ⟨123002579182449646965017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 328006877819865725240045 123002579182449646965017)
                  ·
                    rfl

theorem cell20_269490_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 5, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 5, 3, 1, 3].length) (baseStart_269490 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_269490 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_269490 prefixEnd_269490 := by exact prefixLift 269490
  have htrace : WordTrace (prefixWord ++ tailWord_269490) baseStart_269490 baseEnd_269490 := by
    simpa [prefixWord, tailWord_269490, baseEnd_269490] using wordTrace_append hprefix tailTrace_269490
  have hstable : (prefixWord ++ tailWord_269490).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_269490).length < 2 ^ (prefixWord ++ tailWord_269490).sum := by decide
  have hdescent : baseEnd_269490 < baseStart_269490 := by decide
  rcases family_descends (prefixWord ++ tailWord_269490) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_269514 : List Nat := [3, 1, 2, 1, 3, 4, 1, 3, 2]
def baseStart_269514 : Nat := 118140960795 + 269514 * 2 ^ 59
def prefixEnd_269514 : Nat := 4983230072969 + 3 ^ 40 * 269514 * 2
def baseEnd_269514 : Nat := 123013533436412230164919

theorem tailTrace_269514 : CollatzResearch.WordTrace tailWord_269514 prefixEnd_269514 123013533436412230164919 := by
  unfold tailWord_269514
  simp only [CollatzResearch.WordTrace]
  refine ⟨2457495786401070542931899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6553322097069521447818397 2457495786401070542931899)
  ·
    refine ⟨3686243679601605814397849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2457495786401070542931899 3686243679601605814397849)
    ·
      refine ⟨2764682759701204360798387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3686243679601605814397849 2764682759701204360798387)
      ·
        refine ⟨4147024139551806541197581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2764682759701204360798387 4147024139551806541197581)
        ·
          refine ⟨1555134052331927452949093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4147024139551806541197581 1555134052331927452949093)
          ·
            refine ⟨291587634812236397427955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1555134052331927452949093 291587634812236397427955)
            ·
              refine ⟨437381452218354596141933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 291587634812236397427955 437381452218354596141933)
              ·
                refine ⟨164018044581882973553225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 437381452218354596141933 164018044581882973553225)
                ·
                  refine ⟨123013533436412230164919, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 164018044581882973553225 123013533436412230164919)
                  ·
                    rfl

theorem cell20_269514_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 4, 1, 3, 2].length) (baseStart_269514 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_269514 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_269514 prefixEnd_269514 := by exact prefixLift 269514
  have htrace : WordTrace (prefixWord ++ tailWord_269514) baseStart_269514 baseEnd_269514 := by
    simpa [prefixWord, tailWord_269514, baseEnd_269514] using wordTrace_append hprefix tailTrace_269514
  have hstable : (prefixWord ++ tailWord_269514).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_269514).length < 2 ^ (prefixWord ++ tailWord_269514).sum := by decide
  have hdescent : baseEnd_269514 < baseStart_269514 := by decide
  rcases family_descends (prefixWord ++ tailWord_269514) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_269525 : List Nat := [1, 3, 2, 4, 1, 1, 8]
def baseStart_269525 : Nat := 118140960795 + 269525 * 2 ^ 59
def prefixEnd_269525 : Nat := 4983230072969 + 3 ^ 40 * 269525 * 2
def baseEnd_269525 : Nat := 13668728237349453422023

theorem tailTrace_269525 : CollatzResearch.WordTrace tailWord_269525 prefixEnd_269525 13668728237349453422023 := by
  unfold tailWord_269525
  simp only [CollatzResearch.WordTrace]
  refine ⟨9830384348564431050378029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6553589565709620700252019 9830384348564431050378029)
  ·
    refine ⟨3686394130711661643891761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9830384348564431050378029 3686394130711661643891761)
    ·
      refine ⟨2764795598033746232918821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3686394130711661643891761 2764795598033746232918821)
      ·
        refine ⟨518399174631327418672279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2764795598033746232918821 518399174631327418672279)
        ·
          refine ⟨777598761946991128008419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 518399174631327418672279 777598761946991128008419)
          ·
            refine ⟨1166398142920486692012629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 777598761946991128008419 1166398142920486692012629)
            ·
              refine ⟨13668728237349453422023, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 1166398142920486692012629 13668728237349453422023)
              ·
                rfl

theorem cell20_269525_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 1, 8].length) (baseStart_269525 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_269525 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_269525 prefixEnd_269525 := by exact prefixLift 269525
  have htrace : WordTrace (prefixWord ++ tailWord_269525) baseStart_269525 baseEnd_269525 := by
    simpa [prefixWord, tailWord_269525, baseEnd_269525] using wordTrace_append hprefix tailTrace_269525
  have hstable : (prefixWord ++ tailWord_269525).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_269525).length < 2 ^ (prefixWord ++ tailWord_269525).sum := by decide
  have hdescent : baseEnd_269525 < baseStart_269525 := by decide
  rcases family_descends (prefixWord ++ tailWord_269525) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_269618 : List Nat := [3, 2, 1, 1, 4, 2, 3, 4]
def baseStart_269618 : Nat := 118140960795 + 269618 * 2 ^ 59
def prefixEnd_269618 : Nat := 4983230072969 + 3 ^ 40 * 269618 * 2
def baseEnd_269618 : Nat := 41020333956750030232609

theorem tailTrace_269618 : CollatzResearch.WordTrace tailWord_269618 prefixEnd_269618 41020333956750030232609 := by
  unfold tailWord_269618
  simp only [CollatzResearch.WordTrace]
  refine ⟨2458444084306876983378377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6555850891485005289009005 2458444084306876983378377)
  ·
    refine ⟨1843833063230157737533783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2458444084306876983378377 1843833063230157737533783)
    ·
      refine ⟨2765749594845236606300675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1843833063230157737533783 2765749594845236606300675)
      ·
        refine ⟨4148624392267854909451013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2765749594845236606300675 4148624392267854909451013)
        ·
          refine ⟨777867073550222795522065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4148624392267854909451013 777867073550222795522065)
          ·
            refine ⟨583400305162667096641549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 777867073550222795522065 583400305162667096641549)
            ·
              refine ⟨218775114436000161240581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 583400305162667096641549 218775114436000161240581)
              ·
                refine ⟨41020333956750030232609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 218775114436000161240581 41020333956750030232609)
                ·
                  rfl

theorem cell20_269618_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 2, 3, 4].length) (baseStart_269618 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_269618 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_269618 prefixEnd_269618 := by exact prefixLift 269618
  have htrace : WordTrace (prefixWord ++ tailWord_269618) baseStart_269618 baseEnd_269618 := by
    simpa [prefixWord, tailWord_269618, baseEnd_269618] using wordTrace_append hprefix tailTrace_269618
  have hstable : (prefixWord ++ tailWord_269618).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_269618).length < 2 ^ (prefixWord ++ tailWord_269618).sum := by decide
  have hdescent : baseEnd_269618 < baseStart_269618 := by decide
  rcases family_descends (prefixWord ++ tailWord_269618) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_269646 : List Nat := [4, 1, 1, 1, 1, 1, 5, 1, 5]
def baseStart_269646 : Nat := 118140960795 + 269646 * 2 ^ 59
def prefixEnd_269646 : Nat := 4983230072969 + 3 ^ 40 * 269646 * 2
def baseEnd_269646 : Nat := 123073781833206437764379

theorem tailTrace_269646 : CollatzResearch.WordTrace tailWord_269646 prefixEnd_269646 123073781833206437764379 := by
  unfold tailWord_269646
  simp only [CollatzResearch.WordTrace]
  refine ⟨1229349697640758589441599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 6556531720750712477021861 1229349697640758589441599)
  ·
    refine ⟨1844024546461137884162399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1229349697640758589441599 1844024546461137884162399)
    ·
      refine ⟨2766036819691706826243599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1844024546461137884162399 2766036819691706826243599)
      ·
        refine ⟨4149055229537560239365399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2766036819691706826243599 4149055229537560239365399)
        ·
          refine ⟨6223582844306340359048099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4149055229537560239365399 6223582844306340359048099)
          ·
            refine ⟨9335374266459510538572149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6223582844306340359048099 9335374266459510538572149)
            ·
              refine ⟨875191337480579112991139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 9335374266459510538572149 875191337480579112991139)
              ·
                refine ⟨1312787006220868669486709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 875191337480579112991139 1312787006220868669486709)
                ·
                  refine ⟨123073781833206437764379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1312787006220868669486709 123073781833206437764379)
                  ·
                    rfl

theorem cell20_269646_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 5, 1, 5].length) (baseStart_269646 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_269646 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_269646 prefixEnd_269646 := by exact prefixLift 269646
  have htrace : WordTrace (prefixWord ++ tailWord_269646) baseStart_269646 baseEnd_269646 := by
    simpa [prefixWord, tailWord_269646, baseEnd_269646] using wordTrace_append hprefix tailTrace_269646
  have hstable : (prefixWord ++ tailWord_269646).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_269646).length < 2 ^ (prefixWord ++ tailWord_269646).sum := by decide
  have hdescent : baseEnd_269646 < baseStart_269646 := by decide
  rcases family_descends (prefixWord ++ tailWord_269646) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_269677 : List Nat := [1, 5, 1, 1, 1, 4, 1, 6]
def baseStart_269677 : Nat := 118140960795 + 269677 * 2 ^ 59
def prefixEnd_269677 : Nat := 4983230072969 + 3 ^ 40 * 269677 * 2
def baseEnd_269677 : Nat := 41029310359302702576973

theorem tailTrace_269677 : CollatzResearch.WordTrace tailWord_269677 prefixEnd_269677 41029310359302702576973 := by
  unfold tailWord_269677
  simp only [CollatzResearch.WordTrace]
  refine ⟨9835928244013761009911285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6557285496009174006607523 9835928244013761009911285)
  ·
    refine ⟨922118272876290094679183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 9835928244013761009911285 922118272876290094679183)
    ·
      refine ⟨1383177409314435142018775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 922118272876290094679183 1383177409314435142018775)
      ·
        refine ⟨2074766113971652713028163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1383177409314435142018775 2074766113971652713028163)
        ·
          refine ⟨3112149170957479069542245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2074766113971652713028163 3112149170957479069542245)
          ·
            refine ⟨583527969554527325539171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3112149170957479069542245 583527969554527325539171)
            ·
              refine ⟨875291954331790988308757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 583527969554527325539171 875291954331790988308757)
              ·
                refine ⟨41029310359302702576973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 875291954331790988308757 41029310359302702576973)
                ·
                  rfl

theorem cell20_269677_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 4, 1, 6].length) (baseStart_269677 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_269677 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_269677 prefixEnd_269677 := by exact prefixLift 269677
  have htrace : WordTrace (prefixWord ++ tailWord_269677) baseStart_269677 baseEnd_269677 := by
    simpa [prefixWord, tailWord_269677, baseEnd_269677] using wordTrace_append hprefix tailTrace_269677
  have hstable : (prefixWord ++ tailWord_269677).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_269677).length < 2 ^ (prefixWord ++ tailWord_269677).sum := by decide
  have hdescent : baseEnd_269677 < baseStart_269677 := by decide
  rcases family_descends (prefixWord ++ tailWord_269677) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_269704 : List Nat := [2, 1, 3, 3, 1, 3, 3, 2, 2]
def baseStart_269704 : Nat := 118140960795 + 269704 * 2 ^ 59
def prefixEnd_269704 : Nat := 4983230072969 + 3 ^ 40 * 269704 * 2
def baseEnd_269704 : Nat := 123100254613616013830809

theorem tailTrace_269704 : CollatzResearch.WordTrace tailWord_269704 prefixEnd_269704 123100254613616013830809 := by
  unfold tailWord_269704
  simp only [CollatzResearch.WordTrace]
  refine ⟨4918456507457972310572083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6557942009943963080762777 4918456507457972310572083)
  ·
    refine ⟨7377684761186958465858125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4918456507457972310572083 7377684761186958465858125)
    ·
      refine ⟨2766631785445109424696797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7377684761186958465858125 2766631785445109424696797)
      ·
        refine ⟨1037486919541916034261299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2766631785445109424696797 1037486919541916034261299)
        ·
          refine ⟨1556230379312874051391949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1037486919541916034261299 1556230379312874051391949)
          ·
            refine ⟨583586392242327769271981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1556230379312874051391949 583586392242327769271981)
            ·
              refine ⟨218844897090872913476993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 583586392242327769271981 218844897090872913476993)
              ·
                refine ⟨164133672818154685107745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 218844897090872913476993 164133672818154685107745)
                ·
                  refine ⟨123100254613616013830809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 164133672818154685107745 123100254613616013830809)
                  ·
                    rfl

theorem cell20_269704_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 3, 3, 2, 2].length) (baseStart_269704 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_269704 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_269704 prefixEnd_269704 := by exact prefixLift 269704
  have htrace : WordTrace (prefixWord ++ tailWord_269704) baseStart_269704 baseEnd_269704 := by
    simpa [prefixWord, tailWord_269704, baseEnd_269704] using wordTrace_append hprefix tailTrace_269704
  have hstable : (prefixWord ++ tailWord_269704).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_269704).length < 2 ^ (prefixWord ++ tailWord_269704).sum := by decide
  have hdescent : baseEnd_269704 < baseStart_269704 := by decide
  rcases family_descends (prefixWord ++ tailWord_269704) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_269714 : List Nat := [3, 2, 3, 3, 1, 2, 2, 1, 3]
def baseStart_269714 : Nat := 118140960795 + 269714 * 2 ^ 59
def prefixEnd_269714 : Nat := 4983230072969 + 3 ^ 40 * 269714 * 2
def baseEnd_269714 : Nat := 123104818886100423497435

theorem tailTrace_269714 : CollatzResearch.WordTrace tailWord_269714 prefixEnd_269714 123104818886100423497435 := by
  unfold tailWord_269714
  simp only [CollatzResearch.WordTrace]
  refine ⟨2459319436219929082252049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6558185163253144219338797 2459319436219929082252049)
  ·
    refine ⟨1844489577164946811689037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2459319436219929082252049 1844489577164946811689037)
    ·
      refine ⟨691683591436855054383389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1844489577164946811689037 691683591436855054383389)
      ·
        refine ⟨259381346788820645393771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 691683591436855054383389 259381346788820645393771)
        ·
          refine ⟨389072020183230968090657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 259381346788820645393771 389072020183230968090657)
          ·
            refine ⟨291804015137423226067993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 389072020183230968090657 291804015137423226067993)
            ·
              refine ⟨218853011353067419550995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 291804015137423226067993 218853011353067419550995)
              ·
                refine ⟨328279517029601129326493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 218853011353067419550995 328279517029601129326493)
                ·
                  refine ⟨123104818886100423497435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 328279517029601129326493 123104818886100423497435)
                  ·
                    rfl

theorem cell20_269714_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 3, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 3, 1, 2, 2, 1, 3].length) (baseStart_269714 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_269714 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_269714 prefixEnd_269714 := by exact prefixLift 269714
  have htrace : WordTrace (prefixWord ++ tailWord_269714) baseStart_269714 baseEnd_269714 := by
    simpa [prefixWord, tailWord_269714, baseEnd_269714] using wordTrace_append hprefix tailTrace_269714
  have hstable : (prefixWord ++ tailWord_269714).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_269714).length < 2 ^ (prefixWord ++ tailWord_269714).sum := by decide
  have hdescent : baseEnd_269714 < baseStart_269714 := by decide
  rcases family_descends (prefixWord ++ tailWord_269714) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_269743 : List Nat := [1, 1, 2, 1, 2, 2, 1, 3, 7]
def baseStart_269743 : Nat := 118140960795 + 269743 * 2 ^ 59
def prefixEnd_269743 : Nat := 4983230072969 + 3 ^ 40 * 269743 * 2
def baseEnd_269743 : Nat := 123118055276305211530649

theorem tailTrace_269743 : CollatzResearch.WordTrace tailWord_269743 prefixEnd_269743 123118055276305211530649 := by
  unfold tailWord_269743
  simp only [CollatzResearch.WordTrace]
  refine ⟨9838335461774654281813883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6558890307849769521209255 9838335461774654281813883)
  ·
    refine ⟨14757503192661981422720825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9838335461774654281813883 14757503192661981422720825)
    ·
      refine ⟨11068127394496486067040619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14757503192661981422720825 11068127394496486067040619)
      ·
        refine ⟨16602191091744729100560929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11068127394496486067040619 16602191091744729100560929)
        ·
          refine ⟨12451643318808546825420697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16602191091744729100560929 12451643318808546825420697)
          ·
            refine ⟨9338732489106410119065523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12451643318808546825420697 9338732489106410119065523)
            ·
              refine ⟨14008098733659615178598285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9338732489106410119065523 14008098733659615178598285)
              ·
                refine ⟨5253037025122355691974357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14008098733659615178598285 5253037025122355691974357)
                ·
                  refine ⟨123118055276305211530649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 5253037025122355691974357 123118055276305211530649)
                  ·
                    rfl

theorem cell20_269743_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 1, 3, 7].length) (baseStart_269743 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_269743 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_269743 prefixEnd_269743 := by exact prefixLift 269743
  have htrace : WordTrace (prefixWord ++ tailWord_269743) baseStart_269743 baseEnd_269743 := by
    simpa [prefixWord, tailWord_269743, baseEnd_269743] using wordTrace_append hprefix tailTrace_269743
  have hstable : (prefixWord ++ tailWord_269743).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_269743).length < 2 ^ (prefixWord ++ tailWord_269743).sum := by decide
  have hdescent : baseEnd_269743 < baseStart_269743 := by decide
  rcases family_descends (prefixWord ++ tailWord_269743) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_269753 : List Nat := [1, 2, 1, 4, 5, 7]
def baseStart_269753 : Nat := 118140960795 + 269753 * 2 ^ 59
def prefixEnd_269753 : Nat := 4983230072969 + 3 ^ 40 * 269753 * 2
def baseEnd_269753 : Nat := 4560097020325541525825

theorem tailTrace_269753 : CollatzResearch.WordTrace tailWord_269753 prefixEnd_269753 4560097020325541525825 := by
  unfold tailWord_269753
  simp only [CollatzResearch.WordTrace]
  refine ⟨9838700191738425989677913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6559133461158950659785275 9838700191738425989677913)
  ·
    refine ⟨7379025143803819492258435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9838700191738425989677913 7379025143803819492258435)
    ·
      refine ⟨11068537715705729238387653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7379025143803819492258435 11068537715705729238387653)
      ·
        refine ⟨2075350821694824232197685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 11068537715705729238387653 2075350821694824232197685)
        ·
          refine ⟨194564139533889771768533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 2075350821694824232197685 194564139533889771768533)
          ·
            refine ⟨4560097020325541525825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 194564139533889771768533 4560097020325541525825)
            ·
              rfl

theorem cell20_269753_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 5, 7].length) (baseStart_269753 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_269753 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_269753 prefixEnd_269753 := by exact prefixLift 269753
  have htrace : WordTrace (prefixWord ++ tailWord_269753) baseStart_269753 baseEnd_269753 := by
    simpa [prefixWord, tailWord_269753, baseEnd_269753] using wordTrace_append hprefix tailTrace_269753
  have hstable : (prefixWord ++ tailWord_269753).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_269753).length < 2 ^ (prefixWord ++ tailWord_269753).sum := by decide
  have hdescent : baseEnd_269753 < baseStart_269753 := by decide
  rcases family_descends (prefixWord ++ tailWord_269753) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_269756 : List Nat := [2, 2, 2, 4, 2, 1, 2, 2, 3]
def baseStart_269756 : Nat := 118140960795 + 269756 * 2 ^ 59
def prefixEnd_269756 : Nat := 4983230072969 + 3 ^ 40 * 269756 * 2
def baseEnd_269756 : Nat := 123123988830534944097263

theorem tailTrace_269756 : CollatzResearch.WordTrace tailWord_269756 prefixEnd_269756 123123988830534944097263 := by
  unfold tailWord_269756
  simp only [CollatzResearch.WordTrace]
  refine ⟨4919404805363778751018561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6559206407151705001358081 4919404805363778751018561)
  ·
    refine ⟨3689553604022834063263921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4919404805363778751018561 3689553604022834063263921)
    ·
      refine ⟨2767165203017125547447941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3689553604022834063263921 2767165203017125547447941)
      ·
        refine ⟨518843475565711040146489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2767165203017125547447941 518843475565711040146489)
        ·
          refine ⟨389132606674283280109867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 518843475565711040146489 389132606674283280109867)
          ·
            refine ⟨583698910011424920164801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 389132606674283280109867 583698910011424920164801)
            ·
              refine ⟨437774182508568690123601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 583698910011424920164801 437774182508568690123601)
              ·
                refine ⟨328330636881426517592701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 437774182508568690123601 328330636881426517592701)
                ·
                  refine ⟨123123988830534944097263, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 328330636881426517592701 123123988830534944097263)
                  ·
                    rfl

theorem cell20_269756_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 2, 1, 2, 2, 3].length) (baseStart_269756 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_269756 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_269756 prefixEnd_269756 := by exact prefixLift 269756
  have htrace : WordTrace (prefixWord ++ tailWord_269756) baseStart_269756 baseEnd_269756 := by
    simpa [prefixWord, tailWord_269756, baseEnd_269756] using wordTrace_append hprefix tailTrace_269756
  have hstable : (prefixWord ++ tailWord_269756).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_269756).length < 2 ^ (prefixWord ++ tailWord_269756).sum := by decide
  have hdescent : baseEnd_269756 < baseStart_269756 := by decide
  rcases family_descends (prefixWord ++ tailWord_269756) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_269760 : List Nat := [2, 1, 1, 2, 3, 1, 3, 4, 3]
def baseStart_269760 : Nat := 118140960795 + 269760 * 2 ^ 59
def prefixEnd_269760 : Nat := 4983230072969 + 3 ^ 40 * 269760 * 2
def baseEnd_269760 : Nat := 123125814539528707963913

theorem tailTrace_269760 : CollatzResearch.WordTrace tailWord_269760 prefixEnd_269760 123125814539528707963913 := by
  unfold tailWord_269760
  simp only [CollatzResearch.WordTrace]
  refine ⟨4919477751356533092591367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6559303668475377456788489 4919477751356533092591367)
  ·
    refine ⟨7379216627034799638887051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4919477751356533092591367 7379216627034799638887051)
    ·
      refine ⟨11068824940552199458330577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7379216627034799638887051 11068824940552199458330577)
      ·
        refine ⟨8301618705414149593747933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11068824940552199458330577 8301618705414149593747933)
        ·
          refine ⟨3113107014530306097655475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8301618705414149593747933 3113107014530306097655475)
          ·
            refine ⟨4669660521795459146483213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3113107014530306097655475 4669660521795459146483213)
            ·
              refine ⟨1751122695673297179931205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4669660521795459146483213 1751122695673297179931205)
              ·
                refine ⟨328335505438743221237101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1751122695673297179931205 328335505438743221237101)
                ·
                  refine ⟨123125814539528707963913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 328335505438743221237101 123125814539528707963913)
                  ·
                    rfl

theorem cell20_269760_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 3, 4, 3].length) (baseStart_269760 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_269760 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_269760 prefixEnd_269760 := by exact prefixLift 269760
  have htrace : WordTrace (prefixWord ++ tailWord_269760) baseStart_269760 baseEnd_269760 := by
    simpa [prefixWord, tailWord_269760, baseEnd_269760] using wordTrace_append hprefix tailTrace_269760
  have hstable : (prefixWord ++ tailWord_269760).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_269760).length < 2 ^ (prefixWord ++ tailWord_269760).sum := by decide
  have hdescent : baseEnd_269760 < baseStart_269760 := by decide
  rcases family_descends (prefixWord ++ tailWord_269760) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_269762 : List Nat := [3, 5, 2, 1, 2, 1, 1, 5]
def baseStart_269762 : Nat := 118140960795 + 269762 * 2 ^ 59
def prefixEnd_269762 : Nat := 4983230072969 + 3 ^ 40 * 269762 * 2
def baseEnd_269762 : Nat := 41042242464675196632413

theorem tailTrace_269762 : CollatzResearch.WordTrace tailWord_269762 prefixEnd_269762 41042242464675196632413 := by
  unfold tailWord_269762
  simp only [CollatzResearch.WordTrace]
  refine ⟨2459757112176455131688885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6559352299137213684503693 2459757112176455131688885)
  ·
    refine ⟨230602229266542668595833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 2459757112176455131688885 230602229266542668595833)
    ·
      refine ⟨172951671949907001446875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 230602229266542668595833 172951671949907001446875)
      ·
        refine ⟨259427507924860502170313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 172951671949907001446875 259427507924860502170313)
        ·
          refine ⟨194570630943645376627735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 259427507924860502170313 194570630943645376627735)
          ·
            refine ⟨291855946415468064941603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 194570630943645376627735 291855946415468064941603)
            ·
              refine ⟨437783919623202097412405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 291855946415468064941603 437783919623202097412405)
              ·
                refine ⟨41042242464675196632413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 437783919623202097412405 41042242464675196632413)
                ·
                  rfl

theorem cell20_269762_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 2, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 2, 1, 2, 1, 1, 5].length) (baseStart_269762 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_269762 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_269762 prefixEnd_269762 := by exact prefixLift 269762
  have htrace : WordTrace (prefixWord ++ tailWord_269762) baseStart_269762 baseEnd_269762 := by
    simpa [prefixWord, tailWord_269762, baseEnd_269762] using wordTrace_append hprefix tailTrace_269762
  have hstable : (prefixWord ++ tailWord_269762).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_269762).length < 2 ^ (prefixWord ++ tailWord_269762).sum := by decide
  have hdescent : baseEnd_269762 < baseStart_269762 := by decide
  rcases family_descends (prefixWord ++ tailWord_269762) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_269763 : List Nat := [1, 1, 1, 3, 1, 1, 8, 2, 2]
def baseStart_269763 : Nat := 118140960795 + 269763 * 2 ^ 59
def prefixEnd_269763 : Nat := 4983230072969 + 3 ^ 40 * 269763 * 2
def baseEnd_269763 : Nat := 123127183821274030863901

theorem tailTrace_269763 : CollatzResearch.WordTrace tailWord_269763 prefixEnd_269763 123127183821274030863901 := by
  unfold tailWord_269763
  simp only [CollatzResearch.WordTrace]
  refine ⟨9839064921702197697541943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6559376614468131798361295 9839064921702197697541943)
  ·
    refine ⟨14758597382553296546312915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9839064921702197697541943 14758597382553296546312915)
    ·
      refine ⟨22137896073829944819469373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14758597382553296546312915 22137896073829944819469373)
      ·
        refine ⟨8301711027686229307301015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 22137896073829944819469373 8301711027686229307301015)
        ·
          refine ⟨12452566541529343960951523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8301711027686229307301015 12452566541529343960951523)
          ·
            refine ⟨18678849812294015941427285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12452566541529343960951523 18678849812294015941427285)
            ·
              refine ⟨218892771237820499313601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 18678849812294015941427285 218892771237820499313601)
              ·
                refine ⟨164169578428365374485201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 218892771237820499313601 164169578428365374485201)
                ·
                  refine ⟨123127183821274030863901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 164169578428365374485201 123127183821274030863901)
                  ·
                    rfl

theorem cell20_269763_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 8, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 8, 2, 2].length) (baseStart_269763 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_269763 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_269763 prefixEnd_269763 := by exact prefixLift 269763
  have htrace : WordTrace (prefixWord ++ tailWord_269763) baseStart_269763 baseEnd_269763 := by
    simpa [prefixWord, tailWord_269763, baseEnd_269763] using wordTrace_append hprefix tailTrace_269763
  have hstable : (prefixWord ++ tailWord_269763).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_269763).length < 2 ^ (prefixWord ++ tailWord_269763).sum := by decide
  have hdescent : baseEnd_269763 < baseStart_269763 := by decide
  rcases family_descends (prefixWord ++ tailWord_269763) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_269767 : List Nat := [1, 1, 4, 1, 1, 3, 2, 3, 4]
def baseStart_269767 : Nat := 118140960795 + 269767 * 2 ^ 59
def prefixEnd_269767 : Nat := 4983230072969 + 3 ^ 40 * 269767 * 2
def baseEnd_269767 : Nat := 123129009530267794730551

theorem tailTrace_269767 : CollatzResearch.WordTrace tailWord_269767 prefixEnd_269767 123129009530267794730551 := by
  unfold tailWord_269767
  simp only [CollatzResearch.WordTrace]
  refine ⟨9839210813687706380687555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6559473875791804253791703 9839210813687706380687555)
  ·
    refine ⟨14758816220531559571031333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9839210813687706380687555 14758816220531559571031333)
    ·
      refine ⟨2767278041349667419568375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 14758816220531559571031333 2767278041349667419568375)
      ·
        refine ⟨4150917062024501129352563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2767278041349667419568375 4150917062024501129352563)
        ·
          refine ⟨6226375593036751694028845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4150917062024501129352563 6226375593036751694028845)
          ·
            refine ⟨2334890847388781885260817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6226375593036751694028845 2334890847388781885260817)
            ·
              refine ⟨1751168135541586413945613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2334890847388781885260817 1751168135541586413945613)
              ·
                refine ⟨656688050828094905229605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1751168135541586413945613 656688050828094905229605)
                ·
                  refine ⟨123129009530267794730551, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 656688050828094905229605 123129009530267794730551)
                  ·
                    rfl

theorem cell20_269767_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 2, 3, 4].length) (baseStart_269767 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_269767 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_269767 prefixEnd_269767 := by exact prefixLift 269767
  have htrace : WordTrace (prefixWord ++ tailWord_269767) baseStart_269767 baseEnd_269767 := by
    simpa [prefixWord, tailWord_269767, baseEnd_269767] using wordTrace_append hprefix tailTrace_269767
  have hstable : (prefixWord ++ tailWord_269767).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_269767).length < 2 ^ (prefixWord ++ tailWord_269767).sum := by decide
  have hdescent : baseEnd_269767 < baseStart_269767 := by decide
  rcases family_descends (prefixWord ++ tailWord_269767) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_269791 : List Nat := [1, 1, 2, 3, 3, 1, 5, 4]
def baseStart_269791 : Nat := 118140960795 + 269791 * 2 ^ 59
def prefixEnd_269791 : Nat := 4983230072969 + 3 ^ 40 * 269791 * 2
def baseEnd_269791 : Nat := 41046654594743459310151

theorem tailTrace_269791 : CollatzResearch.WordTrace tailWord_269791 prefixEnd_269791 41046654594743459310151 := by
  unfold tailWord_269791
  simp only [CollatzResearch.WordTrace]
  refine ⟨9840086165600758479561227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6560057443733838986374151 9840086165600758479561227)
  ·
    refine ⟨14760129248401137719341841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9840086165600758479561227 14760129248401137719341841)
    ·
      refine ⟨11070096936300853289506381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14760129248401137719341841 11070096936300853289506381)
      ·
        refine ⟨4151286351112819983564893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11070096936300853289506381 4151286351112819983564893)
        ·
          refine ⟨1556732381667307493836835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4151286351112819983564893 1556732381667307493836835)
          ·
            refine ⟨2335098572500961240755253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1556732381667307493836835 2335098572500961240755253)
            ·
              refine ⟨218915491171965116320805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 2335098572500961240755253 218915491171965116320805)
              ·
                refine ⟨41046654594743459310151, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 218915491171965116320805 41046654594743459310151)
                ·
                  rfl

theorem cell20_269791_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 5, 4].length) (baseStart_269791 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_269791 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_269791 prefixEnd_269791 := by exact prefixLift 269791
  have htrace : WordTrace (prefixWord ++ tailWord_269791) baseStart_269791 baseEnd_269791 := by
    simpa [prefixWord, tailWord_269791, baseEnd_269791] using wordTrace_append hprefix tailTrace_269791
  have hstable : (prefixWord ++ tailWord_269791).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_269791).length < 2 ^ (prefixWord ++ tailWord_269791).sum := by decide
  have hdescent : baseEnd_269791 < baseStart_269791 := by decide
  rcases family_descends (prefixWord ++ tailWord_269791) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_269819 : List Nat := [1, 1, 1, 1, 1, 3, 2, 5, 5]
def baseStart_269819 : Nat := 118140960795 + 269819 * 2 ^ 59
def prefixEnd_269819 : Nat := 4983230072969 + 3 ^ 40 * 269819 * 2
def baseEnd_269819 : Nat := 123152743747186724997005

theorem tailTrace_269819 : CollatzResearch.WordTrace tailWord_269819 prefixEnd_269819 123152743747186724997005 := by
  unfold tailWord_269819
  simp only [CollatzResearch.WordTrace]
  refine ⟨9841107409499319261580511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6560738272999546174387007 9841107409499319261580511)
  ·
    refine ⟨14761661114248978892370767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9841107409499319261580511 14761661114248978892370767)
    ·
      refine ⟨22142491671373468338556151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14761661114248978892370767 22142491671373468338556151)
      ·
        refine ⟨33213737507060202507834227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22142491671373468338556151 33213737507060202507834227)
        ·
          refine ⟨49820606260590303761751341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33213737507060202507834227 49820606260590303761751341)
          ·
            refine ⟨18682727347721363910656753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 49820606260590303761751341 18682727347721363910656753)
            ·
              refine ⟨14012045510791022932992565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18682727347721363910656753 14012045510791022932992565)
              ·
                refine ⟨1313629266636658399968053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 14012045510791022932992565 1313629266636658399968053)
                ·
                  refine ⟨123152743747186724997005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1313629266636658399968053 123152743747186724997005)
                  ·
                    rfl

theorem cell20_269819_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 2, 5, 5].length) (baseStart_269819 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_269819 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_269819 prefixEnd_269819 := by exact prefixLift 269819
  have htrace : WordTrace (prefixWord ++ tailWord_269819) baseStart_269819 baseEnd_269819 := by
    simpa [prefixWord, tailWord_269819, baseEnd_269819] using wordTrace_append hprefix tailTrace_269819
  have hstable : (prefixWord ++ tailWord_269819).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_269819).length < 2 ^ (prefixWord ++ tailWord_269819).sum := by decide
  have hdescent : baseEnd_269819 < baseStart_269819 := by decide
  rcases family_descends (prefixWord ++ tailWord_269819) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_269843 : List Nat := [1, 1, 1, 2, 1, 6, 2, 2, 4]
def baseStart_269843 : Nat := 118140960795 + 269843 * 2 ^ 59
def prefixEnd_269843 : Nat := 4983230072969 + 3 ^ 40 * 269843 * 2
def baseEnd_269843 : Nat := 123163698001149308196907

theorem tailTrace_269843 : CollatzResearch.WordTrace tailWord_269843 prefixEnd_269843 123163698001149308196907 := by
  unfold tailWord_269843
  simp only [CollatzResearch.WordTrace]
  refine ⟨9841982761412371360454183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6561321840941580906969455 9841982761412371360454183)
  ·
    refine ⟨14762974142118557040681275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9841982761412371360454183 14762974142118557040681275)
    ·
      refine ⟨22144461213177835561021913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14762974142118557040681275 22144461213177835561021913)
      ·
        refine ⟨16608345909883376670766435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22144461213177835561021913 16608345909883376670766435)
        ·
          refine ⟨24912518864825065006149653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16608345909883376670766435 24912518864825065006149653)
          ·
            refine ⟨1167774321788674922163265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 24912518864825065006149653 1167774321788674922163265)
            ·
              refine ⟨875830741341506191622449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1167774321788674922163265 875830741341506191622449)
              ·
                refine ⟨656873056006129643716837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 875830741341506191622449 656873056006129643716837)
                ·
                  refine ⟨123163698001149308196907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 656873056006129643716837 123163698001149308196907)
                  ·
                    rfl

theorem cell20_269843_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 6, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 6, 2, 2, 4].length) (baseStart_269843 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_269843 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_269843 prefixEnd_269843 := by exact prefixLift 269843
  have htrace : WordTrace (prefixWord ++ tailWord_269843) baseStart_269843 baseEnd_269843 := by
    simpa [prefixWord, tailWord_269843, baseEnd_269843] using wordTrace_append hprefix tailTrace_269843
  have hstable : (prefixWord ++ tailWord_269843).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_269843).length < 2 ^ (prefixWord ++ tailWord_269843).sum := by decide
  have hdescent : baseEnd_269843 < baseStart_269843 := by decide
  rcases family_descends (prefixWord ++ tailWord_269843) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_269856 : List Nat := [2, 1, 1, 6, 1, 3, 1, 3, 2]
def baseStart_269856 : Nat := 118140960795 + 269856 * 2 ^ 59
def prefixEnd_269856 : Nat := 4983230072969 + 3 ^ 40 * 269856 * 2
def baseEnd_269856 : Nat := 123169631555379040763521

theorem tailTrace_269856 : CollatzResearch.WordTrace tailWord_269856 prefixEnd_269856 123169631555379040763521 := by
  unfold tailWord_269856
  simp only [CollatzResearch.WordTrace]
  refine ⟨4921228455182637290338711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6561637940243516387118281 4921228455182637290338711)
  ·
    refine ⟨7381842682773955935508067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4921228455182637290338711 7381842682773955935508067)
    ·
      refine ⟨11072764024160933903262101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7381842682773955935508067 11072764024160933903262101)
      ·
        refine ⟨519035813632543776715411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 11072764024160933903262101 519035813632543776715411)
        ·
          refine ⟨778553720448815665073117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 519035813632543776715411 778553720448815665073117)
          ·
            refine ⟨291957645168305874402419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 778553720448815665073117 291957645168305874402419)
            ·
              refine ⟨437936467752458811603629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 291957645168305874402419 437936467752458811603629)
              ·
                refine ⟨164226175407172054351361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 437936467752458811603629 164226175407172054351361)
                ·
                  refine ⟨123169631555379040763521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 164226175407172054351361 123169631555379040763521)
                  ·
                    rfl

theorem cell20_269856_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 3, 1, 3, 2].length) (baseStart_269856 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_269856 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_269856 prefixEnd_269856 := by exact prefixLift 269856
  have htrace : WordTrace (prefixWord ++ tailWord_269856) baseStart_269856 baseEnd_269856 := by
    simpa [prefixWord, tailWord_269856, baseEnd_269856] using wordTrace_append hprefix tailTrace_269856
  have hstable : (prefixWord ++ tailWord_269856).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_269856).length < 2 ^ (prefixWord ++ tailWord_269856).sum := by decide
  have hdescent : baseEnd_269856 < baseStart_269856 := by decide
  rcases family_descends (prefixWord ++ tailWord_269856) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_269874 : List Nat := [3, 2, 1, 1, 2, 1, 1, 6, 3]
def baseStart_269874 : Nat := 118140960795 + 269874 * 2 ^ 59
def prefixEnd_269874 : Nat := 4983230072969 + 3 ^ 40 * 269874 * 2
def baseEnd_269874 : Nat := 123177847245850978163447

theorem tailTrace_269874 : CollatzResearch.WordTrace tailWord_269874 prefixEnd_269874 123177847245850978163447 := by
  unfold tailWord_269874
  simp only [CollatzResearch.WordTrace]
  refine ⟨2460778356075015913708169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6562075616200042436555117 2460778356075015913708169)
  ·
    refine ⟨1845583767056261935281127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2460778356075015913708169 1845583767056261935281127)
    ·
      refine ⟨2768375650584392902921691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1845583767056261935281127 2768375650584392902921691)
      ·
        refine ⟨4152563475876589354382537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2768375650584392902921691 4152563475876589354382537)
        ·
          refine ⟨3114422606907442015786903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4152563475876589354382537 3114422606907442015786903)
          ·
            refine ⟨4671633910361163023680355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3114422606907442015786903 4671633910361163023680355)
            ·
              refine ⟨7007450865541744535520533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4671633910361163023680355 7007450865541744535520533)
              ·
                refine ⟨328474259322269275102525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 7007450865541744535520533 328474259322269275102525)
                ·
                  refine ⟨123177847245850978163447, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 328474259322269275102525 123177847245850978163447)
                  ·
                    rfl

theorem cell20_269874_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 1, 6, 3].length) (baseStart_269874 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_269874 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_269874 prefixEnd_269874 := by exact prefixLift 269874
  have htrace : WordTrace (prefixWord ++ tailWord_269874) baseStart_269874 baseEnd_269874 := by
    simpa [prefixWord, tailWord_269874, baseEnd_269874] using wordTrace_append hprefix tailTrace_269874
  have hstable : (prefixWord ++ tailWord_269874).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_269874).length < 2 ^ (prefixWord ++ tailWord_269874).sum := by decide
  have hdescent : baseEnd_269874 < baseStart_269874 := by decide
  rcases family_descends (prefixWord ++ tailWord_269874) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_269957 : List Nat := [1, 3, 1, 1, 4, 1, 3, 2, 4]
def baseStart_269957 : Nat := 118140960795 + 269957 * 2 ^ 59
def prefixEnd_269957 : Nat := 4983230072969 + 3 ^ 40 * 269957 * 2
def baseEnd_269957 : Nat := 123215730707471578396441

theorem tailTrace_269957 : CollatzResearch.WordTrace tailWord_269957 prefixEnd_269957 123215730707471578396441 := by
  unfold tailWord_269957
  simp only [CollatzResearch.WordTrace]
  refine ⟨9846140682999368830104125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6564093788666245886736083 9846140682999368830104125)
  ·
    refine ⟨3692302756124763311289047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9846140682999368830104125 3692302756124763311289047)
    ·
      refine ⟨5538454134187144966933571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3692302756124763311289047 5538454134187144966933571)
      ·
        refine ⟨8307681201280717450400357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5538454134187144966933571 8307681201280717450400357)
        ·
          refine ⟨1557690225240134521950067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 8307681201280717450400357 1557690225240134521950067)
          ·
            refine ⟨2336535337860201782925101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1557690225240134521950067 2336535337860201782925101)
            ·
              refine ⟨876200751697575668596913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2336535337860201782925101 876200751697575668596913)
              ·
                refine ⟨657150563773181751447685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 876200751697575668596913 657150563773181751447685)
                ·
                  refine ⟨123215730707471578396441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 657150563773181751447685 123215730707471578396441)
                  ·
                    rfl

theorem cell20_269957_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 3, 2, 4].length) (baseStart_269957 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_269957 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_269957 prefixEnd_269957 := by exact prefixLift 269957
  have htrace : WordTrace (prefixWord ++ tailWord_269957) baseStart_269957 baseEnd_269957 := by
    simpa [prefixWord, tailWord_269957, baseEnd_269957] using wordTrace_append hprefix tailTrace_269957
  have hstable : (prefixWord ++ tailWord_269957).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_269957).length < 2 ^ (prefixWord ++ tailWord_269957).sum := by decide
  have hdescent : baseEnd_269957 < baseStart_269957 := by decide
  rcases family_descends (prefixWord ++ tailWord_269957) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_269970 : List Nat := [3, 2, 3, 1, 3, 1, 2, 3, 2]
def baseStart_269970 : Nat := 118140960795 + 269970 * 2 ^ 59
def prefixEnd_269970 : Nat := 4983230072969 + 3 ^ 40 * 269970 * 2
def baseEnd_269970 : Nat := 123221664261701310963055

theorem tailTrace_269970 : CollatzResearch.WordTrace tailWord_269970 prefixEnd_269970 123221664261701310963055 := by
  unfold tailWord_269970
  simp only [CollatzResearch.WordTrace]
  refine ⟨2461653707988068012581841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6564409887968181366884909 2461653707988068012581841)
  ·
    refine ⟨1846240280991051009436381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2461653707988068012581841 1846240280991051009436381)
    ·
      refine ⟨692340105371644128538643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1846240280991051009436381 692340105371644128538643)
      ·
        refine ⟨1038510158057466192807965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 692340105371644128538643 1038510158057466192807965)
        ·
          refine ⟨389441309271549822302987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1038510158057466192807965 389441309271549822302987)
          ·
            refine ⟨584161963907324733454481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 389441309271549822302987 584161963907324733454481)
            ·
              refine ⟨438121472930493550090861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 584161963907324733454481 438121472930493550090861)
              ·
                refine ⟨164295552348935081284073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 438121472930493550090861 164295552348935081284073)
                ·
                  refine ⟨123221664261701310963055, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 164295552348935081284073 123221664261701310963055)
                  ·
                    rfl

theorem cell20_269970_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 3, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 3, 1, 2, 3, 2].length) (baseStart_269970 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_269970 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_269970 prefixEnd_269970 := by exact prefixLift 269970
  have htrace : WordTrace (prefixWord ++ tailWord_269970) baseStart_269970 baseEnd_269970 := by
    simpa [prefixWord, tailWord_269970, baseEnd_269970] using wordTrace_append hprefix tailTrace_269970
  have hstable : (prefixWord ++ tailWord_269970).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_269970).length < 2 ^ (prefixWord ++ tailWord_269970).sum := by decide
  have hdescent : baseEnd_269970 < baseStart_269970 := by decide
  rcases family_descends (prefixWord ++ tailWord_269970) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_269988 : List Nat := [2, 3, 1, 2, 2, 3, 1, 1, 5]
def baseStart_269988 : Nat := 118140960795 + 269988 * 2 ^ 59
def prefixEnd_269988 : Nat := 4983230072969 + 3 ^ 40 * 269988 * 2
def baseEnd_269988 : Nat := 123229879952173248362981

theorem tailTrace_269988 : CollatzResearch.WordTrace tailWord_269988 prefixEnd_269988 123229879952173248362981 := by
  unfold tailWord_269988
  simp only [CollatzResearch.WordTrace]
  refine ⟨4923635672943530562241309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6564847563924707416321745 4923635672943530562241309)
  ·
    refine ⟨1846363377353823960840491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4923635672943530562241309 1846363377353823960840491)
    ·
      refine ⟨2769545066030735941260737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1846363377353823960840491 2769545066030735941260737)
      ·
        refine ⟨2077158799523051955945553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2769545066030735941260737 2077158799523051955945553)
        ·
          refine ⟨1557869099642288966959165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2077158799523051955945553 1557869099642288966959165)
          ·
            refine ⟨584200912365858362609687, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1557869099642288966959165 584200912365858362609687)
            ·
              refine ⟨876301368548787543914531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 584200912365858362609687 876301368548787543914531)
              ·
                refine ⟨1314452052823181315871797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 876301368548787543914531 1314452052823181315871797)
                ·
                  refine ⟨123229879952173248362981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1314452052823181315871797 123229879952173248362981)
                  ·
                    rfl

theorem cell20_269988_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 3, 1, 1, 5].length) (baseStart_269988 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_269988 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_269988 prefixEnd_269988 := by exact prefixLift 269988
  have htrace : WordTrace (prefixWord ++ tailWord_269988) baseStart_269988 baseEnd_269988 := by
    simpa [prefixWord, tailWord_269988, baseEnd_269988] using wordTrace_append hprefix tailTrace_269988
  have hstable : (prefixWord ++ tailWord_269988).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_269988).length < 2 ^ (prefixWord ++ tailWord_269988).sum := by decide
  have hdescent : baseEnd_269988 < baseStart_269988 := by decide
  rcases family_descends (prefixWord ++ tailWord_269988) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_270022 : List Nat := [6, 1, 2, 1, 1, 1, 1, 2, 5]
def baseStart_270022 : Nat := 118140960795 + 270022 * 2 ^ 59
def prefixEnd_270022 : Nat := 4983230072969 + 3 ^ 40 * 270022 * 2
def baseEnd_270022 : Nat := 123245398478620241229509

theorem tailTrace_270022 : CollatzResearch.WordTrace tailWord_270022 prefixEnd_270022 123245398478620241229509 := by
  unfold tailWord_270022
  simp only [CollatzResearch.WordTrace]
  refine ⟨307765982117621404100635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 6565674285175923287480213 307765982117621404100635)
  ·
    refine ⟨461648973176432106150953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 307765982117621404100635 461648973176432106150953)
    ·
      refine ⟨346236729882324079613215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 461648973176432106150953 346236729882324079613215)
      ·
        refine ⟨519355094823486119419823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 346236729882324079613215 519355094823486119419823)
        ·
          refine ⟨779032642235229179129735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 519355094823486119419823 779032642235229179129735)
          ·
            refine ⟨1168548963352843768694603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 779032642235229179129735 1168548963352843768694603)
            ·
              refine ⟨1752823445029265653041905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1168548963352843768694603 1752823445029265653041905)
              ·
                refine ⟨1314617583771949239781429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1752823445029265653041905 1314617583771949239781429)
                ·
                  refine ⟨123245398478620241229509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1314617583771949239781429 123245398478620241229509)
                  ·
                    rfl

theorem cell20_270022_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 1, 1, 2, 5].length) (baseStart_270022 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_270022 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_270022 prefixEnd_270022 := by exact prefixLift 270022
  have htrace : WordTrace (prefixWord ++ tailWord_270022) baseStart_270022 baseEnd_270022 := by
    simpa [prefixWord, tailWord_270022, baseEnd_270022] using wordTrace_append hprefix tailTrace_270022
  have hstable : (prefixWord ++ tailWord_270022).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_270022).length < 2 ^ (prefixWord ++ tailWord_270022).sum := by decide
  have hdescent : baseEnd_270022 < baseStart_270022 := by decide
  rcases family_descends (prefixWord ++ tailWord_270022) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_270047 : List Nat := [1, 1, 2, 3, 2, 2, 1, 3, 5]
def baseStart_270047 : Nat := 118140960795 + 270047 * 2 ^ 59
def prefixEnd_270047 : Nat := 4983230072969 + 3 ^ 40 * 270047 * 2
def baseEnd_270047 : Nat := 123256809159831265396073

theorem tailTrace_270047 : CollatzResearch.WordTrace tailWord_270047 prefixEnd_270047 123256809159831265396073 := by
  unfold tailWord_270047
  simp only [CollatzResearch.WordTrace]
  refine ⟨9849423252673314200880395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6566282168448876133920263 9849423252673314200880395)
  ·
    refine ⟨14774134879009971301320593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9849423252673314200880395 14774134879009971301320593)
    ·
      refine ⟨11080601159257478475990445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14774134879009971301320593 11080601159257478475990445)
      ·
        refine ⟨4155225434721554428496417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11080601159257478475990445 4155225434721554428496417)
        ·
          refine ⟨3116419076041165821372313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4155225434721554428496417 3116419076041165821372313)
          ·
            refine ⟨2337314307030874366029235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3116419076041165821372313 2337314307030874366029235)
            ·
              refine ⟨3505971460546311549043853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2337314307030874366029235 3505971460546311549043853)
              ·
                refine ⟨1314739297704866830891445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3505971460546311549043853 1314739297704866830891445)
                ·
                  refine ⟨123256809159831265396073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1314739297704866830891445 123256809159831265396073)
                  ·
                    rfl

theorem cell20_270047_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 1, 3, 5].length) (baseStart_270047 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_270047 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_270047 prefixEnd_270047 := by exact prefixLift 270047
  have htrace : WordTrace (prefixWord ++ tailWord_270047) baseStart_270047 baseEnd_270047 := by
    simpa [prefixWord, tailWord_270047, baseEnd_270047] using wordTrace_append hprefix tailTrace_270047
  have hstable : (prefixWord ++ tailWord_270047).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_270047).length < 2 ^ (prefixWord ++ tailWord_270047).sum := by decide
  have hdescent : baseEnd_270047 < baseStart_270047 := by decide
  rcases family_descends (prefixWord ++ tailWord_270047) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_270088 : List Nat := [2, 1, 3, 2, 2, 1, 2, 5, 2]
def baseStart_270088 : Nat := 118140960795 + 270088 * 2 ^ 59
def prefixEnd_270088 : Nat := 4983230072969 + 3 ^ 40 * 270088 * 2
def baseEnd_270088 : Nat := 123275522677017345029239

theorem tailTrace_270088 : CollatzResearch.WordTrace tailWord_270088 prefixEnd_270088 123275522677017345029239 := by
  unfold tailWord_270088
  simp only [CollatzResearch.WordTrace]
  refine ⟨4925459322762389101561459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6567279097016518802081945 4925459322762389101561459)
  ·
    refine ⟨7388188984143583652342189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4925459322762389101561459 7388188984143583652342189)
    ·
      refine ⟨2770570869053843869628321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7388188984143583652342189 2770570869053843869628321)
      ·
        refine ⟨2077928151790382902221241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2770570869053843869628321 2077928151790382902221241)
        ·
          refine ⟨1558446113842787176665931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2077928151790382902221241 1558446113842787176665931)
          ·
            refine ⟨2337669170764180764998897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1558446113842787176665931 2337669170764180764998897)
            ·
              refine ⟨1753251878073135573749173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2337669170764180764998897 1753251878073135573749173)
              ·
                refine ⟨164367363569356460038985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1753251878073135573749173 164367363569356460038985)
                ·
                  refine ⟨123275522677017345029239, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 164367363569356460038985 123275522677017345029239)
                  ·
                    rfl

theorem cell20_270088_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 2, 5, 2].length) (baseStart_270088 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_270088 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_270088 prefixEnd_270088 := by exact prefixLift 270088
  have htrace : WordTrace (prefixWord ++ tailWord_270088) baseStart_270088 baseEnd_270088 := by
    simpa [prefixWord, tailWord_270088, baseEnd_270088] using wordTrace_append hprefix tailTrace_270088
  have hstable : (prefixWord ++ tailWord_270088).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_270088).length < 2 ^ (prefixWord ++ tailWord_270088).sum := by decide
  have hdescent : baseEnd_270088 < baseStart_270088 := by decide
  rcases family_descends (prefixWord ++ tailWord_270088) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_270098 : List Nat := [3, 2, 4, 1, 1, 2, 2, 2, 3]
def baseStart_270098 : Nat := 118140960795 + 270098 * 2 ^ 59
def prefixEnd_270098 : Nat := 4983230072969 + 3 ^ 40 * 270098 * 2
def baseEnd_270098 : Nat := 123280086949501754695865

theorem tailTrace_270098 : CollatzResearch.WordTrace tailWord_270098 prefixEnd_270098 123280086949501754695865 := by
  unfold tailWord_270098
  simp only [CollatzResearch.WordTrace]
  refine ⟨2462820843872137477746737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6567522250325699940657965 2462820843872137477746737)
  ·
    refine ⟨1847115632904103108310053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2462820843872137477746737 1847115632904103108310053)
    ·
      refine ⟨346334181169519332808135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1847115632904103108310053 346334181169519332808135)
      ·
        refine ⟨519501271754278999212203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 346334181169519332808135 519501271754278999212203)
        ·
          refine ⟨779251907631418498818305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 519501271754278999212203 779251907631418498818305)
          ·
            refine ⟨584438930723563874113729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 779251907631418498818305 584438930723563874113729)
            ·
              refine ⟨438329198042672905585297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 584438930723563874113729 438329198042672905585297)
              ·
                refine ⟨328746898532004679188973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 438329198042672905585297 328746898532004679188973)
                ·
                  refine ⟨123280086949501754695865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 328746898532004679188973 123280086949501754695865)
                  ·
                    rfl

theorem cell20_270098_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 2, 2, 2, 3].length) (baseStart_270098 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_270098 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_270098 prefixEnd_270098 := by exact prefixLift 270098
  have htrace : WordTrace (prefixWord ++ tailWord_270098) baseStart_270098 baseEnd_270098 := by
    simpa [prefixWord, tailWord_270098, baseEnd_270098] using wordTrace_append hprefix tailTrace_270098
  have hstable : (prefixWord ++ tailWord_270098).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_270098).length < 2 ^ (prefixWord ++ tailWord_270098).sum := by decide
  have hdescent : baseEnd_270098 < baseStart_270098 := by decide
  rcases family_descends (prefixWord ++ tailWord_270098) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_270143 : List Nat := [1, 1, 2, 2, 6, 1, 2, 3, 2]
def baseStart_270143 : Nat := 118140960795 + 270143 * 2 ^ 59
def prefixEnd_270143 : Nat := 4983230072969 + 3 ^ 40 * 270143 * 2
def baseEnd_270143 : Nat := 123300626175681598195681

theorem tailTrace_270143 : CollatzResearch.WordTrace tailWord_270143 prefixEnd_270143 123300626175681598195681 := by
  unfold tailWord_270143
  simp only [CollatzResearch.WordTrace]
  refine ⟨9852924660325522596375083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6568616440217015064250055 9852924660325522596375083)
  ·
    refine ⟨14779386990488283894562625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9852924660325522596375083 14779386990488283894562625)
    ·
      refine ⟨11084540242866212920921969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14779386990488283894562625 11084540242866212920921969)
      ·
        refine ⟨8313405182149659690691477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11084540242866212920921969 8313405182149659690691477)
        ·
          refine ⟨389690867913265298001163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 8313405182149659690691477 389690867913265298001163)
          ·
            refine ⟨584536301869897947001745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 389690867913265298001163 584536301869897947001745)
            ·
              refine ⟨438402226402423460251309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 584536301869897947001745 438402226402423460251309)
              ·
                refine ⟨164400834900908797594241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 438402226402423460251309 164400834900908797594241)
                ·
                  refine ⟨123300626175681598195681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 164400834900908797594241 123300626175681598195681)
                  ·
                    rfl

theorem cell20_270143_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 6, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 6, 1, 2, 3, 2].length) (baseStart_270143 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_270143 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_270143 prefixEnd_270143 := by exact prefixLift 270143
  have htrace : WordTrace (prefixWord ++ tailWord_270143) baseStart_270143 baseEnd_270143 := by
    simpa [prefixWord, tailWord_270143, baseEnd_270143] using wordTrace_append hprefix tailTrace_270143
  have hstable : (prefixWord ++ tailWord_270143).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_270143).length < 2 ^ (prefixWord ++ tailWord_270143).sum := by decide
  have hdescent : baseEnd_270143 < baseStart_270143 := by decide
  rcases family_descends (prefixWord ++ tailWord_270143) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_270150 : List Nat := [6, 1, 1, 2, 1, 2, 7]
def baseStart_270150 : Nat := 118140960795 + 270150 * 2 ^ 59
def prefixEnd_270150 : Nat := 4983230072969 + 3 ^ 40 * 270150 * 2
def baseEnd_270150 : Nat := 13700424574046742773591

theorem tailTrace_270150 : CollatzResearch.WordTrace tailWord_270150 prefixEnd_270150 13700424574046742773591 := by
  unfold tailWord_270150
  simp only [CollatzResearch.WordTrace]
  refine ⟨307911874103130087246247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 6568786647533441861253269 307911874103130087246247)
  ·
    refine ⟨461867811154695130869371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 307911874103130087246247 461867811154695130869371)
    ·
      refine ⟨692801716732042696304057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 461867811154695130869371 692801716732042696304057)
      ·
        refine ⟨519601287549032022228043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 692801716732042696304057 519601287549032022228043)
        ·
          refine ⟨779401931323548033342065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 519601287549032022228043 779401931323548033342065)
          ·
            refine ⟨584551448492661025006549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 779401931323548033342065 584551448492661025006549)
            ·
              refine ⟨13700424574046742773591, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 584551448492661025006549 13700424574046742773591)
              ·
                rfl

theorem cell20_270150_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 2, 7].length) (baseStart_270150 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_270150 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_270150 prefixEnd_270150 := by exact prefixLift 270150
  have htrace : WordTrace (prefixWord ++ tailWord_270150) baseStart_270150 baseEnd_270150 := by
    simpa [prefixWord, tailWord_270150, baseEnd_270150] using wordTrace_append hprefix tailTrace_270150
  have hstable : (prefixWord ++ tailWord_270150).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_270150).length < 2 ^ (prefixWord ++ tailWord_270150).sum := by decide
  have hdescent : baseEnd_270150 < baseStart_270150 := by decide
  rcases family_descends (prefixWord ++ tailWord_270150) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_270157 : List Nat := [1, 6, 1, 2, 1, 2, 1, 1, 5]
def baseStart_270157 : Nat := 118140960795 + 270157 * 2 ^ 59
def prefixEnd_270157 : Nat := 4983230072969 + 3 ^ 40 * 270157 * 2
def baseEnd_270157 : Nat := 123307016157159771728957

theorem tailTrace_270157 : CollatzResearch.WordTrace tailWord_270157 prefixEnd_270157 123307016157159771728957 := by
  unfold tailWord_270157
  simp only [CollatzResearch.WordTrace]
  refine ⟨9853435282274802987384725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6568956854849868658256483 9853435282274802987384725)
  ·
    refine ⟨461879778856631390033659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 9853435282274802987384725 461879778856631390033659)
    ·
      refine ⟨692819668284947085050489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 461879778856631390033659 692819668284947085050489)
      ·
        refine ⟨519614751213710313787867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 692819668284947085050489 519614751213710313787867)
        ·
          refine ⟨779422126820565470681801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 519614751213710313787867 779422126820565470681801)
          ·
            refine ⟨584566595115424103011351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 779422126820565470681801 584566595115424103011351)
            ·
              refine ⟨876849892673136154517027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 584566595115424103011351 876849892673136154517027)
              ·
                refine ⟨1315274839009704231775541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 876849892673136154517027 1315274839009704231775541)
                ·
                  refine ⟨123307016157159771728957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1315274839009704231775541 123307016157159771728957)
                  ·
                    rfl

theorem cell20_270157_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 2, 1, 1, 5].length) (baseStart_270157 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_270157 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_270157 prefixEnd_270157 := by exact prefixLift 270157
  have htrace : WordTrace (prefixWord ++ tailWord_270157) baseStart_270157 baseEnd_270157 := by
    simpa [prefixWord, tailWord_270157, baseEnd_270157] using wordTrace_append hprefix tailTrace_270157
  have hstable : (prefixWord ++ tailWord_270157).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_270157).length < 2 ^ (prefixWord ++ tailWord_270157).sum := by decide
  have hdescent : baseEnd_270157 < baseStart_270157 := by decide
  rcases family_descends (prefixWord ++ tailWord_270157) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_270164 : List Nat := [2, 4, 1, 1, 3, 2, 2, 1, 4]
def baseStart_270164 : Nat := 118140960795 + 270164 * 2 ^ 59
def prefixEnd_270164 : Nat := 4983230072969 + 3 ^ 40 * 270164 * 2
def baseEnd_270164 : Nat := 123310211147898858495595

theorem tailTrace_270164 : CollatzResearch.WordTrace tailWord_270164 prefixEnd_270164 123310211147898858495595 := by
  unfold tailWord_270164
  simp only [CollatzResearch.WordTrace]
  refine ⟨4926845296624721591444773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6569127062166295455259697 4926845296624721591444773)
  ·
    refine ⟨923783493117135298395895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 4926845296624721591444773 923783493117135298395895)
    ·
      refine ⟨1385675239675702947593843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 923783493117135298395895 1385675239675702947593843)
      ·
        refine ⟨2078512859513554421390765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1385675239675702947593843 2078512859513554421390765)
        ·
          refine ⟨779442322317582908021537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2078512859513554421390765 779442322317582908021537)
          ·
            refine ⟨584581741738187181016153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 779442322317582908021537 584581741738187181016153)
            ·
              refine ⟨438436306303640385762115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 584581741738187181016153 438436306303640385762115)
              ·
                refine ⟨657654459455460578643173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 438436306303640385762115 657654459455460578643173)
                ·
                  refine ⟨123310211147898858495595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 657654459455460578643173 123310211147898858495595)
                  ·
                    rfl

theorem cell20_270164_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 2, 2, 1, 4].length) (baseStart_270164 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_270164 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_270164 prefixEnd_270164 := by exact prefixLift 270164
  have htrace : WordTrace (prefixWord ++ tailWord_270164) baseStart_270164 baseEnd_270164 := by
    simpa [prefixWord, tailWord_270164, baseEnd_270164] using wordTrace_append hprefix tailTrace_270164
  have hstable : (prefixWord ++ tailWord_270164).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_270164).length < 2 ^ (prefixWord ++ tailWord_270164).sum := by decide
  have hdescent : baseEnd_270164 < baseStart_270164 := by decide
  rcases family_descends (prefixWord ++ tailWord_270164) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_270202 : List Nat := [3, 1, 1, 1, 1, 1, 7, 3, 2]
def baseStart_270202 : Nat := 118140960795 + 270202 * 2 ^ 59
def prefixEnd_270202 : Nat := 4983230072969 + 3 ^ 40 * 270202 * 2
def baseEnd_270202 : Nat := 123327555383339615228773

theorem tailTrace_270202 : CollatzResearch.WordTrace tailWord_270202 prefixEnd_270202 123327555383339615228773 := by
  unfold tailWord_270202
  simp only [CollatzResearch.WordTrace]
  refine ⟨2463769141777943918193215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6570051044741183781848573 2463769141777943918193215)
  ·
    refine ⟨3695653712666915877289823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2463769141777943918193215 3695653712666915877289823)
    ·
      refine ⟨5543480569000373815934735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3695653712666915877289823 5543480569000373815934735)
      ·
        refine ⟨8315220853500560723902103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5543480569000373815934735 8315220853500560723902103)
        ·
          refine ⟨12472831280250841085853155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8315220853500560723902103 12472831280250841085853155)
          ·
            refine ⟨18709246920376261628779733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12472831280250841085853155 18709246920376261628779733)
            ·
              refine ⟨438497974696318631924525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 18709246920376261628779733 438497974696318631924525)
              ·
                refine ⟨164436740511119486971697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 438497974696318631924525 164436740511119486971697)
                ·
                  refine ⟨123327555383339615228773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 164436740511119486971697 123327555383339615228773)
                  ·
                    rfl

theorem cell20_270202_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 7, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 7, 3, 2].length) (baseStart_270202 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_270202 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_270202 prefixEnd_270202 := by exact prefixLift 270202
  have htrace : WordTrace (prefixWord ++ tailWord_270202) baseStart_270202 baseEnd_270202 := by
    simpa [prefixWord, tailWord_270202, baseEnd_270202] using wordTrace_append hprefix tailTrace_270202
  have hstable : (prefixWord ++ tailWord_270202).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_270202).length < 2 ^ (prefixWord ++ tailWord_270202).sum := by decide
  have hdescent : baseEnd_270202 < baseStart_270202 := by decide
  rcases family_descends (prefixWord ++ tailWord_270202) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_270268 : List Nat := [2, 2, 2, 5, 9]
def baseStart_270268 : Nat := 118140960795 + 270268 * 2 ^ 59
def prefixEnd_270268 : Nat := 4983230072969 + 3 ^ 40 * 270268 * 2
def baseEnd_270268 : Nat := 1522934315823910111463

theorem tailTrace_270268 : CollatzResearch.WordTrace tailWord_270268 prefixEnd_270268 1522934315823910111463 := by
  unfold tailWord_270268
  simp only [CollatzResearch.WordTrace]
  refine ⟨4928741892436334472337729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6571655856581779296450305 4928741892436334472337729)
  ·
    refine ⟨3696556419327250854253297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4928741892436334472337729 3696556419327250854253297)
    ·
      refine ⟨2772417314495438140689973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3696556419327250854253297 2772417314495438140689973)
      ·
        refine ⟨259914123233947325689685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 2772417314495438140689973 259914123233947325689685)
        ·
          refine ⟨1522934315823910111463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 9 259914123233947325689685 1522934315823910111463)
          ·
            rfl

theorem cell20_270268_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 5, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 5, 9].length) (baseStart_270268 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_270268 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_270268 prefixEnd_270268 := by exact prefixLift 270268
  have htrace : WordTrace (prefixWord ++ tailWord_270268) baseStart_270268 baseEnd_270268 := by
    simpa [prefixWord, tailWord_270268, baseEnd_270268] using wordTrace_append hprefix tailTrace_270268
  have hstable : (prefixWord ++ tailWord_270268).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_270268).length < 2 ^ (prefixWord ++ tailWord_270268).sum := by decide
  have hdescent : baseEnd_270268 < baseStart_270268 := by decide
  rcases family_descends (prefixWord ++ tailWord_270268) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_270289 : List Nat := [1, 2, 2, 1, 2, 1, 2, 9]
def baseStart_270289 : Nat := 118140960795 + 270289 * 2 ^ 59
def prefixEnd_270289 : Nat := 4983230072969 + 3 ^ 40 * 270289 * 2
def baseEnd_270289 : Nat := 41122421517984659776139

theorem tailTrace_270289 : CollatzResearch.WordTrace tailWord_270289 prefixEnd_270289 41122421517984659776139 := by
  unfold tailWord_270289
  simp only [CollatzResearch.WordTrace]
  refine ⟨9858249717796589531189921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6572166478531059687459947 9858249717796589531189921)
  ·
    refine ⟨7393687288347442148392441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9858249717796589531189921 7393687288347442148392441)
    ·
      refine ⟨5545265466260581611294331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7393687288347442148392441 5545265466260581611294331)
      ·
        refine ⟨8317898199390872416941497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5545265466260581611294331 8317898199390872416941497)
        ·
          refine ⟨6238423649543154312706123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8317898199390872416941497 6238423649543154312706123)
          ·
            refine ⟨9357635474314731469059185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6238423649543154312706123 9357635474314731469059185)
            ·
              refine ⟨7018226605736048601794389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9357635474314731469059185 7018226605736048601794389)
              ·
                refine ⟨41122421517984659776139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 7018226605736048601794389 41122421517984659776139)
                ·
                  rfl

theorem cell20_270289_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 2, 9].length) (baseStart_270289 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_270289 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_270289 prefixEnd_270289 := by exact prefixLift 270289
  have htrace : WordTrace (prefixWord ++ tailWord_270289) baseStart_270289 baseEnd_270289 := by
    simpa [prefixWord, tailWord_270289, baseEnd_270289] using wordTrace_append hprefix tailTrace_270289
  have hstable : (prefixWord ++ tailWord_270289).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_270289).length < 2 ^ (prefixWord ++ tailWord_270289).sum := by decide
  have hdescent : baseEnd_270289 < baseStart_270289 := by decide
  rcases family_descends (prefixWord ++ tailWord_270289) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_270292 : List Nat := [2, 4, 1, 2, 1, 1, 1, 5, 3]
def baseStart_270292 : Nat := 118140960795 + 270292 * 2 ^ 59
def prefixEnd_270292 : Nat := 4983230072969 + 3 ^ 40 * 270292 * 2
def baseEnd_270292 : Nat := 123368633835699302228405

theorem tailTrace_270292 : CollatzResearch.WordTrace tailWord_270292 prefixEnd_270292 123368633835699302228405 := by
  unfold tailWord_270292
  simp only [CollatzResearch.WordTrace]
  refine ⟨4929179568392860521774565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6572239424523814029032753 4929179568392860521774565)
  ·
    refine ⟨924221169073661347832731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 4929179568392860521774565 924221169073661347832731)
    ·
      refine ⟨1386331753610492021749097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 924221169073661347832731 1386331753610492021749097)
      ·
        refine ⟨1039748815207869016311823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1386331753610492021749097 1039748815207869016311823)
        ·
          refine ⟨1559623222811803524467735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1039748815207869016311823 1559623222811803524467735)
          ·
            refine ⟨2339434834217705286701603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1559623222811803524467735 2339434834217705286701603)
            ·
              refine ⟨3509152251326557930052405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2339434834217705286701603 3509152251326557930052405)
              ·
                refine ⟨328983023561864805942413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 3509152251326557930052405 328983023561864805942413)
                ·
                  refine ⟨123368633835699302228405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 328983023561864805942413 123368633835699302228405)
                  ·
                    rfl

theorem cell20_270292_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 1, 5, 3].length) (baseStart_270292 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_270292 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_270292 prefixEnd_270292 := by exact prefixLift 270292
  have htrace : WordTrace (prefixWord ++ tailWord_270292) baseStart_270292 baseEnd_270292 := by
    simpa [prefixWord, tailWord_270292, baseEnd_270292] using wordTrace_append hprefix tailTrace_270292
  have hstable : (prefixWord ++ tailWord_270292).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_270292).length < 2 ^ (prefixWord ++ tailWord_270292).sum := by decide
  have hdescent : baseEnd_270292 < baseStart_270292 := by decide
  rcases family_descends (prefixWord ++ tailWord_270292) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_270326 : List Nat := [5, 1, 1, 1, 4, 2, 1, 2, 3]
def baseStart_270326 : Nat := 118140960795 + 270326 * 2 ^ 59
def prefixEnd_270326 : Nat := 4983230072969 + 3 ^ 40 * 270326 * 2
def baseEnd_270326 : Nat := 123384152362146295094933

theorem tailTrace_270326 : CollatzResearch.WordTrace tailWord_270326 prefixEnd_270326 123384152362146295094933 := by
  unfold tailWord_270326
  simp only [CollatzResearch.WordTrace]
  refine ⟨616224951166409053142927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 6573066145775029900191221 616224951166409053142927)
  ·
    refine ⟨924337426749613579714391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 616224951166409053142927 924337426749613579714391)
    ·
      refine ⟨1386506140124420369571587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 924337426749613579714391 1386506140124420369571587)
      ·
        refine ⟨2079759210186630554357381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1386506140124420369571587 2079759210186630554357381)
        ·
          refine ⟨389954851909993228942009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2079759210186630554357381 389954851909993228942009)
          ·
            refine ⟨292466138932494921706507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 389954851909993228942009 292466138932494921706507)
            ·
              refine ⟨438699208398742382559761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 292466138932494921706507 438699208398742382559761)
              ·
                refine ⟨329024406299056786919821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 438699208398742382559761 329024406299056786919821)
                ·
                  refine ⟨123384152362146295094933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 329024406299056786919821 123384152362146295094933)
                  ·
                    rfl

theorem cell20_270326_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 4, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 4, 2, 1, 2, 3].length) (baseStart_270326 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_270326 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_270326 prefixEnd_270326 := by exact prefixLift 270326
  have htrace : WordTrace (prefixWord ++ tailWord_270326) baseStart_270326 baseEnd_270326 := by
    simpa [prefixWord, tailWord_270326, baseEnd_270326] using wordTrace_append hprefix tailTrace_270326
  have hstable : (prefixWord ++ tailWord_270326).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_270326).length < 2 ^ (prefixWord ++ tailWord_270326).sum := by decide
  have hdescent : baseEnd_270326 < baseStart_270326 := by decide
  rcases family_descends (prefixWord ++ tailWord_270326) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_270337 : List Nat := [1, 2, 4, 1, 2, 1, 4, 1, 4]
def baseStart_270337 : Nat := 118140960795 + 270337 * 2 ^ 59
def prefixEnd_270337 : Nat := 4983230072969 + 3 ^ 40 * 270337 * 2
def baseEnd_270337 : Nat := 123389173061879145728221

theorem tailTrace_270337 : CollatzResearch.WordTrace tailWord_270337 prefixEnd_270337 123389173061879145728221 := by
  unfold tailWord_270337
  simp only [CollatzResearch.WordTrace]
  refine ⟨9860000421622693728937265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6573333614415129152624843 9860000421622693728937265)
  ·
    refine ⟨7395000316217020296702949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9860000421622693728937265 7395000316217020296702949)
    ·
      refine ⟨1386562559290691305631803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 7395000316217020296702949 1386562559290691305631803)
      ·
        refine ⟨2079843838936036958447705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1386562559290691305631803 2079843838936036958447705)
        ·
          refine ⟨1559882879202027718835779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2079843838936036958447705 1559882879202027718835779)
          ·
            refine ⟨2339824318803041578253669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1559882879202027718835779 2339824318803041578253669)
            ·
              refine ⟨438717059775570295922563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2339824318803041578253669 438717059775570295922563)
              ·
                refine ⟨658075589663355443883845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 438717059775570295922563 658075589663355443883845)
                ·
                  refine ⟨123389173061879145728221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 658075589663355443883845 123389173061879145728221)
                  ·
                    rfl

theorem cell20_270337_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 4, 1, 4].length) (baseStart_270337 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_270337 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_270337 prefixEnd_270337 := by exact prefixLift 270337
  have htrace : WordTrace (prefixWord ++ tailWord_270337) baseStart_270337 baseEnd_270337 := by
    simpa [prefixWord, tailWord_270337, baseEnd_270337] using wordTrace_append hprefix tailTrace_270337
  have hstable : (prefixWord ++ tailWord_270337).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_270337).length < 2 ^ (prefixWord ++ tailWord_270337).sum := by decide
  have hdescent : baseEnd_270337 < baseStart_270337 := by decide
  rcases family_descends (prefixWord ++ tailWord_270337) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_270382 : List Nat := [4, 1, 3, 1, 1, 2, 8]
def baseStart_270382 : Nat := 118140960795 + 270382 * 2 ^ 59
def prefixEnd_270382 : Nat := 4983230072969 + 3 ^ 40 * 270382 * 2
def baseEnd_270382 : Nat := 13712190254228776580893

theorem tailTrace_270382 : CollatzResearch.WordTrace tailWord_270382 prefixEnd_270382 13712190254228776580893 := by
  unfold tailWord_270382
  simp only [CollatzResearch.WordTrace]
  refine ⟨1232705213307458301790675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 6574427804306444276216933 1232705213307458301790675)
  ·
    refine ⟨1849057819961187452686013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1232705213307458301790675 1849057819961187452686013)
    ·
      refine ⟨693396682485445294757255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1849057819961187452686013 693396682485445294757255)
      ·
        refine ⟨1040095023728167942135883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 693396682485445294757255 1040095023728167942135883)
        ·
          refine ⟨1560142535592251913203825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1040095023728167942135883 1560142535592251913203825)
          ·
            refine ⟨1170106901694188934902869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1560142535592251913203825 1170106901694188934902869)
            ·
              refine ⟨13712190254228776580893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 1170106901694188934902869 13712190254228776580893)
              ·
                rfl

theorem cell20_270382_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 2, 8].length) (baseStart_270382 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_270382 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_270382 prefixEnd_270382 := by exact prefixLift 270382
  have htrace : WordTrace (prefixWord ++ tailWord_270382) baseStart_270382 baseEnd_270382 := by
    simpa [prefixWord, tailWord_270382, baseEnd_270382] using wordTrace_append hprefix tailTrace_270382
  have hstable : (prefixWord ++ tailWord_270382).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_270382).length < 2 ^ (prefixWord ++ tailWord_270382).sum := by decide
  have hdescent : baseEnd_270382 < baseStart_270382 := by decide
  rcases family_descends (prefixWord ++ tailWord_270382) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_270388 : List Nat := [2, 5, 1, 2, 3, 1, 1, 1, 4]
def baseStart_270388 : Nat := 118140960795 + 270388 * 2 ^ 59
def prefixEnd_270388 : Nat := 4983230072969 + 3 ^ 40 * 270388 * 2
def baseEnd_270388 : Nat := 123412450851549635028013

theorem tailTrace_270388 : CollatzResearch.WordTrace tailWord_270388 prefixEnd_270388 123412450851549635028013 := by
  unfold tailWord_270388
  simp only [CollatzResearch.WordTrace]
  refine ⟨4930930272218964719521909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6574573696291952959362545 4930930272218964719521909)
  ·
    refine ⟨462274713020527942455179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 4930930272218964719521909 462274713020527942455179)
    ·
      refine ⟨693412069530791913682769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 462274713020527942455179 693412069530791913682769)
      ·
        refine ⟨520059052148093935262077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 693412069530791913682769 520059052148093935262077)
        ·
          refine ⟨195022144555535225723279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 520059052148093935262077 195022144555535225723279)
          ·
            refine ⟨292533216833302838584919, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 195022144555535225723279 292533216833302838584919)
            ·
              refine ⟨438799825249954257877379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 292533216833302838584919 438799825249954257877379)
              ·
                refine ⟨658199737874931386816069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 438799825249954257877379 658199737874931386816069)
                ·
                  refine ⟨123412450851549635028013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 658199737874931386816069 123412450851549635028013)
                  ·
                    rfl

theorem cell20_270388_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 3, 1, 1, 1, 4].length) (baseStart_270388 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_270388 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_270388 prefixEnd_270388 := by exact prefixLift 270388
  have htrace : WordTrace (prefixWord ++ tailWord_270388) baseStart_270388 baseEnd_270388 := by
    simpa [prefixWord, tailWord_270388, baseEnd_270388] using wordTrace_append hprefix tailTrace_270388
  have hstable : (prefixWord ++ tailWord_270388).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_270388).length < 2 ^ (prefixWord ++ tailWord_270388).sum := by decide
  have hdescent : baseEnd_270388 < baseStart_270388 := by decide
  rcases family_descends (prefixWord ++ tailWord_270388) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_270389 : List Nat := [1, 3, 3, 1, 1, 1, 4, 1, 5]
def baseStart_270389 : Nat := 118140960795 + 270389 * 2 ^ 59
def prefixEnd_270389 : Nat := 4983230072969 + 3 ^ 40 * 270389 * 2
def baseEnd_270389 : Nat := 123412907278798075994675

theorem tailTrace_270389 : CollatzResearch.WordTrace tailWord_270389 prefixEnd_270389 123412907278798075994675 := by
  unfold tailWord_270389
  simp only [CollatzResearch.WordTrace]
  refine ⟨9861897017434306609830221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6574598011622871073220147 9861897017434306609830221)
  ·
    refine ⟨3698211381537864978686333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9861897017434306609830221 3698211381537864978686333)
    ·
      refine ⟨1386829268076699367007375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3698211381537864978686333 1386829268076699367007375)
      ·
        refine ⟨2080243902115049050511063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1386829268076699367007375 2080243902115049050511063)
        ·
          refine ⟨3120365853172573575766595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2080243902115049050511063 3120365853172573575766595)
          ·
            refine ⟨4680548779758860363649893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3120365853172573575766595 4680548779758860363649893)
            ·
              refine ⟨877602896204786318184355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4680548779758860363649893 877602896204786318184355)
              ·
                refine ⟨1316404344307179477276533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 877602896204786318184355 1316404344307179477276533)
                ·
                  refine ⟨123412907278798075994675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1316404344307179477276533 123412907278798075994675)
                  ·
                    rfl

theorem cell20_270389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 4, 1, 5].length) (baseStart_270389 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_270389 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_270389 prefixEnd_270389 := by exact prefixLift 270389
  have htrace : WordTrace (prefixWord ++ tailWord_270389) baseStart_270389 baseEnd_270389 := by
    simpa [prefixWord, tailWord_270389, baseEnd_270389] using wordTrace_append hprefix tailTrace_270389
  have hstable : (prefixWord ++ tailWord_270389).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_270389).length < 2 ^ (prefixWord ++ tailWord_270389).sum := by decide
  have hdescent : baseEnd_270389 < baseStart_270389 := by decide
  rcases family_descends (prefixWord ++ tailWord_270389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_270392 : List Nat := [2, 1, 2, 1, 6, 2, 1, 1, 4]
def baseStart_270392 : Nat := 118140960795 + 270392 * 2 ^ 59
def prefixEnd_270392 : Nat := 4983230072969 + 3 ^ 40 * 270392 * 2
def baseEnd_270392 : Nat := 123414276560543398894663

theorem tailTrace_270392 : CollatzResearch.WordTrace tailWord_270392 prefixEnd_270392 123414276560543398894663 := by
  unfold tailWord_270392
  simp only [CollatzResearch.WordTrace]
  refine ⟨4931003218211719061094715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6574670957615625414792953 4931003218211719061094715)
  ·
    refine ⟨7396504827317578591642073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4931003218211719061094715 7396504827317578591642073)
    ·
      refine ⟨5547378620488183943731555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7396504827317578591642073 5547378620488183943731555)
      ·
        refine ⟨8321067930732275915597333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5547378620488183943731555 8321067930732275915597333)
        ·
          refine ⟨390050059253075433543625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 8321067930732275915597333 390050059253075433543625)
          ·
            refine ⟨292537544439806575157719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 390050059253075433543625 292537544439806575157719)
            ·
              refine ⟨438806316659709862736579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 292537544439806575157719 438806316659709862736579)
              ·
                refine ⟨658209474989564794104869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 438806316659709862736579 658209474989564794104869)
                ·
                  refine ⟨123414276560543398894663, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 658209474989564794104869 123414276560543398894663)
                  ·
                    rfl

theorem cell20_270392_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 6, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 6, 2, 1, 1, 4].length) (baseStart_270392 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_270392 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_270392 prefixEnd_270392 := by exact prefixLift 270392
  have htrace : WordTrace (prefixWord ++ tailWord_270392) baseStart_270392 baseEnd_270392 := by
    simpa [prefixWord, tailWord_270392, baseEnd_270392] using wordTrace_append hprefix tailTrace_270392
  have hstable : (prefixWord ++ tailWord_270392).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_270392).length < 2 ^ (prefixWord ++ tailWord_270392).sum := by decide
  have hdescent : baseEnd_270392 < baseStart_270392 := by decide
  rcases family_descends (prefixWord ++ tailWord_270392) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_270413 : List Nat := [1, 6, 1, 1, 1, 1, 2, 1, 6]
def baseStart_270413 : Nat := 118140960795 + 270413 * 2 ^ 59
def prefixEnd_270413 : Nat := 4983230072969 + 3 ^ 40 * 270413 * 2
def baseEnd_270413 : Nat := 123423861532760659194577

theorem tailTrace_270413 : CollatzResearch.WordTrace tailWord_270413 prefixEnd_270413 123423861532760659194577 := by
  unfold tailWord_270413
  simp only [CollatzResearch.WordTrace]
  refine ⟨9862772369347358708703893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6575181579564905805802595 9862772369347358708703893)
  ·
    refine ⟨462317454813157439470495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 9862772369347358708703893 462317454813157439470495)
    ·
      refine ⟨693476182219736159205743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 462317454813157439470495 693476182219736159205743)
      ·
        refine ⟨1040214273329604238808615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 693476182219736159205743 1040214273329604238808615)
        ·
          refine ⟨1560321409994406358212923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1040214273329604238808615 1560321409994406358212923)
          ·
            refine ⟨2340482114991609537319385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1560321409994406358212923 2340482114991609537319385)
            ·
              refine ⟨1755361586243707152989539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2340482114991609537319385 1755361586243707152989539)
              ·
                refine ⟨2633042379365560729484309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1755361586243707152989539 2633042379365560729484309)
                ·
                  refine ⟨123423861532760659194577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2633042379365560729484309 123423861532760659194577)
                  ·
                    rfl

theorem cell20_270413_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 2, 1, 6].length) (baseStart_270413 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_270413 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_270413 prefixEnd_270413 := by exact prefixLift 270413
  have htrace : WordTrace (prefixWord ++ tailWord_270413) baseStart_270413 baseEnd_270413 := by
    simpa [prefixWord, tailWord_270413, baseEnd_270413] using wordTrace_append hprefix tailTrace_270413
  have hstable : (prefixWord ++ tailWord_270413).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_270413).length < 2 ^ (prefixWord ++ tailWord_270413).sum := by decide
  have hdescent : baseEnd_270413 < baseStart_270413 := by decide
  rcases family_descends (prefixWord ++ tailWord_270413) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_270444 : List Nat := [2, 2, 1, 1, 3, 4, 2, 2, 3]
def baseStart_270444 : Nat := 118140960795 + 270444 * 2 ^ 59
def prefixEnd_270444 : Nat := 4983230072969 + 3 ^ 40 * 270444 * 2
def baseEnd_270444 : Nat := 123438010777462329161117

theorem tailTrace_270444 : CollatzResearch.WordTrace tailWord_270444 prefixEnd_270444 123438010777462329161117 := by
  unfold tailWord_270444
  simp only [CollatzResearch.WordTrace]
  refine ⟨4931951516117525501541193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6575935354823367335388257 4931951516117525501541193)
  ·
    refine ⟨3698963637088144126155895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4931951516117525501541193 3698963637088144126155895)
    ·
      refine ⟨5548445455632216189233843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3698963637088144126155895 5548445455632216189233843)
      ·
        refine ⟨8322668183448324283850765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5548445455632216189233843 8322668183448324283850765)
        ·
          refine ⟨3121000568793121606444037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8322668183448324283850765 3121000568793121606444037)
          ·
            refine ⟨585187606648710301208257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3121000568793121606444037 585187606648710301208257)
            ·
              refine ⟨438890704986532725906193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 585187606648710301208257 438890704986532725906193)
              ·
                refine ⟨329168028739899544429645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 438890704986532725906193 329168028739899544429645)
                ·
                  refine ⟨123438010777462329161117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 329168028739899544429645 123438010777462329161117)
                  ·
                    rfl

theorem cell20_270444_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 4, 2, 2, 3].length) (baseStart_270444 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_270444 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_270444 prefixEnd_270444 := by exact prefixLift 270444
  have htrace : WordTrace (prefixWord ++ tailWord_270444) baseStart_270444 baseEnd_270444 := by
    simpa [prefixWord, tailWord_270444, baseEnd_270444] using wordTrace_append hprefix tailTrace_270444
  have hstable : (prefixWord ++ tailWord_270444).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_270444).length < 2 ^ (prefixWord ++ tailWord_270444).sum := by decide
  have hdescent : baseEnd_270444 < baseStart_270444 := by decide
  rcases family_descends (prefixWord ++ tailWord_270444) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_270447 : List Nat := [1, 1, 2, 1, 3, 6, 2, 2, 2]
def baseStart_270447 : Nat := 118140960795 + 270447 * 2 ^ 59
def prefixEnd_270447 : Nat := 4983230072969 + 3 ^ 40 * 270447 * 2
def baseEnd_270447 : Nat := 123439380059207652061105

theorem tailTrace_270447 : CollatzResearch.WordTrace tailWord_270447 prefixEnd_270447 123439380059207652061105 := by
  unfold tailWord_270447
  simp only [CollatzResearch.WordTrace]
  refine ⟨9864012451224182515441595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6576008300816121676961063 9864012451224182515441595)
  ·
    refine ⟨14796018676836273773162393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9864012451224182515441595 14796018676836273773162393)
    ·
      refine ⟨11097014007627205329871795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14796018676836273773162393 11097014007627205329871795)
      ·
        refine ⟨16645521011440807994807693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11097014007627205329871795 16645521011440807994807693)
        ·
          refine ⟨6242070379290302998052885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16645521011440807994807693 6242070379290302998052885)
          ·
            refine ⟨292597049029232953033729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 6242070379290302998052885 292597049029232953033729)
            ·
              refine ⟨219447786771924714775297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 292597049029232953033729 219447786771924714775297)
              ·
                refine ⟨164585840078943536081473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 219447786771924714775297 164585840078943536081473)
                ·
                  refine ⟨123439380059207652061105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 164585840078943536081473 123439380059207652061105)
                  ·
                    rfl

theorem cell20_270447_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 6, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 6, 2, 2, 2].length) (baseStart_270447 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_270447 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_270447 prefixEnd_270447 := by exact prefixLift 270447
  have htrace : WordTrace (prefixWord ++ tailWord_270447) baseStart_270447 baseEnd_270447 := by
    simpa [prefixWord, tailWord_270447, baseEnd_270447] using wordTrace_append hprefix tailTrace_270447
  have hstable : (prefixWord ++ tailWord_270447).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_270447).length < 2 ^ (prefixWord ++ tailWord_270447).sum := by decide
  have hdescent : baseEnd_270447 < baseStart_270447 := by decide
  rcases family_descends (prefixWord ++ tailWord_270447) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_270520 : List Nat := [2, 1, 2, 1, 2, 1, 7, 1, 3]
def baseStart_270520 : Nat := 118140960795 + 270520 * 2 ^ 59
def prefixEnd_270520 : Nat := 4983230072969 + 3 ^ 40 * 270520 * 2
def baseEnd_270520 : Nat := 123472699248343842627473

theorem tailTrace_270520 : CollatzResearch.WordTrace tailWord_270520 prefixEnd_270520 123472699248343842627473 := by
  unfold tailWord_270520
  simp only [CollatzResearch.WordTrace]
  refine ⟨4933337489979857991424507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6577783319973143988566009 4933337489979857991424507)
  ·
    refine ⟨7400006234969786987136761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4933337489979857991424507 7400006234969786987136761)
    ·
      refine ⟨5550004676227340240352571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7400006234969786987136761 5550004676227340240352571)
      ·
        refine ⟨8325007014341010360528857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5550004676227340240352571 8325007014341010360528857)
        ·
          refine ⟨6243755260755757770396643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8325007014341010360528857 6243755260755757770396643)
          ·
            refine ⟨9365632891133636655594965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6243755260755757770396643 9365632891133636655594965)
            ·
              refine ⟨219507020885944609115507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 9365632891133636655594965 219507020885944609115507)
              ·
                refine ⟨329260531328916913673261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 219507020885944609115507 329260531328916913673261)
                ·
                  refine ⟨123472699248343842627473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 329260531328916913673261 123472699248343842627473)
                  ·
                    rfl

theorem cell20_270520_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 7, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 7, 1, 3].length) (baseStart_270520 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_270520 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_270520 prefixEnd_270520 := by exact prefixLift 270520
  have htrace : WordTrace (prefixWord ++ tailWord_270520) baseStart_270520 baseEnd_270520 := by
    simpa [prefixWord, tailWord_270520, baseEnd_270520] using wordTrace_append hprefix tailTrace_270520
  have hstable : (prefixWord ++ tailWord_270520).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_270520).length < 2 ^ (prefixWord ++ tailWord_270520).sum := by decide
  have hdescent : baseEnd_270520 < baseStart_270520 := by decide
  rcases family_descends (prefixWord ++ tailWord_270520) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_270530 : List Nat := [3, 5, 1, 1, 1, 2, 1, 6]
def baseStart_270530 : Nat := 118140960795 + 270530 * 2 ^ 59
def prefixEnd_270530 : Nat := 4983230072969 + 3 ^ 40 * 270530 * 2
def baseEnd_270530 : Nat := 41159087840276084098033

theorem tailTrace_270530 : CollatzResearch.WordTrace tailWord_270530 prefixEnd_270530 41159087840276084098033 := by
  unfold tailWord_270530
  simp only [CollatzResearch.WordTrace]
  refine ⟨2466759927480871922678261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6578026473282325127142029 2466759927480871922678261)
  ·
    refine ⟨231258743201331742751087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 2466759927480871922678261 231258743201331742751087)
    ·
      refine ⟨346888114801997614126631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 231258743201331742751087 346888114801997614126631)
      ·
        refine ⟨520332172202996421189947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 346888114801997614126631 520332172202996421189947)
        ·
          refine ⟨780498258304494631784921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 520332172202996421189947 780498258304494631784921)
          ·
            refine ⟨585373693728370973838691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 780498258304494631784921 585373693728370973838691)
            ·
              refine ⟨878060540592556460758037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 585373693728370973838691 878060540592556460758037)
              ·
                refine ⟨41159087840276084098033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 878060540592556460758037 41159087840276084098033)
                ·
                  rfl

theorem cell20_270530_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 2, 1, 6].length) (baseStart_270530 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_270530 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_270530 prefixEnd_270530 := by exact prefixLift 270530
  have htrace : WordTrace (prefixWord ++ tailWord_270530) baseStart_270530 baseEnd_270530 := by
    simpa [prefixWord, tailWord_270530, baseEnd_270530] using wordTrace_append hprefix tailTrace_270530
  have hstable : (prefixWord ++ tailWord_270530).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_270530).length < 2 ^ (prefixWord ++ tailWord_270530).sum := by decide
  have hdescent : baseEnd_270530 < baseStart_270530 := by decide
  rcases family_descends (prefixWord ++ tailWord_270530) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_270540 : List Nat := [2, 2, 1, 6, 1, 2, 1, 3, 2]
def baseStart_270540 : Nat := 118140960795 + 270540 * 2 ^ 59
def prefixEnd_270540 : Nat := 4983230072969 + 3 ^ 40 * 270540 * 2
def baseEnd_270540 : Nat := 123481827793312661960725

theorem tailTrace_270540 : CollatzResearch.WordTrace tailWord_270540 prefixEnd_270540 123481827793312661960725 := by
  unfold tailWord_270540
  simp only [CollatzResearch.WordTrace]
  refine ⟨4933702219943629699288537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6578269626591506265718049 4933702219943629699288537)
  ·
    refine ⟨3700276664957722274466403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4933702219943629699288537 3700276664957722274466403)
    ·
      refine ⟨5550414997436583411699605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3700276664957722274466403 5550414997436583411699605)
      ·
        refine ⟨260175703004839847423419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 5550414997436583411699605 260175703004839847423419)
        ·
          refine ⟨390263554507259771135129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 260175703004839847423419 390263554507259771135129)
          ·
            refine ⟨292697665880444828351347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 390263554507259771135129 292697665880444828351347)
            ·
              refine ⟨439046498820667242527021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 292697665880444828351347 439046498820667242527021)
              ·
                refine ⟨164642437057750215947633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 439046498820667242527021 164642437057750215947633)
                ·
                  refine ⟨123481827793312661960725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 164642437057750215947633 123481827793312661960725)
                  ·
                    rfl

theorem cell20_270540_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 6, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 6, 1, 2, 1, 3, 2].length) (baseStart_270540 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_270540 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_270540 prefixEnd_270540 := by exact prefixLift 270540
  have htrace : WordTrace (prefixWord ++ tailWord_270540) baseStart_270540 baseEnd_270540 := by
    simpa [prefixWord, tailWord_270540, baseEnd_270540] using wordTrace_append hprefix tailTrace_270540
  have hstable : (prefixWord ++ tailWord_270540).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_270540).length < 2 ^ (prefixWord ++ tailWord_270540).sum := by decide
  have hdescent : baseEnd_270540 < baseStart_270540 := by decide
  rcases family_descends (prefixWord ++ tailWord_270540) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_270565 : List Nat := [1, 3, 1, 4, 2, 1, 3, 1, 4]
def baseStart_270565 : Nat := 118140960795 + 270565 * 2 ^ 59
def prefixEnd_270565 : Nat := 4983230072969 + 3 ^ 40 * 270565 * 2
def baseEnd_270565 : Nat := 123493238474523686127289

theorem tailTrace_270565 : CollatzResearch.WordTrace tailWord_270565 prefixEnd_270565 123493238474523686127289 := by
  unfold tailWord_270565
  simp only [CollatzResearch.WordTrace]
  refine ⟨9868316264796688668237149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6578877509864459112158099 9868316264796688668237149)
  ·
    refine ⟨3700618599298758250588931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9868316264796688668237149 3700618599298758250588931)
    ·
      refine ⟨5550927898948137375883397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3700618599298758250588931 5550927898948137375883397)
      ·
        refine ⟨1040798981052775757978137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 5550927898948137375883397 1040798981052775757978137)
        ·
          refine ⟨780599235789581818483603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1040798981052775757978137 780599235789581818483603)
          ·
            refine ⟨1170898853684372727725405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 780599235789581818483603 1170898853684372727725405)
            ·
              refine ⟨439087070131639772897027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1170898853684372727725405 439087070131639772897027)
              ·
                refine ⟨658630605197459659345541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 439087070131639772897027 658630605197459659345541)
                ·
                  refine ⟨123493238474523686127289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 658630605197459659345541 123493238474523686127289)
                  ·
                    rfl

theorem cell20_270565_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 1, 3, 1, 4].length) (baseStart_270565 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_270565 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_270565 prefixEnd_270565 := by exact prefixLift 270565
  have htrace : WordTrace (prefixWord ++ tailWord_270565) baseStart_270565 baseEnd_270565 := by
    simpa [prefixWord, tailWord_270565, baseEnd_270565] using wordTrace_append hprefix tailTrace_270565
  have hstable : (prefixWord ++ tailWord_270565).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_270565).length < 2 ^ (prefixWord ++ tailWord_270565).sum := by decide
  have hdescent : baseEnd_270565 < baseStart_270565 := by decide
  rcases family_descends (prefixWord ++ tailWord_270565) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_270575 : List Nat := [1, 1, 2, 1, 6, 3, 2, 1, 3]
def baseStart_270575 : Nat := 118140960795 + 270575 * 2 ^ 59
def prefixEnd_270575 : Nat := 4983230072969 + 3 ^ 40 * 270575 * 2
def baseEnd_270575 : Nat := 123497802747008095793915

theorem tailTrace_270575 : CollatzResearch.WordTrace tailWord_270575 prefixEnd_270575 123497802747008095793915 := by
  unfold tailWord_270575
  simp only [CollatzResearch.WordTrace]
  refine ⟨9868680994760460376101179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6579120663173640250734119 9868680994760460376101179)
  ·
    refine ⟨14803021492140690564151769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9868680994760460376101179 14803021492140690564151769)
    ·
      refine ⟨11102266119105517923113827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14803021492140690564151769 11102266119105517923113827)
      ·
        refine ⟨16653399178658276884670741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11102266119105517923113827 16653399178658276884670741)
        ·
          refine ⟨780628086499606728968941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 16653399178658276884670741 780628086499606728968941)
          ·
            refine ⟨292735532437352523363353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 780628086499606728968941 292735532437352523363353)
            ·
              refine ⟨219551649328014392522515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 292735532437352523363353 219551649328014392522515)
              ·
                refine ⟨329327473992021588783773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 219551649328014392522515 329327473992021588783773)
                ·
                  refine ⟨123497802747008095793915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 329327473992021588783773 123497802747008095793915)
                  ·
                    rfl

theorem cell20_270575_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 3, 2, 1, 3].length) (baseStart_270575 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_270575 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_270575 prefixEnd_270575 := by exact prefixLift 270575
  have htrace : WordTrace (prefixWord ++ tailWord_270575) baseStart_270575 baseEnd_270575 := by
    simpa [prefixWord, tailWord_270575, baseEnd_270575] using wordTrace_append hprefix tailTrace_270575
  have hstable : (prefixWord ++ tailWord_270575).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_270575).length < 2 ^ (prefixWord ++ tailWord_270575).sum := by decide
  have hdescent : baseEnd_270575 < baseStart_270575 := by decide
  rcases family_descends (prefixWord ++ tailWord_270575) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_270579 : List Nat := [1, 1, 1, 2, 2, 4, 3, 3, 3]
def baseStart_270579 : Nat := 118140960795 + 270579 * 2 ^ 59
def prefixEnd_270579 : Nat := 4983230072969 + 3 ^ 40 * 270579 * 2
def baseEnd_270579 : Nat := 123499628456001859660565

theorem tailTrace_270579 : CollatzResearch.WordTrace tailWord_270579 prefixEnd_270579 123499628456001859660565 := by
  unfold tailWord_270579
  simp only [CollatzResearch.WordTrace]
  refine ⟨9868826886745969059246791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6579217924497312706164527 9868826886745969059246791)
  ·
    refine ⟨14803240330118953588870187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9868826886745969059246791 14803240330118953588870187)
    ·
      refine ⟨22204860495178430383305281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14803240330118953588870187 22204860495178430383305281)
      ·
        refine ⟨16653645371383822787478961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22204860495178430383305281 16653645371383822787478961)
        ·
          refine ⟨12490234028537867090609221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16653645371383822787478961 12490234028537867090609221)
          ·
            refine ⟨2341918880350850079489229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 12490234028537867090609221 2341918880350850079489229)
            ·
              refine ⟨878219580131568779808461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2341918880350850079489229 878219580131568779808461)
              ·
                refine ⟨329332342549338292428173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 878219580131568779808461 329332342549338292428173)
                ·
                  refine ⟨123499628456001859660565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 329332342549338292428173 123499628456001859660565)
                  ·
                    rfl

theorem cell20_270579_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 3, 3, 3].length) (baseStart_270579 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_270579 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_270579 prefixEnd_270579 := by exact prefixLift 270579
  have htrace : WordTrace (prefixWord ++ tailWord_270579) baseStart_270579 baseEnd_270579 := by
    simpa [prefixWord, tailWord_270579, baseEnd_270579] using wordTrace_append hprefix tailTrace_270579
  have hstable : (prefixWord ++ tailWord_270579).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_270579).length < 2 ^ (prefixWord ++ tailWord_270579).sum := by decide
  have hdescent : baseEnd_270579 < baseStart_270579 := by decide
  rcases family_descends (prefixWord ++ tailWord_270579) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_270593 : List Nat := [1, 2, 4, 1, 1, 2, 1, 8]
def baseStart_270593 : Nat := 118140960795 + 270593 * 2 ^ 59
def prefixEnd_270593 : Nat := 4983230072969 + 3 ^ 40 * 270593 * 2
def baseEnd_270593 : Nat := 41168672812493344397947

theorem tailTrace_270593 : CollatzResearch.WordTrace tailWord_270593 prefixEnd_270593 41168672812493344397947 := by
  unfold tailWord_270593
  simp only [CollatzResearch.WordTrace]
  refine ⟨9869337508695249450256433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6579558339130166300170955 9869337508695249450256433)
  ·
    refine ⟨7402003131521437087692325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9869337508695249450256433 7402003131521437087692325)
    ·
      refine ⟨1387875587160269453942311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 7402003131521437087692325 1387875587160269453942311)
      ·
        refine ⟨2081813380740404180913467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1387875587160269453942311 2081813380740404180913467)
        ·
          refine ⟨3122720071110606271370201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2081813380740404180913467 3122720071110606271370201)
          ·
            refine ⟨2342040053332954703527651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3122720071110606271370201 2342040053332954703527651)
            ·
              refine ⟨3513060079999432055291477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2342040053332954703527651 3513060079999432055291477)
              ·
                refine ⟨41168672812493344397947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 3513060079999432055291477 41168672812493344397947)
                ·
                  rfl

theorem cell20_270593_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 1, 8].length) (baseStart_270593 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_270593 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_270593 prefixEnd_270593 := by exact prefixLift 270593
  have htrace : WordTrace (prefixWord ++ tailWord_270593) baseStart_270593 baseEnd_270593 := by
    simpa [prefixWord, tailWord_270593, baseEnd_270593] using wordTrace_append hprefix tailTrace_270593
  have hstable : (prefixWord ++ tailWord_270593).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_270593).length < 2 ^ (prefixWord ++ tailWord_270593).sum := by decide
  have hdescent : baseEnd_270593 < baseStart_270593 := by decide
  rcases family_descends (prefixWord ++ tailWord_270593) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_270603 : List Nat := [1, 1, 1, 1, 5, 2, 2, 5, 2]
def baseStart_270603 : Nat := 118140960795 + 270603 * 2 ^ 59
def prefixEnd_270603 : Nat := 4983230072969 + 3 ^ 40 * 270603 * 2
def baseEnd_270603 : Nat := 123510582709964442860467

theorem tailTrace_270603 : CollatzResearch.WordTrace tailWord_270603 prefixEnd_270603 123510582709964442860467 := by
  unfold tailWord_270603
  simp only [CollatzResearch.WordTrace]
  refine ⟨9869702238659021158120463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6579801492439347438746975 9869702238659021158120463)
  ·
    refine ⟨14804553357988531737180695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9869702238659021158120463 14804553357988531737180695)
    ·
      refine ⟨22206830036982797605771043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14804553357988531737180695 22206830036982797605771043)
      ·
        refine ⟨33310245055474196408656565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22206830036982797605771043 33310245055474196408656565)
        ·
          refine ⟨3122835473950705913311553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 33310245055474196408656565 3122835473950705913311553)
          ·
            refine ⟨2342126605463029434983665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3122835473950705913311553 2342126605463029434983665)
            ·
              refine ⟨1756594954097272076237749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2342126605463029434983665 1756594954097272076237749)
              ·
                refine ⟨164680776946619257147289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1756594954097272076237749 164680776946619257147289)
                ·
                  refine ⟨123510582709964442860467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 164680776946619257147289 123510582709964442860467)
                  ·
                    rfl

theorem cell20_270603_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 2, 5, 2].length) (baseStart_270603 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_270603 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_270603 prefixEnd_270603 := by exact prefixLift 270603
  have htrace : WordTrace (prefixWord ++ tailWord_270603) baseStart_270603 baseEnd_270603 := by
    simpa [prefixWord, tailWord_270603, baseEnd_270603] using wordTrace_append hprefix tailTrace_270603
  have hstable : (prefixWord ++ tailWord_270603).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_270603).length < 2 ^ (prefixWord ++ tailWord_270603).sum := by decide
  have hdescent : baseEnd_270603 < baseStart_270603 := by decide
  rcases family_descends (prefixWord ++ tailWord_270603) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_270641 : List Nat := [1, 2, 2, 3, 4, 1, 1, 2, 4]
def baseStart_270641 : Nat := 118140960795 + 270641 * 2 ^ 59
def prefixEnd_270641 : Nat := 4983230072969 + 3 ^ 40 * 270641 * 2
def baseEnd_270641 : Nat := 123527926945405199593645

theorem tailTrace_270641 : CollatzResearch.WordTrace tailWord_270641 prefixEnd_270641 123527926945405199593645 := by
  unfold tailWord_270641
  simp only [CollatzResearch.WordTrace]
  refine ⟨9871088212521353648003777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6580725475014235765335851 9871088212521353648003777)
  ·
    refine ⟨7403316159391015236002833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9871088212521353648003777 7403316159391015236002833)
    ·
      refine ⟨5552487119543261427002125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7403316159391015236002833 5552487119543261427002125)
      ·
        refine ⟨2082182669828723035125797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5552487119543261427002125 2082182669828723035125797)
        ·
          refine ⟨390409250592885569086087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2082182669828723035125797 390409250592885569086087)
          ·
            refine ⟨585613875889328353629131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 390409250592885569086087 585613875889328353629131)
            ·
              refine ⟨878420813833992530443697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 585613875889328353629131 878420813833992530443697)
              ·
                refine ⟨658815610375494397832773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 878420813833992530443697 658815610375494397832773)
                ·
                  refine ⟨123527926945405199593645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 658815610375494397832773 123527926945405199593645)
                  ·
                    rfl

theorem cell20_270641_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 4, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 4, 1, 1, 2, 4].length) (baseStart_270641 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_270641 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_270641 prefixEnd_270641 := by exact prefixLift 270641
  have htrace : WordTrace (prefixWord ++ tailWord_270641) baseStart_270641 baseEnd_270641 := by
    simpa [prefixWord, tailWord_270641, baseEnd_270641] using wordTrace_append hprefix tailTrace_270641
  have hstable : (prefixWord ++ tailWord_270641).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_270641).length < 2 ^ (prefixWord ++ tailWord_270641).sum := by decide
  have hdescent : baseEnd_270641 < baseStart_270641 := by decide
  rcases family_descends (prefixWord ++ tailWord_270641) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_270672 : List Nat := [2, 1, 1, 1, 1, 8, 1, 2, 3]
def baseStart_270672 : Nat := 118140960795 + 270672 * 2 ^ 59
def prefixEnd_270672 : Nat := 4983230072969 + 3 ^ 40 * 270672 * 2
def baseEnd_270672 : Nat := 123542076190106869560185

theorem tailTrace_270672 : CollatzResearch.WordTrace tailWord_270672 prefixEnd_270672 123542076190106869560185 := by
  unfold tailWord_270672
  simp only [CollatzResearch.WordTrace]
  refine ⟨4936109437704522971191135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6581479250272697294921513 4936109437704522971191135)
  ·
    refine ⟨7404164156556784456786703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4936109437704522971191135 7404164156556784456786703)
    ·
      refine ⟨11106246234835176685180055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7404164156556784456786703 11106246234835176685180055)
      ·
        refine ⟨16659369352252765027770083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11106246234835176685180055 16659369352252765027770083)
        ·
          refine ⟨24989054028379147541655125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16659369352252765027770083 24989054028379147541655125)
          ·
            refine ⟨292840476895068135253771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 24989054028379147541655125 292840476895068135253771)
            ·
              refine ⟨439260715342602202880657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 292840476895068135253771 439260715342602202880657)
              ·
                refine ⟨329445536506951652160493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 439260715342602202880657 329445536506951652160493)
                ·
                  refine ⟨123542076190106869560185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 329445536506951652160493 123542076190106869560185)
                  ·
                    rfl

theorem cell20_270672_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 8, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 8, 1, 2, 3].length) (baseStart_270672 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_270672 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_270672 prefixEnd_270672 := by exact prefixLift 270672
  have htrace : WordTrace (prefixWord ++ tailWord_270672) baseStart_270672 baseEnd_270672 := by
    simpa [prefixWord, tailWord_270672, baseEnd_270672] using wordTrace_append hprefix tailTrace_270672
  have hstable : (prefixWord ++ tailWord_270672).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_270672).length < 2 ^ (prefixWord ++ tailWord_270672).sum := by decide
  have hdescent : baseEnd_270672 < baseStart_270672 := by decide
  rcases family_descends (prefixWord ++ tailWord_270672) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_270679 : List Nat := [1, 1, 3, 2, 3, 1, 1, 6, 2]
def baseStart_270679 : Nat := 118140960795 + 270679 * 2 ^ 59
def prefixEnd_270679 : Nat := 4983230072969 + 3 ^ 40 * 270679 * 2
def baseEnd_270679 : Nat := 123545271180845956326823

theorem tailTrace_270679 : CollatzResearch.WordTrace tailWord_270679 prefixEnd_270679 123545271180845956326823 := by
  unfold tailWord_270679
  simp only [CollatzResearch.WordTrace]
  refine ⟨9872474186383686137887091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6581649457589124091924727 9872474186383686137887091)
  ·
    refine ⟨14808711279575529206830637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9872474186383686137887091 14808711279575529206830637)
    ·
      refine ⟨5553266729840823452561489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14808711279575529206830637 5553266729840823452561489)
      ·
        refine ⟨4164950047380617589421117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5553266729840823452561489 4164950047380617589421117)
        ·
          refine ⟨1561856267767731596032919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4164950047380617589421117 1561856267767731596032919)
          ·
            refine ⟨2342784401651597394049379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1561856267767731596032919 2342784401651597394049379)
            ·
              refine ⟨3514176602477396091074069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2342784401651597394049379 3514176602477396091074069)
              ·
                refine ⟨164727028241127941769097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3514176602477396091074069 164727028241127941769097)
                ·
                  refine ⟨123545271180845956326823, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 164727028241127941769097 123545271180845956326823)
                  ·
                    rfl

theorem cell20_270679_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 1, 6, 2].length) (baseStart_270679 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_270679 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_270679 prefixEnd_270679 := by exact prefixLift 270679
  have htrace : WordTrace (prefixWord ++ tailWord_270679) baseStart_270679 baseEnd_270679 := by
    simpa [prefixWord, tailWord_270679, baseEnd_270679] using wordTrace_append hprefix tailTrace_270679
  have hstable : (prefixWord ++ tailWord_270679).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_270679).length < 2 ^ (prefixWord ++ tailWord_270679).sum := by decide
  have hdescent : baseEnd_270679 < baseStart_270679 := by decide
  rcases family_descends (prefixWord ++ tailWord_270679) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_270730 : List Nat := [3, 1, 2, 5, 1, 1, 3, 2, 2]
def baseStart_270730 : Nat := 118140960795 + 270730 * 2 ^ 59
def prefixEnd_270730 : Nat := 4983230072969 + 3 ^ 40 * 270730 * 2
def baseEnd_270730 : Nat := 123568548970516445626615

theorem tailTrace_270730 : CollatzResearch.WordTrace tailWord_270730 prefixEnd_270730 123568548970516445626615 := by
  unfold tailWord_270730
  simp only [CollatzResearch.WordTrace]
  refine ⟨2468583577299730461998411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6582889539465947898662429 2468583577299730461998411)
  ·
    refine ⟨3702875365949595692997617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2468583577299730461998411 3702875365949595692997617)
    ·
      refine ⟨2777156524462196769748213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3702875365949595692997617 2777156524462196769748213)
      ·
        refine ⟨260358424168330947163895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 2777156524462196769748213 260358424168330947163895)
        ·
          refine ⟨390537636252496420745843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 260358424168330947163895 390537636252496420745843)
          ·
            refine ⟨585806454378744631118765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 390537636252496420745843 585806454378744631118765)
            ·
              refine ⟨219677420392029236669537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 585806454378744631118765 219677420392029236669537)
              ·
                refine ⟨164758065294021927502153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 219677420392029236669537 164758065294021927502153)
                ·
                  refine ⟨123568548970516445626615, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 164758065294021927502153 123568548970516445626615)
                  ·
                    rfl

theorem cell20_270730_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 5, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 5, 1, 1, 3, 2, 2].length) (baseStart_270730 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_270730 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_270730 prefixEnd_270730 := by exact prefixLift 270730
  have htrace : WordTrace (prefixWord ++ tailWord_270730) baseStart_270730 baseEnd_270730 := by
    simpa [prefixWord, tailWord_270730, baseEnd_270730] using wordTrace_append hprefix tailTrace_270730
  have hstable : (prefixWord ++ tailWord_270730).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_270730).length < 2 ^ (prefixWord ++ tailWord_270730).sum := by decide
  have hdescent : baseEnd_270730 < baseStart_270730 := by decide
  rcases family_descends (prefixWord ++ tailWord_270730) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_270734 : List Nat := [4, 1, 1, 4, 1, 3, 1, 1, 4]
def baseStart_270734 : Nat := 118140960795 + 270734 * 2 ^ 59
def prefixEnd_270734 : Nat := 4983230072969 + 3 ^ 40 * 270734 * 2
def baseEnd_270734 : Nat := 123570374679510209493265

theorem tailTrace_270734 : CollatzResearch.WordTrace tailWord_270734 prefixEnd_270734 123570374679510209493265 := by
  unfold tailWord_270734
  simp only [CollatzResearch.WordTrace]
  refine ⟨1234310025148053816392407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 6582986800789620354092837 1234310025148053816392407)
  ·
    refine ⟨1851465037722080724588611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1234310025148053816392407 1851465037722080724588611)
    ·
      refine ⟨2777197556583121086882917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1851465037722080724588611 2777197556583121086882917)
      ·
        refine ⟨520724541859335203790547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2777197556583121086882917 520724541859335203790547)
        ·
          refine ⟨781086812789002805685821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 520724541859335203790547 781086812789002805685821)
          ·
            refine ⟨292907554795876052132183, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 781086812789002805685821 292907554795876052132183)
            ·
              refine ⟨439361332193814078198275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 292907554795876052132183 439361332193814078198275)
              ·
                refine ⟨659041998290721117297413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 439361332193814078198275 659041998290721117297413)
                ·
                  refine ⟨123570374679510209493265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 659041998290721117297413 123570374679510209493265)
                  ·
                    rfl

theorem cell20_270734_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 3, 1, 1, 4].length) (baseStart_270734 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_270734 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_270734 prefixEnd_270734 := by exact prefixLift 270734
  have htrace : WordTrace (prefixWord ++ tailWord_270734) baseStart_270734 baseEnd_270734 := by
    simpa [prefixWord, tailWord_270734, baseEnd_270734] using wordTrace_append hprefix tailTrace_270734
  have hstable : (prefixWord ++ tailWord_270734).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_270734).length < 2 ^ (prefixWord ++ tailWord_270734).sum := by decide
  have hdescent : baseEnd_270734 < baseStart_270734 := by decide
  rcases family_descends (prefixWord ++ tailWord_270734) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_270745 : List Nat := [1, 2, 1, 2, 1, 4, 4, 5]
def baseStart_270745 : Nat := 118140960795 + 270745 * 2 ^ 59
def prefixEnd_270745 : Nat := 4983230072969 + 3 ^ 40 * 270745 * 2
def baseEnd_270745 : Nat := 41191798459747686708851

theorem tailTrace_270745 : CollatzResearch.WordTrace tailWord_270745 prefixEnd_270745 41191798459747686708851 := by
  unfold tailWord_270745
  simp only [CollatzResearch.WordTrace]
  refine ⟨9874881404144579409789689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6583254269429719606526459 9874881404144579409789689)
  ·
    refine ⟨7406161053108434557342267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9874881404144579409789689 7406161053108434557342267)
    ·
      refine ⟨11109241579662651836013401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7406161053108434557342267 11109241579662651836013401)
      ·
        refine ⟨8331931184746988877010051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11109241579662651836013401 8331931184746988877010051)
        ·
          refine ⟨12497896777120483315515077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8331931184746988877010051 12497896777120483315515077)
          ·
            refine ⟨2343355645710090621659077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 12497896777120483315515077 2343355645710090621659077)
            ·
              refine ⟨439379183570641991561077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2343355645710090621659077 439379183570641991561077)
              ·
                refine ⟨41191798459747686708851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 439379183570641991561077 41191798459747686708851)
                ·
                  rfl

theorem cell20_270745_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 4, 5].length) (baseStart_270745 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_270745 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_270745 prefixEnd_270745 := by exact prefixLift 270745
  have htrace : WordTrace (prefixWord ++ tailWord_270745) baseStart_270745 baseEnd_270745 := by
    simpa [prefixWord, tailWord_270745, baseEnd_270745] using wordTrace_append hprefix tailTrace_270745
  have hstable : (prefixWord ++ tailWord_270745).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_270745).length < 2 ^ (prefixWord ++ tailWord_270745).sum := by decide
  have hdescent : baseEnd_270745 < baseStart_270745 := by decide
  rcases family_descends (prefixWord ++ tailWord_270745) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_270828 : List Nat := [2, 2, 1, 1, 2, 1, 4, 2, 5]
def baseStart_270828 : Nat := 118140960795 + 270828 * 2 ^ 59
def prefixEnd_270828 : Nat := 4983230072969 + 3 ^ 40 * 270828 * 2
def baseEnd_270828 : Nat := 123613278840863660359547

theorem tailTrace_270828 : CollatzResearch.WordTrace tailWord_270828 prefixEnd_270828 123613278840863660359547 := by
  unfold tailWord_270828
  simp only [CollatzResearch.WordTrace]
  refine ⟨4938954331421942292530569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6585272441895923056707425 4938954331421942292530569)
  ·
    refine ⟨3704215748566456719397927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4938954331421942292530569 3704215748566456719397927)
    ·
      refine ⟨5556323622849685079096891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3704215748566456719397927 5556323622849685079096891)
      ·
        refine ⟨8334485434274527618645337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5556323622849685079096891 8334485434274527618645337)
        ·
          refine ⟨6250864075705895713984003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8334485434274527618645337 6250864075705895713984003)
          ·
            refine ⟨9376296113558843570976005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6250864075705895713984003 9376296113558843570976005)
            ·
              refine ⟨1758055521292283169558001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9376296113558843570976005 1758055521292283169558001)
              ·
                refine ⟨1318541640969212377168501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1758055521292283169558001 1318541640969212377168501)
                ·
                  refine ⟨123613278840863660359547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1318541640969212377168501 123613278840863660359547)
                  ·
                    rfl

theorem cell20_270828_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 5].length) (baseStart_270828 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_270828 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_270828 prefixEnd_270828 := by exact prefixLift 270828
  have htrace : WordTrace (prefixWord ++ tailWord_270828) baseStart_270828 baseEnd_270828 := by
    simpa [prefixWord, tailWord_270828, baseEnd_270828] using wordTrace_append hprefix tailTrace_270828
  have hstable : (prefixWord ++ tailWord_270828).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_270828).length < 2 ^ (prefixWord ++ tailWord_270828).sum := by decide
  have hdescent : baseEnd_270828 < baseStart_270828 := by decide
  rcases family_descends (prefixWord ++ tailWord_270828) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_270835 : List Nat := [1, 1, 1, 2, 2, 2, 3, 2, 6]
def baseStart_270835 : Nat := 118140960795 + 270835 * 2 ^ 59
def prefixEnd_270835 : Nat := 4983230072969 + 3 ^ 40 * 270835 * 2
def baseEnd_270835 : Nat := 123616473831602747126185

theorem tailTrace_270835 : CollatzResearch.WordTrace tailWord_270835 prefixEnd_270835 123616473831602747126185 := by
  unfold tailWord_270835
  simp only [CollatzResearch.WordTrace]
  refine ⟨9878163973818524780565959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6585442649212349853710639 9878163973818524780565959)
  ·
    refine ⟨14817245960727787170848939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9878163973818524780565959 14817245960727787170848939)
    ·
      refine ⟨22225868941091680756273409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14817245960727787170848939 22225868941091680756273409)
      ·
        refine ⟨16669401705818760567205057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22225868941091680756273409 16669401705818760567205057)
        ·
          refine ⟨12502051279364070425403793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16669401705818760567205057 12502051279364070425403793)
          ·
            refine ⟨9376538459523052819052845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12502051279364070425403793 9376538459523052819052845)
            ·
              refine ⟨3516201922321144807144817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9376538459523052819052845 3516201922321144807144817)
              ·
                refine ⟨2637151441740858605358613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3516201922321144807144817 2637151441740858605358613)
                ·
                  refine ⟨123616473831602747126185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2637151441740858605358613 123616473831602747126185)
                  ·
                    rfl

theorem cell20_270835_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 3, 2, 6].length) (baseStart_270835 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_270835 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_270835 prefixEnd_270835 := by exact prefixLift 270835
  have htrace : WordTrace (prefixWord ++ tailWord_270835) baseStart_270835 baseEnd_270835 := by
    simpa [prefixWord, tailWord_270835, baseEnd_270835] using wordTrace_append hprefix tailTrace_270835
  have hstable : (prefixWord ++ tailWord_270835).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_270835).length < 2 ^ (prefixWord ++ tailWord_270835).sum := by decide
  have hdescent : baseEnd_270835 < baseStart_270835 := by decide
  rcases family_descends (prefixWord ++ tailWord_270835) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_270876 : List Nat := [2, 2, 3, 1, 2, 2, 4, 4]
def baseStart_270876 : Nat := 118140960795 + 270876 * 2 ^ 59
def prefixEnd_270876 : Nat := 4983230072969 + 3 ^ 40 * 270876 * 2
def baseEnd_270876 : Nat := 41211729116262942253117

theorem tailTrace_270876 : CollatzResearch.WordTrace tailWord_270876 prefixEnd_270876 41211729116262942253117 := by
  unfold tailWord_270876
  simp only [CollatzResearch.WordTrace]
  refine ⟨4939829683334994391404241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6586439577779992521872321 4939829683334994391404241)
  ·
    refine ⟨3704872262501245793553181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4939829683334994391404241 3704872262501245793553181)
    ·
      refine ⟨1389327098437967172582443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3704872262501245793553181 1389327098437967172582443)
      ·
        refine ⟨2083990647656950758873665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1389327098437967172582443 2083990647656950758873665)
        ·
          refine ⟨1562992985742713069155249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2083990647656950758873665 1562992985742713069155249)
          ·
            refine ⟨1172244739307034801866437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1562992985742713069155249 1172244739307034801866437)
            ·
              refine ⟨219795888620069025349957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1172244739307034801866437 219795888620069025349957)
              ·
                refine ⟨41211729116262942253117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 219795888620069025349957 41211729116262942253117)
                ·
                  rfl

theorem cell20_270876_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 2, 4, 4].length) (baseStart_270876 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_270876 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_270876 prefixEnd_270876 := by exact prefixLift 270876
  have htrace : WordTrace (prefixWord ++ tailWord_270876) baseStart_270876 baseEnd_270876 := by
    simpa [prefixWord, tailWord_270876, baseEnd_270876] using wordTrace_append hprefix tailTrace_270876
  have hstable : (prefixWord ++ tailWord_270876).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_270876).length < 2 ^ (prefixWord ++ tailWord_270876).sum := by decide
  have hdescent : baseEnd_270876 < baseStart_270876 := by decide
  rcases family_descends (prefixWord ++ tailWord_270876) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_270904 : List Nat := [2, 1, 2, 1, 4, 1, 1, 3, 5]
def baseStart_270904 : Nat := 118140960795 + 270904 * 2 ^ 59
def prefixEnd_270904 : Nat := 4983230072969 + 3 ^ 40 * 270904 * 2
def baseEnd_270904 : Nat := 123647967311745173825903

theorem tailTrace_270904 : CollatzResearch.WordTrace tailWord_270904 prefixEnd_270904 123647967311745173825903 := by
  unfold tailWord_270904
  simp only [CollatzResearch.WordTrace]
  refine ⟨4940340305284274782413883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6587120407045699709885177 4940340305284274782413883)
  ·
    refine ⟨7410510457926412173620825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4940340305284274782413883 7410510457926412173620825)
    ·
      refine ⟨5557882843444809130215619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7410510457926412173620825 5557882843444809130215619)
      ·
        refine ⟨8336824265167213695323429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5557882843444809130215619 8336824265167213695323429)
        ·
          refine ⟨1563154549718852567873143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 8336824265167213695323429 1563154549718852567873143)
          ·
            refine ⟨2344731824578278851809715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1563154549718852567873143 2344731824578278851809715)
            ·
              refine ⟨3517097736867418277714573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2344731824578278851809715 3517097736867418277714573)
              ·
                refine ⟨1318911651325281854142965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3517097736867418277714573 1318911651325281854142965)
                ·
                  refine ⟨123647967311745173825903, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1318911651325281854142965 123647967311745173825903)
                  ·
                    rfl

theorem cell20_270904_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 1, 3, 5].length) (baseStart_270904 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_270904 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_270904 prefixEnd_270904 := by exact prefixLift 270904
  have htrace : WordTrace (prefixWord ++ tailWord_270904) baseStart_270904 baseEnd_270904 := by
    simpa [prefixWord, tailWord_270904, baseEnd_270904] using wordTrace_append hprefix tailTrace_270904
  have hstable : (prefixWord ++ tailWord_270904).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_270904).length < 2 ^ (prefixWord ++ tailWord_270904).sum := by decide
  have hdescent : baseEnd_270904 < baseStart_270904 := by decide
  rcases family_descends (prefixWord ++ tailWord_270904) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_270952 : List Nat := [2, 1, 4, 3, 3, 7]
def baseStart_270952 : Nat := 118140960795 + 270952 * 2 ^ 59
def prefixEnd_270952 : Nat := 4983230072969 + 3 ^ 40 * 270952 * 2
def baseEnd_270952 : Nat := 4580365771098901489841

theorem tailTrace_270952 : CollatzResearch.WordTrace tailWord_270952 prefixEnd_270952 4580365771098901489841 := by
  unfold tailWord_270952
  simp only [CollatzResearch.WordTrace]
  refine ⟨4941215657197326881287555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6588287542929769175050073 4941215657197326881287555)
  ·
    refine ⟨7411823485795990321931333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4941215657197326881287555 7411823485795990321931333)
    ·
      refine ⟨1389716903586748185362125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 7411823485795990321931333 1389716903586748185362125)
      ·
        refine ⟨521143838845030569510797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1389716903586748185362125 521143838845030569510797)
        ·
          refine ⟨195428939566886463566549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 521143838845030569510797 195428939566886463566549)
          ·
            refine ⟨4580365771098901489841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 195428939566886463566549 4580365771098901489841)
            ·
              rfl

theorem cell20_270952_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 3, 7].length) (baseStart_270952 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_270952 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_270952 prefixEnd_270952 := by exact prefixLift 270952
  have htrace : WordTrace (prefixWord ++ tailWord_270952) baseStart_270952 baseEnd_270952 := by
    simpa [prefixWord, tailWord_270952, baseEnd_270952] using wordTrace_append hprefix tailTrace_270952
  have hstable : (prefixWord ++ tailWord_270952).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_270952).length < 2 ^ (prefixWord ++ tailWord_270952).sum := by decide
  have hdescent : baseEnd_270952 < baseStart_270952 := by decide
  rcases family_descends (prefixWord ++ tailWord_270952) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_270962 : List Nat := [3, 2, 1, 2, 4, 1, 1, 4, 2]
def baseStart_270962 : Nat := 118140960795 + 270962 * 2 ^ 59
def prefixEnd_270962 : Nat := 4983230072969 + 3 ^ 40 * 270962 * 2
def baseEnd_270962 : Nat := 123674440092154749892333

theorem tailTrace_270962 : CollatzResearch.WordTrace tailWord_270962 prefixEnd_270962 123674440092154749892333 := by
  unfold tailWord_270962
  simp only [CollatzResearch.WordTrace]
  refine ⟨2470699011089606367609785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6588530696238950313626093 2470699011089606367609785)
  ·
    refine ⟨1853024258317204775707339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2470699011089606367609785 1853024258317204775707339)
    ·
      refine ⟨2779536387475807163561009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1853024258317204775707339 2779536387475807163561009)
      ·
        refine ⟨2084652290606855372670757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2779536387475807163561009 2084652290606855372670757)
        ·
          refine ⟨390872304488785382375767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2084652290606855372670757 390872304488785382375767)
          ·
            refine ⟨586308456733178073563651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 390872304488785382375767 586308456733178073563651)
            ·
              refine ⟨879462685099767110345477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 586308456733178073563651 879462685099767110345477)
              ·
                refine ⟨164899253456206333189777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 879462685099767110345477 164899253456206333189777)
                ·
                  refine ⟨123674440092154749892333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 164899253456206333189777 123674440092154749892333)
                  ·
                    rfl

theorem cell20_270962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 4, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 4, 1, 1, 4, 2].length) (baseStart_270962 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_270962 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_270962 prefixEnd_270962 := by exact prefixLift 270962
  have htrace : WordTrace (prefixWord ++ tailWord_270962) baseStart_270962 baseEnd_270962 := by
    simpa [prefixWord, tailWord_270962, baseEnd_270962] using wordTrace_append hprefix tailTrace_270962
  have hstable : (prefixWord ++ tailWord_270962).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_270962).length < 2 ^ (prefixWord ++ tailWord_270962).sum := by decide
  have hdescent : baseEnd_270962 < baseStart_270962 := by decide
  rcases family_descends (prefixWord ++ tailWord_270962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_270990 : List Nat := [4, 1, 1, 3, 1, 1, 5, 4]
def baseStart_270990 : Nat := 118140960795 + 270990 * 2 ^ 59
def prefixEnd_270990 : Nat := 4983230072969 + 3 ^ 40 * 270990 * 2
def baseEnd_270990 : Nat := 41229073351703698986295

theorem tailTrace_270990 : CollatzResearch.WordTrace tailWord_270990 prefixEnd_270990 41229073351703698986295 := by
  unfold tailWord_270990
  simp only [CollatzResearch.WordTrace]
  refine ⟨1235477161032123281557303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 6589211525504657501638949 1235477161032123281557303)
  ·
    refine ⟨1853215741548184922335955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1235477161032123281557303 1853215741548184922335955)
    ·
      refine ⟨2779823612322277383503933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1853215741548184922335955 2779823612322277383503933)
      ·
        refine ⟨1042433854620854018813975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2779823612322277383503933 1042433854620854018813975)
        ·
          refine ⟨1563650781931281028220963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1042433854620854018813975 1563650781931281028220963)
          ·
            refine ⟨2345476172896921542331445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1563650781931281028220963 2345476172896921542331445)
            ·
              refine ⟨219888391209086394593573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 2345476172896921542331445 219888391209086394593573)
              ·
                refine ⟨41229073351703698986295, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 219888391209086394593573 41229073351703698986295)
                ·
                  rfl

theorem cell20_270990_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 5, 4].length) (baseStart_270990 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_270990 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_270990 prefixEnd_270990 := by exact prefixLift 270990
  have htrace : WordTrace (prefixWord ++ tailWord_270990) baseStart_270990 baseEnd_270990 := by
    simpa [prefixWord, tailWord_270990, baseEnd_270990] using wordTrace_append hprefix tailTrace_270990
  have hstable : (prefixWord ++ tailWord_270990).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_270990).length < 2 ^ (prefixWord ++ tailWord_270990).sum := by decide
  have hdescent : baseEnd_270990 < baseStart_270990 := by decide
  rcases family_descends (prefixWord ++ tailWord_270990) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_271021 : List Nat := [1, 5, 2, 1, 1, 3, 2, 1, 4]
def baseStart_271021 : Nat := 118140960795 + 271021 * 2 ^ 59
def prefixEnd_271021 : Nat := 4983230072969 + 3 ^ 40 * 271021 * 2
def baseEnd_271021 : Nat := 123701369299812766925425

theorem tailTrace_271021 : CollatzResearch.WordTrace tailWord_271021 prefixEnd_271021 123701369299812766925425 := by
  unfold tailWord_271021
  simp only [CollatzResearch.WordTrace]
  refine ⟨9884947951144678546836917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6589965300763119031224611 9884947951144678546836917)
  ·
    refine ⟨926713870419813613765961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 9884947951144678546836917 926713870419813613765961)
    ·
      refine ⟨695035402814860210324471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 926713870419813613765961 695035402814860210324471)
      ·
        refine ⟨1042553104222290315486707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 695035402814860210324471 1042553104222290315486707)
        ·
          refine ⟨1563829656333435473230061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1042553104222290315486707 1563829656333435473230061)
          ·
            refine ⟨586436121125038302461273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1563829656333435473230061 586436121125038302461273)
            ·
              refine ⟨439827090843778726845955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 586436121125038302461273 439827090843778726845955)
              ·
                refine ⟨659740636265668090268933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 439827090843778726845955 659740636265668090268933)
                ·
                  refine ⟨123701369299812766925425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 659740636265668090268933 123701369299812766925425)
                  ·
                    rfl

theorem cell20_271021_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 3, 2, 1, 4].length) (baseStart_271021 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_271021 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_271021 prefixEnd_271021 := by exact prefixLift 271021
  have htrace : WordTrace (prefixWord ++ tailWord_271021) baseStart_271021 baseEnd_271021 := by
    simpa [prefixWord, tailWord_271021, baseEnd_271021] using wordTrace_append hprefix tailTrace_271021
  have hstable : (prefixWord ++ tailWord_271021).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_271021).length < 2 ^ (prefixWord ++ tailWord_271021).sum := by decide
  have hdescent : baseEnd_271021 < baseStart_271021 := by decide
  rcases family_descends (prefixWord ++ tailWord_271021) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_271041 : List Nat := [1, 2, 6, 2, 2, 1, 2, 4]
def baseStart_271041 : Nat := 118140960795 + 271041 * 2 ^ 59
def prefixEnd_271041 : Nat := 4983230072969 + 3 ^ 40 * 271041 * 2
def baseEnd_271041 : Nat := 41236832614927195419559

theorem tailTrace_271041 : CollatzResearch.WordTrace tailWord_271041 prefixEnd_271041 41236832614927195419559 := by
  unfold tailWord_271041
  simp only [CollatzResearch.WordTrace]
  refine ⟨9885677411072221962564977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6590451607381481308376651 9885677411072221962564977)
  ·
    refine ⟨7414258058304166471923733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9885677411072221962564977 7414258058304166471923733)
    ·
      refine ⟨347543346483007803371425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 7414258058304166471923733 347543346483007803371425)
      ·
        refine ⟨260657509862255852528569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 347543346483007803371425 260657509862255852528569)
        ·
          refine ⟨195493132396691889396427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 260657509862255852528569 195493132396691889396427)
          ·
            refine ⟨293239698595037834094641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 195493132396691889396427 293239698595037834094641)
            ·
              refine ⟨219929773946278375570981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 293239698595037834094641 219929773946278375570981)
              ·
                refine ⟨41236832614927195419559, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 219929773946278375570981 41236832614927195419559)
                ·
                  rfl

theorem cell20_271041_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 2, 2, 1, 2, 4].length) (baseStart_271041 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_271041 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_271041 prefixEnd_271041 := by exact prefixLift 271041
  have htrace : WordTrace (prefixWord ++ tailWord_271041) baseStart_271041 baseEnd_271041 := by
    simpa [prefixWord, tailWord_271041, baseEnd_271041] using wordTrace_append hprefix tailTrace_271041
  have hstable : (prefixWord ++ tailWord_271041).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_271041).length < 2 ^ (prefixWord ++ tailWord_271041).sum := by decide
  have hdescent : baseEnd_271041 < baseStart_271041 := by decide
  rcases family_descends (prefixWord ++ tailWord_271041) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_271076 : List Nat := [2, 3, 1, 1, 1, 5, 3, 2, 2]
def baseStart_271076 : Nat := 118140960795 + 271076 * 2 ^ 59
def prefixEnd_271076 : Nat := 4983230072969 + 3 ^ 40 * 271076 * 2
def baseEnd_271076 : Nat := 123726472798477020091867

theorem tailTrace_271076 : CollatzResearch.WordTrace tailWord_271076 prefixEnd_271076 123726472798477020091867 := by
  unfold tailWord_271076
  simp only [CollatzResearch.WordTrace]
  refine ⟨4943476982972711470044541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6591302643963615293392721 4943476982972711470044541)
  ·
    refine ⟨1853803868614766801266703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4943476982972711470044541 1853803868614766801266703)
    ·
      refine ⟨2780705802922150201900055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1853803868614766801266703 2780705802922150201900055)
      ·
        refine ⟨4171058704383225302850083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2780705802922150201900055 4171058704383225302850083)
        ·
          refine ⟨6256588056574837954275125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4171058704383225302850083 6256588056574837954275125)
          ·
            refine ⟨586555130303891058213293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 6256588056574837954275125 586555130303891058213293)
            ·
              refine ⟨219958173863959146829985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 586555130303891058213293 219958173863959146829985)
              ·
                refine ⟨164968630397969360122489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 219958173863959146829985 164968630397969360122489)
                ·
                  refine ⟨123726472798477020091867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 164968630397969360122489 123726472798477020091867)
                  ·
                    rfl

theorem cell20_271076_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 5, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 5, 3, 2, 2].length) (baseStart_271076 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_271076 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_271076 prefixEnd_271076 := by exact prefixLift 271076
  have htrace : WordTrace (prefixWord ++ tailWord_271076) baseStart_271076 baseEnd_271076 := by
    simpa [prefixWord, tailWord_271076, baseEnd_271076] using wordTrace_append hprefix tailTrace_271076
  have hstable : (prefixWord ++ tailWord_271076).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_271076).length < 2 ^ (prefixWord ++ tailWord_271076).sum := by decide
  have hdescent : baseEnd_271076 < baseStart_271076 := by decide
  rcases family_descends (prefixWord ++ tailWord_271076) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_271087 : List Nat := [1, 1, 2, 1, 5, 3, 2, 5]
def baseStart_271087 : Nat := 118140960795 + 271087 * 2 ^ 59
def prefixEnd_271087 : Nat := 4983230072969 + 3 ^ 40 * 271087 * 2
def baseEnd_271087 : Nat := 41243831166069956908385

theorem tailTrace_271087 : CollatzResearch.WordTrace tailWord_271087 prefixEnd_271087 41243831166069956908385 := by
  unfold tailWord_271087
  simp only [CollatzResearch.WordTrace]
  refine ⟨9887355168905571818739515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6591570112603714545826343 9887355168905571818739515)
  ·
    refine ⟨14831032753358357728109273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9887355168905571818739515 14831032753358357728109273)
    ·
      refine ⟨11123274565018768296081955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14831032753358357728109273 11123274565018768296081955)
      ·
        refine ⟨16684911847528152444122933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11123274565018768296081955 16684911847528152444122933)
        ·
          refine ⟨1564210485705764291636525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 16684911847528152444122933 1564210485705764291636525)
          ·
            refine ⟨586578932139661609363697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1564210485705764291636525 586578932139661609363697)
            ·
              refine ⟨439934199104746207022773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 586578932139661609363697 439934199104746207022773)
              ·
                refine ⟨41243831166069956908385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 439934199104746207022773 41243831166069956908385)
                ·
                  rfl

theorem cell20_271087_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 3, 2, 5].length) (baseStart_271087 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_271087 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_271087 prefixEnd_271087 := by exact prefixLift 271087
  have htrace : WordTrace (prefixWord ++ tailWord_271087) baseStart_271087 baseEnd_271087 := by
    simpa [prefixWord, tailWord_271087, baseEnd_271087] using wordTrace_append hprefix tailTrace_271087
  have hstable : (prefixWord ++ tailWord_271087).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_271087).length < 2 ^ (prefixWord ++ tailWord_271087).sum := by decide
  have hdescent : baseEnd_271087 < baseStart_271087 := by decide
  rcases family_descends (prefixWord ++ tailWord_271087) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_271090 : List Nat := [3, 2, 1, 3, 1, 2, 4, 1, 3]
def baseStart_271090 : Nat := 118140960795 + 271090 * 2 ^ 59
def prefixEnd_271090 : Nat := 4983230072969 + 3 ^ 40 * 271090 * 2
def baseEnd_271090 : Nat := 123732862779955193625143

theorem tailTrace_271090 : CollatzResearch.WordTrace tailWord_271090 prefixEnd_271090 123732862779955193625143 := by
  unfold tailWord_271090
  simp only [CollatzResearch.WordTrace]
  refine ⟨2471866146973675832774681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6591643058596468887399149 2471866146973675832774681)
  ·
    refine ⟨1853899610230256874581011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2471866146973675832774681 1853899610230256874581011)
    ·
      refine ⟨2780849415345385311871517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1853899610230256874581011 2780849415345385311871517)
      ·
        refine ⟨1042818530754519491951819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2780849415345385311871517 1042818530754519491951819)
        ·
          refine ⟨1564227796131779237927729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1042818530754519491951819 1564227796131779237927729)
          ·
            refine ⟨1173170847098834428445797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1564227796131779237927729 1173170847098834428445797)
            ·
              refine ⟨219969533831031455333587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1173170847098834428445797 219969533831031455333587)
              ·
                refine ⟨329954300746547183000381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 219969533831031455333587 329954300746547183000381)
                ·
                  refine ⟨123732862779955193625143, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 329954300746547183000381 123732862779955193625143)
                  ·
                    rfl

theorem cell20_271090_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 2, 4, 1, 3].length) (baseStart_271090 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_271090 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_271090 prefixEnd_271090 := by exact prefixLift 271090
  have htrace : WordTrace (prefixWord ++ tailWord_271090) baseStart_271090 baseEnd_271090 := by
    simpa [prefixWord, tailWord_271090, baseEnd_271090] using wordTrace_append hprefix tailTrace_271090
  have hstable : (prefixWord ++ tailWord_271090).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_271090).length < 2 ^ (prefixWord ++ tailWord_271090).sum := by decide
  have hdescent : baseEnd_271090 < baseStart_271090 := by decide
  rcases family_descends (prefixWord ++ tailWord_271090) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_271101 : List Nat := [1, 4, 1, 1, 1, 1, 4, 1, 6]
def baseStart_271101 : Nat := 118140960795 + 271101 * 2 ^ 59
def prefixEnd_271101 : Nat := 4983230072969 + 3 ^ 40 * 271101 * 2
def baseEnd_271101 : Nat := 123737883479688044258431

theorem tailTrace_271101 : CollatzResearch.WordTrace tailWord_271101 prefixEnd_271101 123737883479688044258431 := by
  unfold tailWord_271101
  simp only [CollatzResearch.WordTrace]
  refine ⟨9887865790854852209749157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6591910527236568139832771 9887865790854852209749157)
  ·
    refine ⟨1853974835785284789327967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 9887865790854852209749157 1853974835785284789327967)
    ·
      refine ⟨2780962253677927183991951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1853974835785284789327967 2780962253677927183991951)
      ·
        refine ⟨4171443380516890775987927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2780962253677927183991951 4171443380516890775987927)
        ·
          refine ⟨6257165070775336163981891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4171443380516890775987927 6257165070775336163981891)
          ·
            refine ⟨9385747606163004245972837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6257165070775336163981891 9385747606163004245972837)
            ·
              refine ⟨1759827676155563296119907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9385747606163004245972837 1759827676155563296119907)
              ·
                refine ⟨2639741514233344944179861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1759827676155563296119907 2639741514233344944179861)
                ·
                  refine ⟨123737883479688044258431, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2639741514233344944179861 123737883479688044258431)
                  ·
                    rfl

theorem cell20_271101_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 4, 1, 6].length) (baseStart_271101 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_271101 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_271101 prefixEnd_271101 := by exact prefixLift 271101
  have htrace : WordTrace (prefixWord ++ tailWord_271101) baseStart_271101 baseEnd_271101 := by
    simpa [prefixWord, tailWord_271101, baseEnd_271101] using wordTrace_append hprefix tailTrace_271101
  have hstable : (prefixWord ++ tailWord_271101).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_271101).length < 2 ^ (prefixWord ++ tailWord_271101).sum := by decide
  have hdescent : baseEnd_271101 < baseStart_271101 := by decide
  rcases family_descends (prefixWord ++ tailWord_271101) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_271135 : List Nat := [1, 1, 2, 4, 2, 3, 1, 4, 2]
def baseStart_271135 : Nat := 118140960795 + 271135 * 2 ^ 59
def prefixEnd_271135 : Nat := 4983230072969 + 3 ^ 40 * 271135 * 2
def baseEnd_271135 : Nat := 123753402006135037124959

theorem tailTrace_271135 : CollatzResearch.WordTrace tailWord_271135 prefixEnd_271135 123753402006135037124959 := by
  unfold tailWord_271135
  simp only [CollatzResearch.WordTrace]
  refine ⟨9889105872731676016486859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6592737248487784010991239 9889105872731676016486859)
  ·
    refine ⟨14833658809097514024730289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9889105872731676016486859 14833658809097514024730289)
    ·
      refine ⟨11125244106823135518547717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14833658809097514024730289 11125244106823135518547717)
      ·
        refine ⟨2085983270029337909727697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 11125244106823135518547717 2085983270029337909727697)
        ·
          refine ⟨1564487452522003432295773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2085983270029337909727697 1564487452522003432295773)
          ·
            refine ⟨586682794695751287110915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1564487452522003432295773 586682794695751287110915)
            ·
              refine ⟨880024192043626930666373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 586682794695751287110915 880024192043626930666373)
              ·
                refine ⟨165004536008180049499945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 880024192043626930666373 165004536008180049499945)
                ·
                  refine ⟨123753402006135037124959, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 165004536008180049499945 123753402006135037124959)
                  ·
                    rfl

theorem cell20_271135_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 3, 1, 4, 2].length) (baseStart_271135 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_271135 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_271135 prefixEnd_271135 := by exact prefixLift 271135
  have htrace : WordTrace (prefixWord ++ tailWord_271135) baseStart_271135 baseEnd_271135 := by
    simpa [prefixWord, tailWord_271135, baseEnd_271135] using wordTrace_append hprefix tailTrace_271135
  have hstable : (prefixWord ++ tailWord_271135).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_271135).length < 2 ^ (prefixWord ++ tailWord_271135).sum := by decide
  have hdescent : baseEnd_271135 < baseStart_271135 := by decide
  rcases family_descends (prefixWord ++ tailWord_271135) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_271139 : List Nat := [1, 1, 1, 4, 2, 1, 1, 5, 4]
def baseStart_271139 : Nat := 118140960795 + 271139 * 2 ^ 59
def prefixEnd_271139 : Nat := 4983230072969 + 3 ^ 40 * 271139 * 2
def baseEnd_271139 : Nat := 123755227715128800991609

theorem tailTrace_271139 : CollatzResearch.WordTrace tailWord_271139 prefixEnd_271139 123755227715128800991609 := by
  unfold tailWord_271139
  simp only [CollatzResearch.WordTrace]
  refine ⟨9889251764717184699632471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6592834509811456466421647 9889251764717184699632471)
  ·
    refine ⟨14833877647075777049448707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9889251764717184699632471 14833877647075777049448707)
    ·
      refine ⟨22250816470613665574173061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14833877647075777049448707 22250816470613665574173061)
      ·
        refine ⟨4172028088240062295157449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 22250816470613665574173061 4172028088240062295157449)
        ·
          refine ⟨3129021066180046721368087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4172028088240062295157449 3129021066180046721368087)
          ·
            refine ⟨4693531599270070082052131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3129021066180046721368087 4693531599270070082052131)
            ·
              refine ⟨7040297398905105123078197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4693531599270070082052131 7040297398905105123078197)
              ·
                refine ⟨660027881147353605288581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 7040297398905105123078197 660027881147353605288581)
                ·
                  refine ⟨123755227715128800991609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 660027881147353605288581 123755227715128800991609)
                  ·
                    rfl

theorem cell20_271139_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 1, 5, 4].length) (baseStart_271139 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_271139 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_271139 prefixEnd_271139 := by exact prefixLift 271139
  have htrace : WordTrace (prefixWord ++ tailWord_271139) baseStart_271139 baseEnd_271139 := by
    simpa [prefixWord, tailWord_271139, baseEnd_271139] using wordTrace_append hprefix tailTrace_271139
  have hstable : (prefixWord ++ tailWord_271139).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_271139).length < 2 ^ (prefixWord ++ tailWord_271139).sum := by decide
  have hdescent : baseEnd_271139 < baseStart_271139 := by decide
  rcases family_descends (prefixWord ++ tailWord_271139) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_271169 : List Nat := [1, 2, 5, 3, 1, 1, 2, 3, 2]
def baseStart_271169 : Nat := 118140960795 + 271169 * 2 ^ 59
def prefixEnd_271169 : Nat := 4983230072969 + 3 ^ 40 * 271169 * 2
def baseEnd_271169 : Nat := 123768920532582029991487

theorem tailTrace_271169 : CollatzResearch.WordTrace tailWord_271169 prefixEnd_271169 123768920532582029991487 := by
  unfold tailWord_271169
  simp only [CollatzResearch.WordTrace]
  refine ⟨9890345954608499823224561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6593563969738999882149707 9890345954608499823224561)
  ·
    refine ⟨7417759465956374867418421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9890345954608499823224561 7417759465956374867418421)
    ·
      refine ⟨695414949933410143820477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 7417759465956374867418421 695414949933410143820477)
      ·
        refine ⟨260780606225028803932679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 695414949933410143820477 260780606225028803932679)
        ·
          refine ⟨391170909337543205899019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 260780606225028803932679 391170909337543205899019)
          ·
            refine ⟨586756364006314808848529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 391170909337543205899019 586756364006314808848529)
            ·
              refine ⟨440067273004736106636397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 586756364006314808848529 440067273004736106636397)
              ·
                refine ⟨165025227376776039988649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 440067273004736106636397 165025227376776039988649)
                ·
                  refine ⟨123768920532582029991487, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 165025227376776039988649 123768920532582029991487)
                  ·
                    rfl

theorem cell20_271169_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 3, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 3, 1, 1, 2, 3, 2].length) (baseStart_271169 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_271169 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_271169 prefixEnd_271169 := by exact prefixLift 271169
  have htrace : WordTrace (prefixWord ++ tailWord_271169) baseStart_271169 baseEnd_271169 := by
    simpa [prefixWord, tailWord_271169, baseEnd_271169] using wordTrace_append hprefix tailTrace_271169
  have hstable : (prefixWord ++ tailWord_271169).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_271169).length < 2 ^ (prefixWord ++ tailWord_271169).sum := by decide
  have hdescent : baseEnd_271169 < baseStart_271169 := by decide
  rcases family_descends (prefixWord ++ tailWord_271169) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_271194 : List Nat := [3, 1, 1, 2, 1, 5, 2, 1, 4]
def baseStart_271194 : Nat := 118140960795 + 271194 * 2 ^ 59
def prefixEnd_271194 : Nat := 4983230072969 + 3 ^ 40 * 271194 * 2
def baseEnd_271194 : Nat := 123780331213793054158051

theorem tailTrace_271194 : CollatzResearch.WordTrace tailWord_271194 prefixEnd_271194 123780331213793054158051 := by
  unfold tailWord_271194
  simp only [CollatzResearch.WordTrace]
  refine ⟨2472814444879482273221159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6594171853011952728589757 2472814444879482273221159)
  ·
    refine ⟨3709221667319223409831739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2472814444879482273221159 3709221667319223409831739)
    ·
      refine ⟨5563832500978835114747609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3709221667319223409831739 5563832500978835114747609)
      ·
        refine ⟨4172874375734126336060707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5563832500978835114747609 4172874375734126336060707)
        ·
          refine ⟨6259311563601189504091061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4172874375734126336060707 6259311563601189504091061)
          ·
            refine ⟨586810459087611516008537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 6259311563601189504091061 586810459087611516008537)
            ·
              refine ⟨440107844315708637006403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 586810459087611516008537 440107844315708637006403)
              ·
                refine ⟨660161766473562955509605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 440107844315708637006403 660161766473562955509605)
                ·
                  refine ⟨123780331213793054158051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 660161766473562955509605 123780331213793054158051)
                  ·
                    rfl

theorem cell20_271194_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 5, 2, 1, 4].length) (baseStart_271194 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_271194 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_271194 prefixEnd_271194 := by exact prefixLift 271194
  have htrace : WordTrace (prefixWord ++ tailWord_271194) baseStart_271194 baseEnd_271194 := by
    simpa [prefixWord, tailWord_271194, baseEnd_271194] using wordTrace_append hprefix tailTrace_271194
  have hstable : (prefixWord ++ tailWord_271194).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_271194).length < 2 ^ (prefixWord ++ tailWord_271194).sum := by decide
  have hdescent : baseEnd_271194 < baseStart_271194 := by decide
  rcases family_descends (prefixWord ++ tailWord_271194) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_271204 : List Nat := [2, 3, 1, 1, 4, 2, 3, 1, 3]
def baseStart_271204 : Nat := 118140960795 + 271204 * 2 ^ 59
def prefixEnd_271204 : Nat := 4983230072969 + 3 ^ 40 * 271204 * 2
def baseEnd_271204 : Nat := 123784895486277463824677

theorem tailTrace_271204 : CollatzResearch.WordTrace tailWord_271204 prefixEnd_271204 123784895486277463824677 := by
  unfold tailWord_271204
  simp only [CollatzResearch.WordTrace]
  refine ⟨4945811254740850400374333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6594415006321133867165777 4945811254740850400374333)
  ·
    refine ⟨1854679220527818900140375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4945811254740850400374333 1854679220527818900140375)
    ·
      refine ⟨2782018830791728350210563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1854679220527818900140375 2782018830791728350210563)
      ·
        refine ⟨4173028246187592525315845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2782018830791728350210563 4173028246187592525315845)
        ·
          refine ⟨782442796160173598496721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4173028246187592525315845 782442796160173598496721)
          ·
            refine ⟨586832097120130198872541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 782442796160173598496721 586832097120130198872541)
            ·
              refine ⟨220062036420048824577203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 586832097120130198872541 220062036420048824577203)
              ·
                refine ⟨330093054630073236865805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 220062036420048824577203 330093054630073236865805)
                ·
                  refine ⟨123784895486277463824677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 330093054630073236865805 123784895486277463824677)
                  ·
                    rfl

theorem cell20_271204_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 2, 3, 1, 3].length) (baseStart_271204 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_271204 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_271204 prefixEnd_271204 := by exact prefixLift 271204
  have htrace : WordTrace (prefixWord ++ tailWord_271204) baseStart_271204 baseEnd_271204 := by
    simpa [prefixWord, tailWord_271204, baseEnd_271204] using wordTrace_append hprefix tailTrace_271204
  have hstable : (prefixWord ++ tailWord_271204).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_271204).length < 2 ^ (prefixWord ++ tailWord_271204).sum := by decide
  have hdescent : baseEnd_271204 < baseStart_271204 := by decide
  rcases family_descends (prefixWord ++ tailWord_271204) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_271214 : List Nat := [4, 1, 2, 3, 3, 1, 2, 4]
def baseStart_271214 : Nat := 118140960795 + 271214 * 2 ^ 59
def prefixEnd_271214 : Nat := 4983230072969 + 3 ^ 40 * 271214 * 2
def baseEnd_271214 : Nat := 41263153252920624497101

theorem tailTrace_271214 : CollatzResearch.WordTrace tailWord_271214 prefixEnd_271214 41263153252920624497101 := by
  unfold tailWord_271214
  simp only [CollatzResearch.WordTrace]
  refine ⟨1236498404930684063576587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 6594658159630315005741797 1236498404930684063576587)
  ·
    refine ⟨1854747607396026095364881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1236498404930684063576587 1854747607396026095364881)
    ·
      refine ⟨1391060705547019571523661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1854747607396026095364881 1391060705547019571523661)
      ·
        refine ⟨521647764580132339321373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1391060705547019571523661 521647764580132339321373)
        ·
          refine ⟨195617911717549627245515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 521647764580132339321373 195617911717549627245515)
          ·
            refine ⟨293426867576324440868273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 195617911717549627245515 293426867576324440868273)
            ·
              refine ⟨220070150682243330651205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 293426867576324440868273 220070150682243330651205)
              ·
                refine ⟨41263153252920624497101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 220070150682243330651205 41263153252920624497101)
                ·
                  rfl

theorem cell20_271214_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 3, 1, 2, 4].length) (baseStart_271214 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_271214 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_271214 prefixEnd_271214 := by exact prefixLift 271214
  have htrace : WordTrace (prefixWord ++ tailWord_271214) baseStart_271214 baseEnd_271214 := by
    simpa [prefixWord, tailWord_271214, baseEnd_271214] using wordTrace_append hprefix tailTrace_271214
  have hstable : (prefixWord ++ tailWord_271214).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_271214).length < 2 ^ (prefixWord ++ tailWord_271214).sum := by decide
  have hdescent : baseEnd_271214 < baseStart_271214 := by decide
  rcases family_descends (prefixWord ++ tailWord_271214) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_271232 : List Nat := [2, 1, 1, 2, 1, 2, 2, 7, 2]
def baseStart_271232 : Nat := 118140960795 + 271232 * 2 ^ 59
def prefixEnd_271232 : Nat := 4983230072969 + 3 ^ 40 * 271232 * 2
def baseEnd_271232 : Nat := 123797675449233810891229

theorem tailTrace_271232 : CollatzResearch.WordTrace tailWord_271232 prefixEnd_271232 123797675449233810891229 := by
  unfold tailWord_271232
  simp only [CollatzResearch.WordTrace]
  refine ⟨4946321876690130791383975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6595095835586841055178633 4946321876690130791383975)
  ·
    refine ⟨7419482815035196187075963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4946321876690130791383975 7419482815035196187075963)
    ·
      refine ⟨11129224222552794280613945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7419482815035196187075963 11129224222552794280613945)
      ·
        refine ⟨8346918166914595710460459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11129224222552794280613945 8346918166914595710460459)
        ·
          refine ⟨12520377250371893565690689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8346918166914595710460459 12520377250371893565690689)
          ·
            refine ⟨9390282937778920174268017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12520377250371893565690689 9390282937778920174268017)
            ·
              refine ⟨7042712203334190130701013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9390282937778920174268017 7042712203334190130701013)
              ·
                refine ⟨165063567265645081188305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 7042712203334190130701013 165063567265645081188305)
                ·
                  refine ⟨123797675449233810891229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 165063567265645081188305 123797675449233810891229)
                  ·
                    rfl

theorem cell20_271232_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 2, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 2, 7, 2].length) (baseStart_271232 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_271232 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_271232 prefixEnd_271232 := by exact prefixLift 271232
  have htrace : WordTrace (prefixWord ++ tailWord_271232) baseStart_271232 baseEnd_271232 := by
    simpa [prefixWord, tailWord_271232, baseEnd_271232] using wordTrace_append hprefix tailTrace_271232
  have hstable : (prefixWord ++ tailWord_271232).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_271232).length < 2 ^ (prefixWord ++ tailWord_271232).sum := by decide
  have hdescent : baseEnd_271232 < baseStart_271232 := by decide
  rcases family_descends (prefixWord ++ tailWord_271232) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_271239 : List Nat := [1, 1, 4, 2, 3, 3, 6]
def baseStart_271239 : Nat := 118140960795 + 271239 * 2 ^ 59
def prefixEnd_271239 : Nat := 4983230072969 + 3 ^ 40 * 271239 * 2
def baseEnd_271239 : Nat := 13755652271108099739763

theorem tailTrace_271239 : CollatzResearch.WordTrace tailWord_271239 prefixEnd_271239 13755652271108099739763 := by
  unfold tailWord_271239
  simp only [CollatzResearch.WordTrace]
  refine ⟨9892899064354901778272771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6595266042903267852181847 9892899064354901778272771)
  ·
    refine ⟨14839348596532352667409157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9892899064354901778272771 14839348596532352667409157)
    ·
      refine ⟨2782377861849816125139217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 14839348596532352667409157 2782377861849816125139217)
      ·
        refine ⟨2086783396387362093854413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2782377861849816125139217 2086783396387362093854413)
        ·
          refine ⟨782543773645260785195405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2086783396387362093854413 782543773645260785195405)
          ·
            refine ⟨293453915116972794448277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 782543773645260785195405 293453915116972794448277)
            ·
              refine ⟨13755652271108099739763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 293453915116972794448277 13755652271108099739763)
              ·
                rfl

theorem cell20_271239_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 3, 6].length) (baseStart_271239 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_271239 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_271239 prefixEnd_271239 := by exact prefixLift 271239
  have htrace : WordTrace (prefixWord ++ tailWord_271239) baseStart_271239 baseEnd_271239 := by
    simpa [prefixWord, tailWord_271239, baseEnd_271239] using wordTrace_append hprefix tailTrace_271239
  have hstable : (prefixWord ++ tailWord_271239).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_271239).length < 2 ^ (prefixWord ++ tailWord_271239).sum := by decide
  have hdescent : baseEnd_271239 < baseStart_271239 := by decide
  rcases family_descends (prefixWord ++ tailWord_271239) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_271263 : List Nat := [1, 1, 2, 5, 2, 2, 1, 3, 3]
def baseStart_271263 : Nat := 118140960795 + 271263 * 2 ^ 59
def prefixEnd_271263 : Nat := 4983230072969 + 3 ^ 40 * 271263 * 2
def baseEnd_271263 : Nat := 123811824693935480857769

theorem tailTrace_271263 : CollatzResearch.WordTrace tailWord_271263 prefixEnd_271263 123811824693935480857769 := by
  unfold tailWord_271263
  simp only [CollatzResearch.WordTrace]
  refine ⟨9893774416267953877146443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6595849610845302584764295 9893774416267953877146443)
  ·
    refine ⟨14840661624401930815719665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9893774416267953877146443 14840661624401930815719665)
    ·
      refine ⟨11130496218301448111789749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14840661624401930815719665 11130496218301448111789749)
      ·
        refine ⟨1043484020465760760480289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 11130496218301448111789749 1043484020465760760480289)
        ·
          refine ⟨782613015349320570360217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1043484020465760760480289 782613015349320570360217)
          ·
            refine ⟨586959761511990427770163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 782613015349320570360217 586959761511990427770163)
            ·
              refine ⟨880439642267985641655245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 586959761511990427770163 880439642267985641655245)
              ·
                refine ⟨330164865850494615620717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 880439642267985641655245 330164865850494615620717)
                ·
                  refine ⟨123811824693935480857769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 330164865850494615620717 123811824693935480857769)
                  ·
                    rfl

theorem cell20_271263_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 2, 1, 3, 3].length) (baseStart_271263 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_271263 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_271263 prefixEnd_271263 := by exact prefixLift 271263
  have htrace : WordTrace (prefixWord ++ tailWord_271263) baseStart_271263 baseEnd_271263 := by
    simpa [prefixWord, tailWord_271263, baseEnd_271263] using wordTrace_append hprefix tailTrace_271263
  have hstable : (prefixWord ++ tailWord_271263).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_271263).length < 2 ^ (prefixWord ++ tailWord_271263).sum := by decide
  have hdescent : baseEnd_271263 < baseStart_271263 := by decide
  rcases family_descends (prefixWord ++ tailWord_271263) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_271300 : List Nat := [2, 3, 3, 3, 1, 2, 2, 2, 2]
def baseStart_271300 : Nat := 118140960795 + 271300 * 2 ^ 59
def prefixEnd_271300 : Nat := 4983230072969 + 3 ^ 40 * 271300 * 2
def baseEnd_271300 : Nat := 123828712502127796624285

theorem tailTrace_271300 : CollatzResearch.WordTrace tailWord_271300 prefixEnd_271300 123828712502127796624285 := by
  unfold tailWord_271300
  simp only [CollatzResearch.WordTrace]
  refine ⟨4947561958566954598121677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6596749278089272797495569 4947561958566954598121677)
  ·
    refine ⟨1855335734462607974295629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4947561958566954598121677 1855335734462607974295629)
    ·
      refine ⟨695750900423477990360861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1855335734462607974295629 695750900423477990360861)
      ·
        refine ⟨260906587658804246385323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 695750900423477990360861 260906587658804246385323)
        ·
          refine ⟨391359881488206369577985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 260906587658804246385323 391359881488206369577985)
          ·
            refine ⟨293519911116154777183489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 391359881488206369577985 293519911116154777183489)
            ·
              refine ⟨220139933337116082887617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 293519911116154777183489 220139933337116082887617)
              ·
                refine ⟨165104950002837062165713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 220139933337116082887617 165104950002837062165713)
                ·
                  refine ⟨123828712502127796624285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 165104950002837062165713 123828712502127796624285)
                  ·
                    rfl

theorem cell20_271300_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 3, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 3, 1, 2, 2, 2, 2].length) (baseStart_271300 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_271300 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_271300 prefixEnd_271300 := by exact prefixLift 271300
  have htrace : WordTrace (prefixWord ++ tailWord_271300) baseStart_271300 baseEnd_271300 := by
    simpa [prefixWord, tailWord_271300, baseEnd_271300] using wordTrace_append hprefix tailTrace_271300
  have hstable : (prefixWord ++ tailWord_271300).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_271300).length < 2 ^ (prefixWord ++ tailWord_271300).sum := by decide
  have hdescent : baseEnd_271300 < baseStart_271300 := by decide
  rcases family_descends (prefixWord ++ tailWord_271300) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_271318 : List Nat := [5, 2, 1, 1, 2, 1, 2, 3, 3]
def baseStart_271318 : Nat := 118140960795 + 271318 * 2 ^ 59
def prefixEnd_271318 : Nat := 4983230072969 + 3 ^ 40 * 271318 * 2
def baseEnd_271318 : Nat := 123836928192599734024211

theorem tailTrace_271318 : CollatzResearch.WordTrace tailWord_271318 prefixEnd_271318 123836928192599734024211 := by
  unfold tailWord_271318
  simp only [CollatzResearch.WordTrace]
  refine ⟨618486276941793641899913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 6597186954045798846932405 618486276941793641899913)
  ·
    refine ⟨463864707706345231424935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 618486276941793641899913 463864707706345231424935)
    ·
      refine ⟨695797061559517847137403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 463864707706345231424935 695797061559517847137403)
      ·
        refine ⟨1043695592339276770706105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 695797061559517847137403 1043695592339276770706105)
        ·
          refine ⟨782771694254457578029579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1043695592339276770706105 782771694254457578029579)
          ·
            refine ⟨1174157541381686367044369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 782771694254457578029579 1174157541381686367044369)
            ·
              refine ⟨880618156036264775283277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1174157541381686367044369 880618156036264775283277)
              ·
                refine ⟨330231808513599290731229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 880618156036264775283277 330231808513599290731229)
                ·
                  refine ⟨123836928192599734024211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 330231808513599290731229 123836928192599734024211)
                  ·
                    rfl

theorem cell20_271318_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 1, 2, 3, 3].length) (baseStart_271318 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_271318 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_271318 prefixEnd_271318 := by exact prefixLift 271318
  have htrace : WordTrace (prefixWord ++ tailWord_271318) baseStart_271318 baseEnd_271318 := by
    simpa [prefixWord, tailWord_271318, baseEnd_271318] using wordTrace_append hprefix tailTrace_271318
  have hstable : (prefixWord ++ tailWord_271318).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_271318).length < 2 ^ (prefixWord ++ tailWord_271318).sum := by decide
  have hdescent : baseEnd_271318 < baseStart_271318 := by decide
  rcases family_descends (prefixWord ++ tailWord_271318) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_271336 : List Nat := [2, 1, 4, 1, 1, 1, 2, 8]
def baseStart_271336 : Nat := 118140960795 + 271336 * 2 ^ 59
def prefixEnd_271336 : Nat := 4983230072969 + 3 ^ 40 * 271336 * 2
def baseEnd_271336 : Nat := 41281714627690557141379

theorem tailTrace_271336 : CollatzResearch.WordTrace tailWord_271336 prefixEnd_271336 41281714627690557141379 := by
  unfold tailWord_271336
  simp only [CollatzResearch.WordTrace]
  refine ⟨4948218472501743672276931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6597624630002324896369241 4948218472501743672276931)
  ·
    refine ⟨7422327708752615508415397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4948218472501743672276931 7422327708752615508415397)
    ·
      refine ⟨1391686445391115407827887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 7422327708752615508415397 1391686445391115407827887)
      ·
        refine ⟨2087529668086673111741831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1391686445391115407827887 2087529668086673111741831)
        ·
          refine ⟨3131294502130009667612747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2087529668086673111741831 3131294502130009667612747)
          ·
            refine ⟨4696941753195014501419121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3131294502130009667612747 4696941753195014501419121)
            ·
              refine ⟨3522706314896260876064341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4696941753195014501419121 3522706314896260876064341)
              ·
                refine ⟨41281714627690557141379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 3522706314896260876064341 41281714627690557141379)
                ·
                  rfl

theorem cell20_271336_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 2, 8].length) (baseStart_271336 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_271336 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_271336 prefixEnd_271336 := by exact prefixLift 271336
  have htrace : WordTrace (prefixWord ++ tailWord_271336) baseStart_271336 baseEnd_271336 := by
    simpa [prefixWord, tailWord_271336, baseEnd_271336] using wordTrace_append hprefix tailTrace_271336
  have hstable : (prefixWord ++ tailWord_271336).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_271336).length < 2 ^ (prefixWord ++ tailWord_271336).sum := by decide
  have hdescent : baseEnd_271336 < baseStart_271336 := by decide
  rcases family_descends (prefixWord ++ tailWord_271336) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_271342 : List Nat := [4, 1, 2, 1, 4, 1, 2, 3, 2]
def baseStart_271342 : Nat := 118140960795 + 271342 * 2 ^ 59
def prefixEnd_271342 : Nat := 4983230072969 + 3 ^ 40 * 271342 * 2
def baseEnd_271342 : Nat := 123847882446562317224113

theorem tailTrace_271342 : CollatzResearch.WordTrace tailWord_271342 prefixEnd_271342 123847882446562317224113 := by
  unfold tailWord_271342
  simp only [CollatzResearch.WordTrace]
  refine ⟨1237081972872718796159035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 6597770521987833579514853 1237081972872718796159035)
  ·
    refine ⟨1855622959309078194238553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1237081972872718796159035 1855622959309078194238553)
    ·
      refine ⟨1391717219481808645678915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1855622959309078194238553 1391717219481808645678915)
      ·
        refine ⟨2087575829222712968518373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1391717219481808645678915 2087575829222712968518373)
        ·
          refine ⟨391420467979258681597195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2087575829222712968518373 391420467979258681597195)
          ·
            refine ⟨587130701968888022395793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 391420467979258681597195 587130701968888022395793)
            ·
              refine ⟨440348026476666016796845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 587130701968888022395793 440348026476666016796845)
              ·
                refine ⟨165130509928749756298817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 440348026476666016796845 165130509928749756298817)
                ·
                  refine ⟨123847882446562317224113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 165130509928749756298817 123847882446562317224113)
                  ·
                    rfl

theorem cell20_271342_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 4, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 4, 1, 2, 3, 2].length) (baseStart_271342 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_271342 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_271342 prefixEnd_271342 := by exact prefixLift 271342
  have htrace : WordTrace (prefixWord ++ tailWord_271342) baseStart_271342 baseEnd_271342 := by
    simpa [prefixWord, tailWord_271342, baseEnd_271342] using wordTrace_append hprefix tailTrace_271342
  have hstable : (prefixWord ++ tailWord_271342).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_271342).length < 2 ^ (prefixWord ++ tailWord_271342).sum := by decide
  have hdescent : baseEnd_271342 < baseStart_271342 := by decide
  rcases family_descends (prefixWord ++ tailWord_271342) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_271348 : List Nat := [2, 6, 2, 1, 2, 1, 1, 2, 3]
def baseStart_271348 : Nat := 118140960795 + 271348 * 2 ^ 59
def prefixEnd_271348 : Nat := 4983230072969 + 3 ^ 40 * 271348 * 2
def baseEnd_271348 : Nat := 123850621010052963024089

theorem tailTrace_271348 : CollatzResearch.WordTrace tailWord_271348 prefixEnd_271348 123850621010052963024089 := by
  unfold tailWord_271348
  simp only [CollatzResearch.WordTrace]
  refine ⟨4948437310480006696995349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6597916413973342262660465 4948437310480006696995349)
  ·
    refine ⟨231957998928750313921657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 4948437310480006696995349 231957998928750313921657)
    ·
      refine ⟨173968499196562735441243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 231957998928750313921657 173968499196562735441243)
      ·
        refine ⟨260952748794844103161865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 173968499196562735441243 260952748794844103161865)
        ·
          refine ⟨195714561596133077371399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 260952748794844103161865 195714561596133077371399)
          ·
            refine ⟨293571842394199616057099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 195714561596133077371399 293571842394199616057099)
            ·
              refine ⟨440357763591299424085649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 293571842394199616057099 440357763591299424085649)
              ·
                refine ⟨330268322693474568064237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 440357763591299424085649 330268322693474568064237)
                ·
                  refine ⟨123850621010052963024089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 330268322693474568064237 123850621010052963024089)
                  ·
                    rfl

theorem cell20_271348_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 2, 1, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 2, 1, 2, 1, 1, 2, 3].length) (baseStart_271348 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_271348 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_271348 prefixEnd_271348 := by exact prefixLift 271348
  have htrace : WordTrace (prefixWord ++ tailWord_271348) baseStart_271348 baseEnd_271348 := by
    simpa [prefixWord, tailWord_271348, baseEnd_271348] using wordTrace_append hprefix tailTrace_271348
  have hstable : (prefixWord ++ tailWord_271348).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_271348).length < 2 ^ (prefixWord ++ tailWord_271348).sum := by decide
  have hdescent : baseEnd_271348 < baseStart_271348 := by decide
  rcases family_descends (prefixWord ++ tailWord_271348) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_271391 : List Nat := [1, 1, 2, 4, 1, 3, 4, 4]
def baseStart_271391 : Nat := 118140960795 + 271391 * 2 ^ 59
def prefixEnd_271391 : Nat := 4983230072969 + 3 ^ 40 * 271391 * 2
def baseEnd_271391 : Nat := 41290082460578641530193

theorem tailTrace_271391 : CollatzResearch.WordTrace tailWord_271391 prefixEnd_271391 41290082460578641530193 := by
  unfold tailWord_271391
  simp only [CollatzResearch.WordTrace]
  refine ⟨9898442959804231737806027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6598961973202821158537351 9898442959804231737806027)
  ·
    refine ⟨14847664439706347606709041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9898442959804231737806027 14847664439706347606709041)
    ·
      refine ⟨11135748329779760705031781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14847664439706347606709041 11135748329779760705031781)
      ·
        refine ⟨2087952811833705132193459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 11135748329779760705031781 2087952811833705132193459)
        ·
          refine ⟨3131929217750557698290189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2087952811833705132193459 3131929217750557698290189)
          ·
            refine ⟨1174473456656459136858821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3131929217750557698290189 1174473456656459136858821)
            ·
              refine ⟨220213773123086088161029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1174473456656459136858821 220213773123086088161029)
              ·
                refine ⟨41290082460578641530193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 220213773123086088161029 41290082460578641530193)
                ·
                  rfl

theorem cell20_271391_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 3, 4, 4].length) (baseStart_271391 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_271391 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_271391 prefixEnd_271391 := by exact prefixLift 271391
  have htrace : WordTrace (prefixWord ++ tailWord_271391) baseStart_271391 baseEnd_271391 := by
    simpa [prefixWord, tailWord_271391, baseEnd_271391] using wordTrace_append hprefix tailTrace_271391
  have hstable : (prefixWord ++ tailWord_271391).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_271391).length < 2 ^ (prefixWord ++ tailWord_271391).sum := by decide
  have hdescent : baseEnd_271391 < baseStart_271391 := by decide
  rcases family_descends (prefixWord ++ tailWord_271391) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_271457 : List Nat := [1, 2, 3, 1, 1, 2, 2, 1, 7]
def baseStart_271457 : Nat := 118140960795 + 271457 * 2 ^ 59
def prefixEnd_271457 : Nat := 4983230072969 + 3 ^ 40 * 271457 * 2
def baseEnd_271457 : Nat := 123900371580133028390309

theorem tailTrace_271457 : CollatzResearch.WordTrace tailWord_271457 prefixEnd_271457 123900371580133028390309 := by
  unfold tailWord_271457
  simp only [CollatzResearch.WordTrace]
  refine ⟨9900850177565125009708625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6600566785043416673139083 9900850177565125009708625)
  ·
    refine ⟨7425637633173843757281469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9900850177565125009708625 7425637633173843757281469)
    ·
      refine ⟨2784614112440191408980551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7425637633173843757281469 2784614112440191408980551)
      ·
        refine ⟨4176921168660287113470827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2784614112440191408980551 4176921168660287113470827)
        ·
          refine ⟨6265381752990430670206241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4176921168660287113470827 6265381752990430670206241)
          ·
            refine ⟨4699036314742823002654681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6265381752990430670206241 4699036314742823002654681)
            ·
              refine ⟨3524277236057117251991011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4699036314742823002654681 3524277236057117251991011)
              ·
                refine ⟨5286415854085675877986517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3524277236057117251991011 5286415854085675877986517)
                ·
                  refine ⟨123900371580133028390309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 5286415854085675877986517 123900371580133028390309)
                  ·
                    rfl

theorem cell20_271457_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 2, 1, 7].length) (baseStart_271457 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_271457 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_271457 prefixEnd_271457 := by exact prefixLift 271457
  have htrace : WordTrace (prefixWord ++ tailWord_271457) baseStart_271457 baseEnd_271457 := by
    simpa [prefixWord, tailWord_271457, baseEnd_271457] using wordTrace_append hprefix tailTrace_271457
  have hstable : (prefixWord ++ tailWord_271457).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_271457).length < 2 ^ (prefixWord ++ tailWord_271457).sum := by decide
  have hdescent : baseEnd_271457 < baseStart_271457 := by decide
  rcases family_descends (prefixWord ++ tailWord_271457) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_271460 : List Nat := [2, 3, 1, 1, 2, 1, 1, 7, 2]
def baseStart_271460 : Nat := 118140960795 + 271460 * 2 ^ 59
def prefixEnd_271460 : Nat := 4983230072969 + 3 ^ 40 * 271460 * 2
def baseEnd_271460 : Nat := 123901740861878351290297

theorem tailTrace_271460 : CollatzResearch.WordTrace tailWord_271460 prefixEnd_271460 123901740861878351290297 := by
  unfold tailWord_271460
  simp only [CollatzResearch.WordTrace]
  refine ⟨4950479798277128261033917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6600639731036171014711889 4950479798277128261033917)
  ·
    refine ⟨1856429924353923097887719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4950479798277128261033917 1856429924353923097887719)
    ·
      refine ⟨2784644886530884646831579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1856429924353923097887719 2784644886530884646831579)
      ·
        refine ⟨4176967329796326970247369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2784644886530884646831579 4176967329796326970247369)
        ·
          refine ⟨3132725497347245227685527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4176967329796326970247369 3132725497347245227685527)
          ·
            refine ⟨4699088246020867841528291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3132725497347245227685527 4699088246020867841528291)
            ·
              refine ⟨7048632369031301762292437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4699088246020867841528291 7048632369031301762292437)
              ·
                refine ⟨165202321149171135053729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 7048632369031301762292437 165202321149171135053729)
                ·
                  refine ⟨123901740861878351290297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 165202321149171135053729 123901740861878351290297)
                  ·
                    rfl

theorem cell20_271460_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 1, 7, 2].length) (baseStart_271460 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_271460 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_271460 prefixEnd_271460 := by exact prefixLift 271460
  have htrace : WordTrace (prefixWord ++ tailWord_271460) baseStart_271460 baseEnd_271460 := by
    simpa [prefixWord, tailWord_271460, baseEnd_271460] using wordTrace_append hprefix tailTrace_271460
  have hstable : (prefixWord ++ tailWord_271460).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_271460).length < 2 ^ (prefixWord ++ tailWord_271460).sum := by decide
  have hdescent : baseEnd_271460 < baseStart_271460 := by decide
  rcases family_descends (prefixWord ++ tailWord_271460) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_271488 : List Nat := [2, 1, 1, 2, 1, 3, 5, 5]
def baseStart_271488 : Nat := 118140960795 + 271488 * 2 ^ 59
def prefixEnd_271488 : Nat := 4983230072969 + 3 ^ 40 * 271488 * 2
def baseEnd_271488 : Nat := 41304840274944899452283

theorem tailTrace_271488 : CollatzResearch.WordTrace tailWord_271488 prefixEnd_271488 41304840274944899452283 := by
  unfold tailWord_271488
  simp only [CollatzResearch.WordTrace]
  refine ⟨4950990420226408652043559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6601320560301878202724745 4950990420226408652043559)
  ·
    refine ⟨7426485630339612978065339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4950990420226408652043559 7426485630339612978065339)
    ·
      refine ⟨11139728445509419467098009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7426485630339612978065339 11139728445509419467098009)
      ·
        refine ⟨8354796334132064600323507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11139728445509419467098009 8354796334132064600323507)
        ·
          refine ⟨12532194501198096900485261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8354796334132064600323507 12532194501198096900485261)
          ·
            refine ⟨4699572937949286337681973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12532194501198096900485261 4699572937949286337681973)
            ·
              refine ⟨440584962932745594157685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 4699572937949286337681973 440584962932745594157685)
              ·
                refine ⟨41304840274944899452283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 440584962932745594157685 41304840274944899452283)
                ·
                  rfl

theorem cell20_271488_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 5, 5].length) (baseStart_271488 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_271488 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_271488 prefixEnd_271488 := by exact prefixLift 271488
  have htrace : WordTrace (prefixWord ++ tailWord_271488) baseStart_271488 baseEnd_271488 := by
    simpa [prefixWord, tailWord_271488, baseEnd_271488] using wordTrace_append hprefix tailTrace_271488
  have hstable : (prefixWord ++ tailWord_271488).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_271488).length < 2 ^ (prefixWord ++ tailWord_271488).sum := by decide
  have hdescent : baseEnd_271488 < baseStart_271488 := by decide
  rcases family_descends (prefixWord ++ tailWord_271488) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_271495 : List Nat := [1, 1, 4, 2, 1, 1, 1, 2, 7]
def baseStart_271495 : Nat := 118140960795 + 271495 * 2 ^ 59
def prefixEnd_271495 : Nat := 4983230072969 + 3 ^ 40 * 271495 * 2
def baseEnd_271495 : Nat := 123917715815573785123487

theorem tailTrace_271495 : CollatzResearch.WordTrace tailWord_271495 prefixEnd_271495 123917715815573785123487 := by
  unfold tailWord_271495
  simp only [CollatzResearch.WordTrace]
  refine ⟨9902236151427457499591939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6601490767618304999727959 9902236151427457499591939)
  ·
    refine ⟨14853354227141186249387909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9902236151427457499591939 14853354227141186249387909)
    ·
      refine ⟨2785003917588972421760233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 14853354227141186249387909 2785003917588972421760233)
      ·
        refine ⟨2088752938191729316320175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2785003917588972421760233 2088752938191729316320175)
        ·
          refine ⟨3133129407287593974480263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2088752938191729316320175 3133129407287593974480263)
          ·
            refine ⟨4699694110931390961720395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3133129407287593974480263 4699694110931390961720395)
            ·
              refine ⟨7049541166397086442580593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4699694110931390961720395 7049541166397086442580593)
              ·
                refine ⟨5287155874797814831935445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7049541166397086442580593 5287155874797814831935445)
                ·
                  refine ⟨123917715815573785123487, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 5287155874797814831935445 123917715815573785123487)
                  ·
                    rfl

theorem cell20_271495_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 1, 2, 7].length) (baseStart_271495 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_271495 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_271495 prefixEnd_271495 := by exact prefixLift 271495
  have htrace : WordTrace (prefixWord ++ tailWord_271495) baseStart_271495 baseEnd_271495 := by
    simpa [prefixWord, tailWord_271495, baseEnd_271495] using wordTrace_append hprefix tailTrace_271495
  have hstable : (prefixWord ++ tailWord_271495).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_271495).length < 2 ^ (prefixWord ++ tailWord_271495).sum := by decide
  have hdescent : baseEnd_271495 < baseStart_271495 := by decide
  rcases family_descends (prefixWord ++ tailWord_271495) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_271542 : List Nat := [5, 1, 3, 2, 1, 1, 3, 1, 3]
def baseStart_271542 : Nat := 118140960795 + 271542 * 2 ^ 59
def prefixEnd_271542 : Nat := 4983230072969 + 3 ^ 40 * 271542 * 2
def baseEnd_271542 : Nat := 123939167896250510556629

theorem tailTrace_271542 : CollatzResearch.WordTrace tailWord_271542 prefixEnd_271542 123939167896250510556629 := by
  unfold tailWord_271542
  simp only [CollatzResearch.WordTrace]
  refine ⟨618996898891074032909555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 6602633588171456351035253 618996898891074032909555)
  ·
    refine ⟨928495348336611049364333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 618996898891074032909555 928495348336611049364333)
    ·
      refine ⟨348185755626229143511625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 928495348336611049364333 348185755626229143511625)
      ·
        refine ⟨261139316719671857633719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 348185755626229143511625 261139316719671857633719)
        ·
          refine ⟨391708975079507786450579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 261139316719671857633719 391708975079507786450579)
          ·
            refine ⟨587563462619261679675869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 391708975079507786450579 587563462619261679675869)
            ·
              refine ⟨220336298482223129878451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 587563462619261679675869 220336298482223129878451)
              ·
                refine ⟨330504447723334694817677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 220336298482223129878451 330504447723334694817677)
                ·
                  refine ⟨123939167896250510556629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 330504447723334694817677 123939167896250510556629)
                  ·
                    rfl

theorem cell20_271542_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 2, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 2, 1, 1, 3, 1, 3].length) (baseStart_271542 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_271542 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_271542 prefixEnd_271542 := by exact prefixLift 271542
  have htrace : WordTrace (prefixWord ++ tailWord_271542) baseStart_271542 baseEnd_271542 := by
    simpa [prefixWord, tailWord_271542, baseEnd_271542] using wordTrace_append hprefix tailTrace_271542
  have hstable : (prefixWord ++ tailWord_271542).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_271542).length < 2 ^ (prefixWord ++ tailWord_271542).sum := by decide
  have hdescent : baseEnd_271542 < baseStart_271542 := by decide
  rcases family_descends (prefixWord ++ tailWord_271542) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_271591 : List Nat := [1, 1, 5, 3, 2, 2, 1, 1, 4]
def baseStart_271591 : Nat := 118140960795 + 271591 * 2 ^ 59
def prefixEnd_271591 : Nat := 4983230072969 + 3 ^ 40 * 271591 * 2
def baseEnd_271591 : Nat := 123961532831424117923095

theorem tailTrace_271591 : CollatzResearch.WordTrace tailWord_271591 prefixEnd_271591 123961532831424117923095 := by
  unfold tailWord_271591
  simp only [CollatzResearch.WordTrace]
  refine ⟨9905737559079665895086627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6603825039386443930057751 9905737559079665895086627)
  ·
    refine ⟨14858606338619498842629941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9905737559079665895086627 14858606338619498842629941)
    ·
      refine ⟨1392994344245578016496557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 14858606338619498842629941 1392994344245578016496557)
      ·
        refine ⟨522372879092091756186209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1392994344245578016496557 522372879092091756186209)
        ·
          refine ⟨391779659319068817139657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 522372879092091756186209 391779659319068817139657)
          ·
            refine ⟨293834744489301612854743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 391779659319068817139657 293834744489301612854743)
            ·
              refine ⟨440752116733952419282115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 293834744489301612854743 440752116733952419282115)
              ·
                refine ⟨661128175100928628923173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 440752116733952419282115 661128175100928628923173)
                ·
                  refine ⟨123961532831424117923095, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 661128175100928628923173 123961532831424117923095)
                  ·
                    rfl

theorem cell20_271591_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 2, 2, 1, 1, 4].length) (baseStart_271591 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_271591 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_271591 prefixEnd_271591 := by exact prefixLift 271591
  have htrace : WordTrace (prefixWord ++ tailWord_271591) baseStart_271591 baseEnd_271591 := by
    simpa [prefixWord, tailWord_271591, baseEnd_271591] using wordTrace_append hprefix tailTrace_271591
  have hstable : (prefixWord ++ tailWord_271591).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_271591).length < 2 ^ (prefixWord ++ tailWord_271591).sum := by decide
  have hdescent : baseEnd_271591 < baseStart_271591 := by decide
  rcases family_descends (prefixWord ++ tailWord_271591) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_271595 : List Nat := [1, 1, 1, 1, 2, 6, 3, 1, 4]
def baseStart_271595 : Nat := 118140960795 + 271595 * 2 ^ 59
def prefixEnd_271595 : Nat := 4983230072969 + 3 ^ 40 * 271595 * 2
def baseEnd_271595 : Nat := 123963358540417881789745

theorem tailTrace_271595 : CollatzResearch.WordTrace tailWord_271595 prefixEnd_271595 123963358540417881789745 := by
  unfold tailWord_271595
  simp only [CollatzResearch.WordTrace]
  refine ⟨9905883451065174578232239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6603922300710116385488159 9905883451065174578232239)
  ·
    refine ⟨14858825176597761867348359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9905883451065174578232239 14858825176597761867348359)
    ·
      refine ⟨22288237764896642801022539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14858825176597761867348359 22288237764896642801022539)
      ·
        refine ⟨33432356647344964201533809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22288237764896642801022539 33432356647344964201533809)
        ·
          refine ⟨25074267485508723151150357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33432356647344964201533809 25074267485508723151150357)
          ·
            refine ⟨1175356288383221397710173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 25074267485508723151150357 1175356288383221397710173)
            ·
              refine ⟨440758608143708024141315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1175356288383221397710173 440758608143708024141315)
              ·
                refine ⟨661137912215562036211973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 440758608143708024141315 661137912215562036211973)
                ·
                  refine ⟨123963358540417881789745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 661137912215562036211973 123963358540417881789745)
                  ·
                    rfl

theorem cell20_271595_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 6, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 6, 3, 1, 4].length) (baseStart_271595 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_271595 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_271595 prefixEnd_271595 := by exact prefixLift 271595
  have htrace : WordTrace (prefixWord ++ tailWord_271595) baseStart_271595 baseEnd_271595 := by
    simpa [prefixWord, tailWord_271595, baseEnd_271595] using wordTrace_append hprefix tailTrace_271595
  have hstable : (prefixWord ++ tailWord_271595).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_271595).length < 2 ^ (prefixWord ++ tailWord_271595).sum := by decide
  have hdescent : baseEnd_271595 < baseStart_271595 := by decide
  rcases family_descends (prefixWord ++ tailWord_271595) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_271616 : List Nat := [2, 1, 1, 2, 1, 1, 3, 3, 6]
def baseStart_271616 : Nat := 118140960795 + 271616 * 2 ^ 59
def prefixEnd_271616 : Nat := 4983230072969 + 3 ^ 40 * 271616 * 2
def baseEnd_271616 : Nat := 123972943512635142089659

theorem tailTrace_271616 : CollatzResearch.WordTrace tailWord_271616 prefixEnd_271616 123972943512635142089659 := by
  unfold tailWord_271616
  simp only [CollatzResearch.WordTrace]
  refine ⟨4953324691994547582373351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6604432922659396776497801 4953324691994547582373351)
  ·
    refine ⟨7429987037991821373560027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4953324691994547582373351 7429987037991821373560027)
    ·
      refine ⟨11144980556987732060340041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7429987037991821373560027 11144980556987732060340041)
      ·
        refine ⟨8358735417740799045255031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11144980556987732060340041 8358735417740799045255031)
        ·
          refine ⟨12538103126611198567882547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8358735417740799045255031 12538103126611198567882547)
          ·
            refine ⟨18807154689916797851823821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12538103126611198567882547 18807154689916797851823821)
            ·
              refine ⟨7052683008718799194433933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18807154689916797851823821 7052683008718799194433933)
              ·
                refine ⟨2644756128269549697912725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7052683008718799194433933 2644756128269549697912725)
                ·
                  refine ⟨123972943512635142089659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2644756128269549697912725 123972943512635142089659)
                  ·
                    rfl

theorem cell20_271616_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 3, 3, 6].length) (baseStart_271616 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_271616 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_271616 prefixEnd_271616 := by exact prefixLift 271616
  have htrace : WordTrace (prefixWord ++ tailWord_271616) baseStart_271616 baseEnd_271616 := by
    simpa [prefixWord, tailWord_271616, baseEnd_271616] using wordTrace_append hprefix tailTrace_271616
  have hstable : (prefixWord ++ tailWord_271616).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_271616).length < 2 ^ (prefixWord ++ tailWord_271616).sum := by decide
  have hdescent : baseEnd_271616 < baseStart_271616 := by decide
  rcases family_descends (prefixWord ++ tailWord_271616) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_271684 : List Nat := [2, 3, 4, 1, 1, 2, 2, 3, 2]
def baseStart_271684 : Nat := 118140960795 + 271684 * 2 ^ 59
def prefixEnd_271684 : Nat := 4983230072969 + 3 ^ 40 * 271684 * 2
def baseEnd_271684 : Nat := 124003980565529127822715

theorem tailTrace_271684 : CollatzResearch.WordTrace tailWord_271684 prefixEnd_271684 124003980565529127822715 := by
  unfold tailWord_271684
  simp only [CollatzResearch.WordTrace]
  refine ⟨4954564773871371389111053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6606086365161828518814737 4954564773871371389111053)
  ·
    refine ⟨1857961790201764270916645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4954564773871371389111053 1857961790201764270916645)
    ·
      refine ⟨348367835662830800796871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1857961790201764270916645 348367835662830800796871)
      ·
        refine ⟨522551753494246201195307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 348367835662830800796871 522551753494246201195307)
        ·
          refine ⟨783827630241369301792961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 522551753494246201195307 783827630241369301792961)
          ·
            refine ⟨587870722681026976344721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 783827630241369301792961 587870722681026976344721)
            ·
              refine ⟨440903042010770232258541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 587870722681026976344721 440903042010770232258541)
              ·
                refine ⟨165338640754038837096953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 440903042010770232258541 165338640754038837096953)
                ·
                  refine ⟨124003980565529127822715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 165338640754038837096953 124003980565529127822715)
                  ·
                    rfl

theorem cell20_271684_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 2, 2, 3, 2].length) (baseStart_271684 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_271684 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_271684 prefixEnd_271684 := by exact prefixLift 271684
  have htrace : WordTrace (prefixWord ++ tailWord_271684) baseStart_271684 baseEnd_271684 := by
    simpa [prefixWord, tailWord_271684, baseEnd_271684] using wordTrace_append hprefix tailTrace_271684
  have hstable : (prefixWord ++ tailWord_271684).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_271684).length < 2 ^ (prefixWord ++ tailWord_271684).sum := by decide
  have hdescent : baseEnd_271684 < baseStart_271684 := by decide
  rcases family_descends (prefixWord ++ tailWord_271684) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_271699 : List Nat := [1, 1, 1, 2, 1, 1, 13]
def baseStart_271699 : Nat := 118140960795 + 271699 * 2 ^ 59
def prefixEnd_271699 : Nat := 4983230072969 + 3 ^ 40 * 271699 * 2
def baseEnd_271699 : Nat := 13778980774917304702517

theorem tailTrace_271699 : CollatzResearch.WordTrace tailWord_271699 prefixEnd_271699 13778980774917304702517 := by
  unfold tailWord_271699
  simp only [CollatzResearch.WordTrace]
  refine ⟨9909676642688400340018151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6606451095125600226678767 9909676642688400340018151)
  ·
    refine ⟨14864514964032600510027227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9909676642688400340018151 14864514964032600510027227)
    ·
      refine ⟨22296772446048900765040841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14864514964032600510027227 22296772446048900765040841)
      ·
        refine ⟨16722579334536675573780631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22296772446048900765040841 16722579334536675573780631)
        ·
          refine ⟨25083869001805013360670947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16722579334536675573780631 25083869001805013360670947)
          ·
            refine ⟨37625803502707520041006421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25083869001805013360670947 37625803502707520041006421)
            ·
              refine ⟨13778980774917304702517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 13 37625803502707520041006421 13778980774917304702517)
              ·
                rfl

theorem cell20_271699_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 13].length) (baseStart_271699 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_271699 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_271699 prefixEnd_271699 := by exact prefixLift 271699
  have htrace : WordTrace (prefixWord ++ tailWord_271699) baseStart_271699 baseEnd_271699 := by
    simpa [prefixWord, tailWord_271699, baseEnd_271699] using wordTrace_append hprefix tailTrace_271699
  have hstable : (prefixWord ++ tailWord_271699).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_271699).length < 2 ^ (prefixWord ++ tailWord_271699).sum := by decide
  have hdescent : baseEnd_271699 < baseStart_271699 := by decide
  rcases family_descends (prefixWord ++ tailWord_271699) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_271733 : List Nat := [1, 3, 4, 1, 3, 1, 1, 6]
def baseStart_271733 : Nat := 118140960795 + 271733 * 2 ^ 59
def prefixEnd_271733 : Nat := 4983230072969 + 3 ^ 40 * 271733 * 2
def baseEnd_271733 : Nat := 41342115166900911729727

theorem tailTrace_271733 : CollatzResearch.WordTrace tailWord_271733 prefixEnd_271733 41342115166900911729727 := by
  unfold tailWord_271733
  simp only [CollatzResearch.WordTrace]
  refine ⟨9910916724565224146755853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6607277816376816097837235 9910916724565224146755853)
  ·
    refine ⟨3716593771711959055033445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9910916724565224146755853 3716593771711959055033445)
    ·
      refine ⟨696861332195992322818771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3716593771711959055033445 696861332195992322818771)
      ·
        refine ⟨1045291998293988484228157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 696861332195992322818771 1045291998293988484228157)
        ·
          refine ⟨391984499360245681585559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1045291998293988484228157 391984499360245681585559)
          ·
            refine ⟨587976749040368522378339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 391984499360245681585559 587976749040368522378339)
            ·
              refine ⟨881965123560552783567509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 587976749040368522378339 881965123560552783567509)
              ·
                refine ⟨41342115166900911729727, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 881965123560552783567509 41342115166900911729727)
                ·
                  rfl

theorem cell20_271733_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 3, 1, 1, 6].length) (baseStart_271733 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_271733 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_271733 prefixEnd_271733 := by exact prefixLift 271733
  have htrace : WordTrace (prefixWord ++ tailWord_271733) baseStart_271733 baseEnd_271733 := by
    simpa [prefixWord, tailWord_271733, baseEnd_271733] using wordTrace_append hprefix tailTrace_271733
  have hstable : (prefixWord ++ tailWord_271733).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_271733).length < 2 ^ (prefixWord ++ tailWord_271733).sum := by decide
  have hdescent : baseEnd_271733 < baseStart_271733 := by decide
  rcases family_descends (prefixWord ++ tailWord_271733) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_271764 : List Nat := [2, 4, 2, 1, 2, 1, 3, 1, 4]
def baseStart_271764 : Nat := 118140960795 + 271764 * 2 ^ 59
def prefixEnd_271764 : Nat := 4983230072969 + 3 ^ 40 * 271764 * 2
def baseEnd_271764 : Nat := 124040494745404405155721

theorem tailTrace_271764 : CollatzResearch.WordTrace tailWord_271764 prefixEnd_271764 124040494745404405155721 := by
  unfold tailWord_271764
  simp only [CollatzResearch.WordTrace]
  refine ⟨4956023693726458220567173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6608031591635277627422897 4956023693726458220567173)
  ·
    refine ⟨929254442573710916356345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 4956023693726458220567173 929254442573710916356345)
    ·
      refine ⟨696940831930283187267259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 929254442573710916356345 696940831930283187267259)
      ·
        refine ⟨1045411247895424780900889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 696940831930283187267259 1045411247895424780900889)
        ·
          refine ⟨784058435921568585675667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1045411247895424780900889 784058435921568585675667)
          ·
            refine ⟨1176087653882352878513501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 784058435921568585675667 1176087653882352878513501)
            ·
              refine ⟨441032870205882329442563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1176087653882352878513501 441032870205882329442563)
              ·
                refine ⟨661549305308823494163845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 441032870205882329442563 661549305308823494163845)
                ·
                  refine ⟨124040494745404405155721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 661549305308823494163845 124040494745404405155721)
                  ·
                    rfl

theorem cell20_271764_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 1, 3, 1, 4].length) (baseStart_271764 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_271764 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_271764 prefixEnd_271764 := by exact prefixLift 271764
  have htrace : WordTrace (prefixWord ++ tailWord_271764) baseStart_271764 baseEnd_271764 := by
    simpa [prefixWord, tailWord_271764, baseEnd_271764] using wordTrace_append hprefix tailTrace_271764
  have hstable : (prefixWord ++ tailWord_271764).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_271764).length < 2 ^ (prefixWord ++ tailWord_271764).sum := by decide
  have hdescent : baseEnd_271764 < baseStart_271764 := by decide
  rcases family_descends (prefixWord ++ tailWord_271764) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_271774 : List Nat := [4, 3, 1, 2, 2, 1, 1, 3, 3]
def baseStart_271774 : Nat := 118140960795 + 271774 * 2 ^ 59
def prefixEnd_271774 : Nat := 4983230072969 + 3 ^ 40 * 271774 * 2
def baseEnd_271774 : Nat := 124045059017888814822347

theorem tailTrace_271774 : CollatzResearch.WordTrace tailWord_271774 prefixEnd_271774 124045059017888814822347 := by
  unfold tailWord_271774
  simp only [CollatzResearch.WordTrace]
  refine ⟨1239051514677086018624797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 6608274744944458765998917 1239051514677086018624797)
  ·
    refine ⟨464644318003907256984299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1239051514677086018624797 464644318003907256984299)
    ·
      refine ⟨696966477005860885476449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 464644318003907256984299 696966477005860885476449)
      ·
        refine ⟨522724857754395664107337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 696966477005860885476449 522724857754395664107337)
        ·
          refine ⟨392043643315796748080503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 522724857754395664107337 392043643315796748080503)
          ·
            refine ⟨588065464973695122120755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 392043643315796748080503 588065464973695122120755)
            ·
              refine ⟨882098197460542683181133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 588065464973695122120755 882098197460542683181133)
              ·
                refine ⟨330786824047703506192925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 882098197460542683181133 330786824047703506192925)
                ·
                  refine ⟨124045059017888814822347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 330786824047703506192925 124045059017888814822347)
                  ·
                    rfl

theorem cell20_271774_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 2, 1, 1, 3, 3].length) (baseStart_271774 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_271774 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_271774 prefixEnd_271774 := by exact prefixLift 271774
  have htrace : WordTrace (prefixWord ++ tailWord_271774) baseStart_271774 baseEnd_271774 := by
    simpa [prefixWord, tailWord_271774, baseEnd_271774] using wordTrace_append hprefix tailTrace_271774
  have hstable : (prefixWord ++ tailWord_271774).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_271774).length < 2 ^ (prefixWord ++ tailWord_271774).sum := by decide
  have hdescent : baseEnd_271774 < baseStart_271774 := by decide
  rcases family_descends (prefixWord ++ tailWord_271774) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_271816 : List Nat := [2, 1, 3, 1, 3, 1, 4, 2, 3]
def baseStart_271816 : Nat := 118140960795 + 271816 * 2 ^ 59
def prefixEnd_271816 : Nat := 4983230072969 + 3 ^ 40 * 271816 * 2
def baseEnd_271816 : Nat := 124064228962323335422175

theorem tailTrace_271816 : CollatzResearch.WordTrace tailWord_271816 prefixEnd_271816 124064228962323335422175 := by
  unfold tailWord_271816
  simp only [CollatzResearch.WordTrace]
  refine ⟨4956971991632264661013651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6609295988843019548018201 4956971991632264661013651)
  ·
    refine ⟨7435457987448396991520477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4956971991632264661013651 7435457987448396991520477)
    ·
      refine ⟨2788296745293148871820179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7435457987448396991520477 2788296745293148871820179)
      ·
        refine ⟨4182445117939723307730269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2788296745293148871820179 4182445117939723307730269)
        ·
          refine ⟨1568416919227396240398851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4182445117939723307730269 1568416919227396240398851)
          ·
            refine ⟨2352625378841094360598277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1568416919227396240398851 2352625378841094360598277)
            ·
              refine ⟨441117258532705192612177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2352625378841094360598277 441117258532705192612177)
              ·
                refine ⟨330837943899528894459133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 441117258532705192612177 330837943899528894459133)
                ·
                  refine ⟨124064228962323335422175, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 330837943899528894459133 124064228962323335422175)
                  ·
                    rfl

theorem cell20_271816_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 4, 2, 3].length) (baseStart_271816 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_271816 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_271816 prefixEnd_271816 := by exact prefixLift 271816
  have htrace : WordTrace (prefixWord ++ tailWord_271816) baseStart_271816 baseEnd_271816 := by
    simpa [prefixWord, tailWord_271816, baseEnd_271816] using wordTrace_append hprefix tailTrace_271816
  have hstable : (prefixWord ++ tailWord_271816).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_271816).length < 2 ^ (prefixWord ++ tailWord_271816).sum := by decide
  have hdescent : baseEnd_271816 < baseStart_271816 := by decide
  rcases family_descends (prefixWord ++ tailWord_271816) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_271847 : List Nat := [1, 1, 5, 2, 1, 3, 3, 4]
def baseStart_271847 : Nat := 118140960795 + 271847 * 2 ^ 59
def prefixEnd_271847 : Nat := 4983230072969 + 3 ^ 40 * 271847 * 2
def baseEnd_271847 : Nat := 41359459402341668462905

theorem tailTrace_271847 : CollatzResearch.WordTrace tailWord_271847 prefixEnd_271847 41359459402341668462905 := by
  unfold tailWord_271847
  simp only [CollatzResearch.WordTrace]
  refine ⟨9915074646152221616405795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6610049764101481077603863 9915074646152221616405795)
  ·
    refine ⟨14872611969228332424608693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9915074646152221616405795 14872611969228332424608693)
    ·
      refine ⟨1394307372115156164807065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 14872611969228332424608693 1394307372115156164807065)
      ·
        refine ⟨1045730529086367123605299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1394307372115156164807065 1045730529086367123605299)
        ·
          refine ⟨1568595793629550685407949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1045730529086367123605299 1568595793629550685407949)
          ·
            refine ⟨588223422611081507027981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1568595793629550685407949 588223422611081507027981)
            ·
              refine ⟨220583783479155565135493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 588223422611081507027981 220583783479155565135493)
              ·
                refine ⟨41359459402341668462905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 220583783479155565135493 41359459402341668462905)
                ·
                  rfl

theorem cell20_271847_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 3, 3, 4].length) (baseStart_271847 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_271847 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_271847 prefixEnd_271847 := by exact prefixLift 271847
  have htrace : WordTrace (prefixWord ++ tailWord_271847) baseStart_271847 baseEnd_271847 := by
    simpa [prefixWord, tailWord_271847, baseEnd_271847] using wordTrace_append hprefix tailTrace_271847
  have hstable : (prefixWord ++ tailWord_271847).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_271847).length < 2 ^ (prefixWord ++ tailWord_271847).sum := by decide
  have hdescent : baseEnd_271847 < baseStart_271847 := by decide
  rcases family_descends (prefixWord ++ tailWord_271847) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_271875 : List Nat := [1, 1, 1, 3, 2, 1, 2, 6, 3]
def baseStart_271875 : Nat := 118140960795 + 271875 * 2 ^ 59
def prefixEnd_271875 : Nat := 4983230072969 + 3 ^ 40 * 271875 * 2
def baseEnd_271875 : Nat := 124091158169981352455267

theorem tailTrace_271875 : CollatzResearch.WordTrace tailWord_271875 prefixEnd_271875 124091158169981352455267 := by
  unfold tailWord_271875
  simp only [CollatzResearch.WordTrace]
  refine ⟨9916095890050782398425079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6610730593367188265616719 9916095890050782398425079)
  ·
    refine ⟨14874143835076173597637619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9916095890050782398425079 14874143835076173597637619)
    ·
      refine ⟨22311215752614260396456429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14874143835076173597637619 22311215752614260396456429)
      ·
        refine ⟨8366705907230347648671161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 22311215752614260396456429 8366705907230347648671161)
        ·
          refine ⟨6275029430422760736503371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8366705907230347648671161 6275029430422760736503371)
          ·
            refine ⟨9412544145634141104755057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6275029430422760736503371 9412544145634141104755057)
            ·
              refine ⟨7059408109225605828566293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9412544145634141104755057 7059408109225605828566293)
              ·
                refine ⟨330909755119950273214045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 7059408109225605828566293 330909755119950273214045)
                ·
                  refine ⟨124091158169981352455267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 330909755119950273214045 124091158169981352455267)
                  ·
                    rfl

theorem cell20_271875_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 2, 6, 3].length) (baseStart_271875 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_271875 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_271875 prefixEnd_271875 := by exact prefixLift 271875
  have htrace : WordTrace (prefixWord ++ tailWord_271875) baseStart_271875 baseEnd_271875 := by
    simpa [prefixWord, tailWord_271875, baseEnd_271875] using wordTrace_append hprefix tailTrace_271875
  have hstable : (prefixWord ++ tailWord_271875).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_271875).length < 2 ^ (prefixWord ++ tailWord_271875).sum := by decide
  have hdescent : baseEnd_271875 < baseStart_271875 := by decide
  rcases family_descends (prefixWord ++ tailWord_271875) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_271889 : List Nat := [1, 2, 2, 1, 1, 2, 4, 7]
def baseStart_271889 : Nat := 118140960795 + 271889 * 2 ^ 59
def prefixEnd_271889 : Nat := 4983230072969 + 3 ^ 40 * 271889 * 2
def baseEnd_271889 : Nat := 41365849383819841996181

theorem tailTrace_271889 : CollatzResearch.WordTrace tailWord_271889 prefixEnd_271889 41365849383819841996181 := by
  unfold tailWord_271889
  simp only [CollatzResearch.WordTrace]
  refine ⟨9916606512000062789434721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6611071008000041859623147 9916606512000062789434721)
  ·
    refine ⟨7437454884000047092076041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9916606512000062789434721 7437454884000047092076041)
    ·
      refine ⟨5578091163000035319057031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7437454884000047092076041 5578091163000035319057031)
      ·
        refine ⟨8367136744500052978585547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5578091163000035319057031 8367136744500052978585547)
        ·
          refine ⟨12550705116750079467878321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8367136744500052978585547 12550705116750079467878321)
          ·
            refine ⟨9413028837562559600908741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12550705116750079467878321 9413028837562559600908741)
            ·
              refine ⟨1764942907042979925170389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9413028837562559600908741 1764942907042979925170389)
              ·
                refine ⟨41365849383819841996181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1764942907042979925170389 41365849383819841996181)
                ·
                  rfl

theorem cell20_271889_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 4, 7].length) (baseStart_271889 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_271889 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_271889 prefixEnd_271889 := by exact prefixLift 271889
  have htrace : WordTrace (prefixWord ++ tailWord_271889) baseStart_271889 baseEnd_271889 := by
    simpa [prefixWord, tailWord_271889, baseEnd_271889] using wordTrace_append hprefix tailTrace_271889
  have hstable : (prefixWord ++ tailWord_271889).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_271889).length < 2 ^ (prefixWord ++ tailWord_271889).sum := by decide
  have hdescent : baseEnd_271889 < baseStart_271889 := by decide
  rcases family_descends (prefixWord ++ tailWord_271889) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_271912 : List Nat := [2, 1, 5, 2, 2, 2, 1, 3, 2]
def baseStart_271912 : Nat := 118140960795 + 271912 * 2 ^ 59
def prefixEnd_271912 : Nat := 4983230072969 + 3 ^ 40 * 271912 * 2
def baseEnd_271912 : Nat := 124108045978173668221783

theorem tailTrace_271912 : CollatzResearch.WordTrace tailWord_271912 prefixEnd_271912 124108045978173668221783 := by
  unfold tailWord_271912
  simp only [CollatzResearch.WordTrace]
  refine ⟨4958722695458368858760995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6611630260611158478347993 4958722695458368858760995)
  ·
    refine ⟨7438084043187553288141493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4958722695458368858760995 7438084043187553288141493)
    ·
      refine ⟨697320379048833120763265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 7438084043187553288141493 697320379048833120763265)
      ·
        refine ⟨522990284286624840572449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 697320379048833120763265 522990284286624840572449)
        ·
          refine ⟨392242713214968630429337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 522990284286624840572449 392242713214968630429337)
          ·
            refine ⟨294182034911226472822003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 392242713214968630429337 294182034911226472822003)
            ·
              refine ⟨441273052366839709233005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 294182034911226472822003 441273052366839709233005)
              ·
                refine ⟨165477394637564890962377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 441273052366839709233005 165477394637564890962377)
                ·
                  refine ⟨124108045978173668221783, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 165477394637564890962377 124108045978173668221783)
                  ·
                    rfl

theorem cell20_271912_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 2, 2, 1, 3, 2].length) (baseStart_271912 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_271912 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_271912 prefixEnd_271912 := by exact prefixLift 271912
  have htrace : WordTrace (prefixWord ++ tailWord_271912) baseStart_271912 baseEnd_271912 := by
    simpa [prefixWord, tailWord_271912, baseEnd_271912] using wordTrace_append hprefix tailTrace_271912
  have hstable : (prefixWord ++ tailWord_271912).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_271912).length < 2 ^ (prefixWord ++ tailWord_271912).sum := by decide
  have hdescent : baseEnd_271912 < baseStart_271912 := by decide
  rcases family_descends (prefixWord ++ tailWord_271912) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_271927 : List Nat := [1, 1, 3, 1, 2, 4, 8]
def baseStart_271927 : Nat := 118140960795 + 271927 * 2 ^ 59
def prefixEnd_271927 : Nat := 4983230072969 + 3 ^ 40 * 271927 * 2
def baseEnd_271927 : Nat := 13790543598544475857969

theorem tailTrace_271927 : CollatzResearch.WordTrace tailWord_271927 prefixEnd_271927 13790543598544475857969 := by
  unfold tailWord_271927
  simp only [CollatzResearch.WordTrace]
  refine ⟨9917992485862395279318035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6611994990574930186212023 9917992485862395279318035)
  ·
    refine ⟨14876988728793592918977053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9917992485862395279318035 14876988728793592918977053)
    ·
      refine ⟨5578870773297597344616395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14876988728793592918977053 5578870773297597344616395)
      ·
        refine ⟨8368306159946396016924593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5578870773297597344616395 8368306159946396016924593)
        ·
          refine ⟨6276229619959797012693445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8368306159946396016924593 6276229619959797012693445)
          ·
            refine ⟨1176793053742461939880021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 6276229619959797012693445 1176793053742461939880021)
            ·
              refine ⟨13790543598544475857969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 1176793053742461939880021 13790543598544475857969)
              ·
                rfl

theorem cell20_271927_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 4, 8].length) (baseStart_271927 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_271927 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_271927 prefixEnd_271927 := by exact prefixLift 271927
  have htrace : WordTrace (prefixWord ++ tailWord_271927) baseStart_271927 baseEnd_271927 := by
    simpa [prefixWord, tailWord_271927, baseEnd_271927] using wordTrace_append hprefix tailTrace_271927
  have hstable : (prefixWord ++ tailWord_271927).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_271927).length < 2 ^ (prefixWord ++ tailWord_271927).sum := by decide
  have hdescent : baseEnd_271927 < baseStart_271927 := by decide
  rcases family_descends (prefixWord ++ tailWord_271927) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_271933 : List Nat := [1, 4, 1, 3, 4, 1, 1, 1, 4]
def baseStart_271933 : Nat := 118140960795 + 271933 * 2 ^ 59
def prefixEnd_271933 : Nat := 4983230072969 + 3 ^ 40 * 271933 * 2
def baseEnd_271933 : Nat := 124117630950390928521697

theorem tailTrace_271933 : CollatzResearch.WordTrace tailWord_271933 prefixEnd_271933 124117630950390928521697 := by
  unfold tailWord_271933
  simp only [CollatzResearch.WordTrace]
  refine ⟨9918211323840658304036453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6612140882560438869357635 9918211323840658304036453)
  ·
    refine ⟨1859664623220123432006835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 9918211323840658304036453 1859664623220123432006835)
    ·
      refine ⟨2789496934830185148010253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1859664623220123432006835 2789496934830185148010253)
      ·
        refine ⟨1046061350561319430503845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2789496934830185148010253 1046061350561319430503845)
        ·
          refine ⟨196136503230247393219471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1046061350561319430503845 196136503230247393219471)
          ·
            refine ⟨294204754845371089829207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 196136503230247393219471 294204754845371089829207)
            ·
              refine ⟨441307132268056634743811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 294204754845371089829207 441307132268056634743811)
              ·
                refine ⟨661960698402084952115717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 441307132268056634743811 661960698402084952115717)
                ·
                  refine ⟨124117630950390928521697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 661960698402084952115717 124117630950390928521697)
                  ·
                    rfl

theorem cell20_271933_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 4, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 4, 1, 1, 1, 4].length) (baseStart_271933 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_271933 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_271933 prefixEnd_271933 := by exact prefixLift 271933
  have htrace : WordTrace (prefixWord ++ tailWord_271933) baseStart_271933 baseEnd_271933 := by
    simpa [prefixWord, tailWord_271933, baseEnd_271933] using wordTrace_append hprefix tailTrace_271933
  have hstable : (prefixWord ++ tailWord_271933).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_271933).length < 2 ^ (prefixWord ++ tailWord_271933).sum := by decide
  have hdescent : baseEnd_271933 < baseStart_271933 := by decide
  rcases family_descends (prefixWord ++ tailWord_271933) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_271982 : List Nat := [4, 1, 2, 2, 3, 8]
def baseStart_271982 : Nat := 118140960795 + 271982 * 2 ^ 59
def prefixEnd_271982 : Nat := 4983230072969 + 3 ^ 40 * 271982 * 2
def baseEnd_271982 : Nat := 4597777625391279106969

theorem tailTrace_271982 : CollatzResearch.WordTrace tailWord_271982 prefixEnd_271982 4597777625391279106969 := by
  unfold tailWord_271982
  simp only [CollatzResearch.WordTrace]
  refine ⟨1239999812582892459071275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 6613332333775426448380133 1239999812582892459071275)
  ·
    refine ⟨1859999718874338688606913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1239999812582892459071275 1859999718874338688606913)
    ·
      refine ⟨1394999789155754016455185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1859999718874338688606913 1394999789155754016455185)
      ·
        refine ⟨1046249841866815512341389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1394999789155754016455185 1046249841866815512341389)
        ·
          refine ⟨392343690700055817128021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1046249841866815512341389 392343690700055817128021)
          ·
            refine ⟨4597777625391279106969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 392343690700055817128021 4597777625391279106969)
            ·
              rfl

theorem cell20_271982_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 3, 8].length) (baseStart_271982 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_271982 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_271982 prefixEnd_271982 := by exact prefixLift 271982
  have htrace : WordTrace (prefixWord ++ tailWord_271982) baseStart_271982 baseEnd_271982 := by
    simpa [prefixWord, tailWord_271982, baseEnd_271982] using wordTrace_append hprefix tailTrace_271982
  have hstable : (prefixWord ++ tailWord_271982).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_271982).length < 2 ^ (prefixWord ++ tailWord_271982).sum := by decide
  have hdescent : baseEnd_271982 < baseStart_271982 := by decide
  rcases family_descends (prefixWord ++ tailWord_271982) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_271996 : List Nat := [2, 2, 2, 1, 1, 2, 1, 5, 4]
def baseStart_271996 : Nat := 118140960795 + 271996 * 2 ^ 59
def prefixEnd_271996 : Nat := 4983230072969 + 3 ^ 40 * 271996 * 2
def baseEnd_271996 : Nat := 124146385867042709421439

theorem tailTrace_271996 : CollatzResearch.WordTrace tailWord_271996 prefixEnd_271996 124146385867042709421439 := by
  unfold tailWord_271996
  simp only [CollatzResearch.WordTrace]
  refine ⟨4960254561306210031789921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6613672748408280042386561 4960254561306210031789921)
  ·
    refine ⟨3720190920979657523842441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4960254561306210031789921 3720190920979657523842441)
    ·
      refine ⟨2790143190734743142881831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3720190920979657523842441 2790143190734743142881831)
      ·
        refine ⟨4185214786102114714322747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2790143190734743142881831 4185214786102114714322747)
        ·
          refine ⟨6277822179153172071484121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4185214786102114714322747 6277822179153172071484121)
          ·
            refine ⟨4708366634364879053613091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6277822179153172071484121 4708366634364879053613091)
            ·
              refine ⟨7062549951547318580419637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4708366634364879053613091 7062549951547318580419637)
              ·
                refine ⟨662114057957561116914341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 7062549951547318580419637 662114057957561116914341)
                ·
                  refine ⟨124146385867042709421439, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 662114057957561116914341 124146385867042709421439)
                  ·
                    rfl

theorem cell20_271996_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 1, 5, 4].length) (baseStart_271996 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_271996 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_271996 prefixEnd_271996 := by exact prefixLift 271996
  have htrace : WordTrace (prefixWord ++ tailWord_271996) baseStart_271996 baseEnd_271996 := by
    simpa [prefixWord, tailWord_271996, baseEnd_271996] using wordTrace_append hprefix tailTrace_271996
  have hstable : (prefixWord ++ tailWord_271996).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_271996).length < 2 ^ (prefixWord ++ tailWord_271996).sum := by decide
  have hdescent : baseEnd_271996 < baseStart_271996 := by decide
  rcases family_descends (prefixWord ++ tailWord_271996) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_272040 : List Nat := [2, 1, 7, 1, 1, 1, 1, 1, 5]
def baseStart_272040 : Nat := 118140960795 + 272040 * 2 ^ 59
def prefixEnd_272040 : Nat := 4983230072969 + 3 ^ 40 * 272040 * 2
def baseEnd_272040 : Nat := 124166468665974111954593

theorem tailTrace_272040 : CollatzResearch.WordTrace tailWord_272040 prefixEnd_272040 124166468665974111954593 := by
  unfold tailWord_272040
  simp only [CollatzResearch.WordTrace]
  refine ⟨4961056967226507789090787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6614742622968677052121049 4961056967226507789090787)
  ·
    refine ⟨7441585450839761683636181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4961056967226507789090787 7441585450839761683636181)
    ·
      refine ⟨174412159004056914460223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 7441585450839761683636181 174412159004056914460223)
      ·
        refine ⟨261618238506085371690335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 174412159004056914460223 261618238506085371690335)
        ·
          refine ⟨392427357759128057535503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 261618238506085371690335 392427357759128057535503)
          ·
            refine ⟨588641036638692086303255, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 392427357759128057535503 588641036638692086303255)
            ·
              refine ⟨882961554958038129454883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 588641036638692086303255 882961554958038129454883)
              ·
                refine ⟨1324442332437057194182325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 882961554958038129454883 1324442332437057194182325)
                ·
                  refine ⟨124166468665974111954593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1324442332437057194182325 124166468665974111954593)
                  ·
                    rfl

theorem cell20_272040_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 7, 1, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 7, 1, 1, 1, 1, 1, 5].length) (baseStart_272040 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_272040 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_272040 prefixEnd_272040 := by exact prefixLift 272040
  have htrace : WordTrace (prefixWord ++ tailWord_272040) baseStart_272040 baseEnd_272040 := by
    simpa [prefixWord, tailWord_272040, baseEnd_272040] using wordTrace_append hprefix tailTrace_272040
  have hstable : (prefixWord ++ tailWord_272040).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_272040).length < 2 ^ (prefixWord ++ tailWord_272040).sum := by decide
  have hdescent : baseEnd_272040 < baseStart_272040 := by decide
  rcases family_descends (prefixWord ++ tailWord_272040) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_272051 : List Nat := [1, 1, 1, 2, 3, 3, 1, 6, 2]
def baseStart_272051 : Nat := 118140960795 + 272051 * 2 ^ 59
def prefixEnd_272051 : Nat := 4983230072969 + 3 ^ 40 * 272051 * 2
def baseEnd_272051 : Nat := 124171489365706962587881

theorem tailTrace_272051 : CollatzResearch.WordTrace tailWord_272051 prefixEnd_272051 124171489365706962587881 := by
  unfold tailWord_272051
  simp only [CollatzResearch.WordTrace]
  refine ⟨9922515137413164456832007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6615010091608776304554671 9922515137413164456832007)
  ·
    refine ⟨14883772706119746685248011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9922515137413164456832007 14883772706119746685248011)
    ·
      refine ⟨22325659059179620027872017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14883772706119746685248011 22325659059179620027872017)
      ·
        refine ⟨16744244294384715020904013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22325659059179620027872017 16744244294384715020904013)
        ·
          refine ⟨6279091610394268132839005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16744244294384715020904013 6279091610394268132839005)
          ·
            refine ⟨2354659353897850549814627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6279091610394268132839005 2354659353897850549814627)
            ·
              refine ⟨3531989030846775824721941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2354659353897850549814627 3531989030846775824721941)
              ·
                refine ⟨165561985820942616783841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3531989030846775824721941 165561985820942616783841)
                ·
                  refine ⟨124171489365706962587881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 165561985820942616783841 124171489365706962587881)
                  ·
                    rfl

theorem cell20_272051_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 1, 6, 2].length) (baseStart_272051 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_272051 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_272051 prefixEnd_272051 := by exact prefixLift 272051
  have htrace : WordTrace (prefixWord ++ tailWord_272051) baseStart_272051 baseEnd_272051 := by
    simpa [prefixWord, tailWord_272051, baseEnd_272051] using wordTrace_append hprefix tailTrace_272051
  have hstable : (prefixWord ++ tailWord_272051).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_272051).length < 2 ^ (prefixWord ++ tailWord_272051).sum := by decide
  have hdescent : baseEnd_272051 < baseStart_272051 := by decide
  rcases family_descends (prefixWord ++ tailWord_272051) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_272072 : List Nat := [2, 1, 3, 1, 2, 2, 1, 4, 4]
def baseStart_272072 : Nat := 118140960795 + 272072 * 2 ^ 59
def prefixEnd_272072 : Nat := 4983230072969 + 3 ^ 40 * 272072 * 2
def baseEnd_272072 : Nat := 124181074337924222887795

theorem tailTrace_272072 : CollatzResearch.WordTrace tailWord_272072 prefixEnd_272072 124181074337924222887795 := by
  unfold tailWord_272072
  simp only [CollatzResearch.WordTrace]
  refine ⟨4961640535168542521673235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6615520713558056695564313 4961640535168542521673235)
  ·
    refine ⟨7442460802752813782509853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4961640535168542521673235 7442460802752813782509853)
    ·
      refine ⟨2790922801032305168441195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7442460802752813782509853 2790922801032305168441195)
      ·
        refine ⟨4186384201548457752661793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2790922801032305168441195 4186384201548457752661793)
        ·
          refine ⟨3139788151161343314496345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4186384201548457752661793 3139788151161343314496345)
          ·
            refine ⟨2354841113371007485872259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3139788151161343314496345 2354841113371007485872259)
            ·
              refine ⟨3532261670056511228808389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2354841113371007485872259 3532261670056511228808389)
              ·
                refine ⟨662299063135595855401573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3532261670056511228808389 662299063135595855401573)
                ·
                  refine ⟨124181074337924222887795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 662299063135595855401573 124181074337924222887795)
                  ·
                    rfl

theorem cell20_272072_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 1, 4, 4].length) (baseStart_272072 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_272072 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_272072 prefixEnd_272072 := by exact prefixLift 272072
  have htrace : WordTrace (prefixWord ++ tailWord_272072) baseStart_272072 baseEnd_272072 := by
    simpa [prefixWord, tailWord_272072, baseEnd_272072] using wordTrace_append hprefix tailTrace_272072
  have hstable : (prefixWord ++ tailWord_272072).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_272072).length < 2 ^ (prefixWord ++ tailWord_272072).sum := by decide
  have hdescent : baseEnd_272072 < baseStart_272072 := by decide
  rcases family_descends (prefixWord ++ tailWord_272072) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_272092 : List Nat := [2, 2, 5, 1, 3, 1, 6]
def baseStart_272092 : Nat := 118140960795 + 272092 * 2 ^ 59
def prefixEnd_272092 : Nat := 4983230072969 + 3 ^ 40 * 272092 * 2
def baseEnd_272092 : Nat := 13798911431432560246783

theorem tailTrace_272092 : CollatzResearch.WordTrace tailWord_272092 prefixEnd_272092 13798911431432560246783 := by
  unfold tailWord_272092
  simp only [CollatzResearch.WordTrace]
  refine ⟨4962005265132314229537265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6616007020176418972716353 4962005265132314229537265)
  ·
    refine ⟨3721503948849235672152949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4962005265132314229537265 3721503948849235672152949)
    ·
      refine ⟨348890995204615844264339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 3721503948849235672152949 348890995204615844264339)
      ·
        refine ⟨523336492806923766396509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 348890995204615844264339 523336492806923766396509)
        ·
          refine ⟨196251184802596412398691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 523336492806923766396509 196251184802596412398691)
          ·
            refine ⟨294376777203894618598037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 196251184802596412398691 294376777203894618598037)
            ·
              refine ⟨13798911431432560246783, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 294376777203894618598037 13798911431432560246783)
              ·
                rfl

theorem cell20_272092_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 3, 1, 6].length) (baseStart_272092 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_272092 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_272092 prefixEnd_272092 := by exact prefixLift 272092
  have htrace : WordTrace (prefixWord ++ tailWord_272092) baseStart_272092 baseEnd_272092 := by
    simpa [prefixWord, tailWord_272092, baseEnd_272092] using wordTrace_append hprefix tailTrace_272092
  have hstable : (prefixWord ++ tailWord_272092).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_272092).length < 2 ^ (prefixWord ++ tailWord_272092).sum := by decide
  have hdescent : baseEnd_272092 < baseStart_272092 := by decide
  rcases family_descends (prefixWord ++ tailWord_272092) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_272116 : List Nat := [2, 6, 1, 1, 1, 2, 1, 3, 3]
def baseStart_272116 : Nat := 118140960795 + 272116 * 2 ^ 59
def prefixEnd_272116 : Nat := 4983230072969 + 3 ^ 40 * 272116 * 2
def baseEnd_272116 : Nat := 124201157136855625420949

theorem tailTrace_272116 : CollatzResearch.WordTrace tailWord_272116 prefixEnd_272116 124201157136855625420949 := by
  unfold tailWord_272116
  simp only [CollatzResearch.WordTrace]
  refine ⟨4962442941088840278974101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6616590588118453705298801 4962442941088840278974101)
  ·
    refine ⟨232614512863539388076911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 4962442941088840278974101 232614512863539388076911)
    ·
      refine ⟨348921769295309082115367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 232614512863539388076911 348921769295309082115367)
      ·
        refine ⟨523382653942963623173051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 348921769295309082115367 523382653942963623173051)
        ·
          refine ⟨785073980914445434759577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 523382653942963623173051 785073980914445434759577)
          ·
            refine ⟨588805485685834076069683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 785073980914445434759577 588805485685834076069683)
            ·
              refine ⟨883208228528751114104525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 588805485685834076069683 883208228528751114104525)
              ·
                refine ⟨331203085698281667789197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 883208228528751114104525 331203085698281667789197)
                ·
                  refine ⟨124201157136855625420949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 331203085698281667789197 124201157136855625420949)
                  ·
                    rfl

theorem cell20_272116_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 2, 1, 3, 3].length) (baseStart_272116 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_272116 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_272116 prefixEnd_272116 := by exact prefixLift 272116
  have htrace : WordTrace (prefixWord ++ tailWord_272116) baseStart_272116 baseEnd_272116 := by
    simpa [prefixWord, tailWord_272116, baseEnd_272116] using wordTrace_append hprefix tailTrace_272116
  have hstable : (prefixWord ++ tailWord_272116).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_272116).length < 2 ^ (prefixWord ++ tailWord_272116).sum := by decide
  have hdescent : baseEnd_272116 < baseStart_272116 := by decide
  rcases family_descends (prefixWord ++ tailWord_272116) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_272161 : List Nat := [1, 2, 3, 2, 1, 5, 2, 2, 2]
def baseStart_272161 : Nat := 118140960795 + 272161 * 2 ^ 59
def prefixEnd_272161 : Nat := 4983230072969 + 3 ^ 40 * 272161 * 2
def baseEnd_272161 : Nat := 124221696363035468920765

theorem tailTrace_272161 : CollatzResearch.WordTrace tailWord_272161 prefixEnd_272161 124221696363035468920765 := by
  unfold tailWord_272161
  simp only [CollatzResearch.WordTrace]
  refine ⟨9926527167014653243336337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6617684778009768828890891 9926527167014653243336337)
  ·
    refine ⟨7444895375260989932502253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9926527167014653243336337 7444895375260989932502253)
    ·
      refine ⟨2791835765722871224688345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7444895375260989932502253 2791835765722871224688345)
      ·
        refine ⟨2093876824292153418516259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2791835765722871224688345 2093876824292153418516259)
        ·
          refine ⟨3140815236438230127774389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2093876824292153418516259 3140815236438230127774389)
          ·
            refine ⟨294451428416084074478849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 3140815236438230127774389 294451428416084074478849)
            ·
              refine ⟨220838571312063055859137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 294451428416084074478849 220838571312063055859137)
              ·
                refine ⟨165628928484047291894353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 220838571312063055859137 165628928484047291894353)
                ·
                  refine ⟨124221696363035468920765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 165628928484047291894353 124221696363035468920765)
                  ·
                    rfl

theorem cell20_272161_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 5, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 5, 2, 2, 2].length) (baseStart_272161 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_272161 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_272161 prefixEnd_272161 := by exact prefixLift 272161
  have htrace : WordTrace (prefixWord ++ tailWord_272161) baseStart_272161 baseEnd_272161 := by
    simpa [prefixWord, tailWord_272161, baseEnd_272161] using wordTrace_append hprefix tailTrace_272161
  have hstable : (prefixWord ++ tailWord_272161).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_272161).length < 2 ^ (prefixWord ++ tailWord_272161).sum := by decide
  have hdescent : baseEnd_272161 < baseStart_272161 := by decide
  rcases family_descends (prefixWord ++ tailWord_272161) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_272172 : List Nat := [2, 2, 1, 1, 1, 7, 1, 5]
def baseStart_272172 : Nat := 118140960795 + 272172 * 2 ^ 59
def prefixEnd_272172 : Nat := 4983230072969 + 3 ^ 40 * 272172 * 2
def baseEnd_272172 : Nat := 41408905687589439851351

theorem tailTrace_272172 : CollatzResearch.WordTrace tailWord_272172 prefixEnd_272172 41408905687589439851351 := by
  unfold tailWord_272172
  simp only [CollatzResearch.WordTrace]
  refine ⟨4963464184987401060993385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6617952246649868081324513 4963464184987401060993385)
  ·
    refine ⟨3722598138740550795745039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4963464184987401060993385 3722598138740550795745039)
    ·
      refine ⟨5583897208110826193617559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3722598138740550795745039 5583897208110826193617559)
      ·
        refine ⟨8375845812166239290426339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5583897208110826193617559 8375845812166239290426339)
        ·
          refine ⟨12563768718249358935639509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8375845812166239290426339 12563768718249358935639509)
          ·
            refine ⟨294463329333969350054051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 12563768718249358935639509 294463329333969350054051)
            ·
              refine ⟨441694994000954025081077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 294463329333969350054051 441694994000954025081077)
              ·
                refine ⟨41408905687589439851351, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 441694994000954025081077 41408905687589439851351)
                ·
                  rfl

theorem cell20_272172_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 7, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 7, 1, 5].length) (baseStart_272172 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_272172 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_272172 prefixEnd_272172 := by exact prefixLift 272172
  have htrace : WordTrace (prefixWord ++ tailWord_272172) baseStart_272172 baseEnd_272172 := by
    simpa [prefixWord, tailWord_272172, baseEnd_272172] using wordTrace_append hprefix tailTrace_272172
  have hstable : (prefixWord ++ tailWord_272172).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_272172).length < 2 ^ (prefixWord ++ tailWord_272172).sum := by decide
  have hdescent : baseEnd_272172 < baseStart_272172 := by decide
  rcases family_descends (prefixWord ++ tailWord_272172) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_272182 : List Nat := [5, 1, 2, 2, 1, 2, 1, 2, 4]
def baseStart_272182 : Nat := 118140960795 + 272182 * 2 ^ 59
def prefixEnd_272182 : Nat := 4983230072969 + 3 ^ 40 * 272182 * 2
def baseEnd_272182 : Nat := 124231281335252729220679

theorem tailTrace_272182 : CollatzResearch.WordTrace tailWord_272182 prefixEnd_272182 124231281335252729220679 := by
  unfold tailWord_272182
  simp only [CollatzResearch.WordTrace]
  refine ⟨620455818746160864365675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 6618195399959049219900533 620455818746160864365675)
  ·
    refine ⟨930683728119241296548513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 620455818746160864365675 930683728119241296548513)
    ·
      refine ⟨698012796089430972411385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 930683728119241296548513 698012796089430972411385)
      ·
        refine ⟨523509597067073229308539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 698012796089430972411385 523509597067073229308539)
        ·
          refine ⟨785264395600609843962809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 523509597067073229308539 785264395600609843962809)
          ·
            refine ⟨588948296700457382972107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 785264395600609843962809 588948296700457382972107)
            ·
              refine ⟨883422445050686074458161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 588948296700457382972107 883422445050686074458161)
              ·
                refine ⟨662566833788014555843621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 883422445050686074458161 662566833788014555843621)
                ·
                  refine ⟨124231281335252729220679, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 662566833788014555843621 124231281335252729220679)
                  ·
                    rfl

theorem cell20_272182_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 2, 1, 2, 4].length) (baseStart_272182 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_272182 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_272182 prefixEnd_272182 := by exact prefixLift 272182
  have htrace : WordTrace (prefixWord ++ tailWord_272182) baseStart_272182 baseEnd_272182 := by
    simpa [prefixWord, tailWord_272182, baseEnd_272182] using wordTrace_append hprefix tailTrace_272182
  have hstable : (prefixWord ++ tailWord_272182).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_272182).length < 2 ^ (prefixWord ++ tailWord_272182).sum := by decide
  have hdescent : baseEnd_272182 < baseStart_272182 := by decide
  rcases family_descends (prefixWord ++ tailWord_272182) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_272186 : List Nat := [3, 1, 1, 1, 5, 1, 1, 1, 6]
def baseStart_272186 : Nat := 118140960795 + 272186 * 2 ^ 59
def prefixEnd_272186 : Nat := 4983230072969 + 3 ^ 40 * 272186 * 2
def baseEnd_272186 : Nat := 124233107044246493087329

theorem tailTrace_272186 : CollatzResearch.WordTrace tailWord_272186 prefixEnd_272186 124233107044246493087329 := by
  unfold tailWord_272186
  simp only [CollatzResearch.WordTrace]
  refine ⟨2481859747981020628249103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6618292661282721675330941 2481859747981020628249103)
  ·
    refine ⟨3722789621971530942373655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2481859747981020628249103 3722789621971530942373655)
    ·
      refine ⟨5584184432957296413560483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3722789621971530942373655 5584184432957296413560483)
      ·
        refine ⟨8376276649435944620340725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5584184432957296413560483 8376276649435944620340725)
        ·
          refine ⟨785275935884619808156943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 8376276649435944620340725 785275935884619808156943)
          ·
            refine ⟨1177913903826929712235415, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 785275935884619808156943 1177913903826929712235415)
            ·
              refine ⟨1766870855740394568353123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1177913903826929712235415 1766870855740394568353123)
              ·
                refine ⟨2650306283610591852529685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1766870855740394568353123 2650306283610591852529685)
                ·
                  refine ⟨124233107044246493087329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2650306283610591852529685 124233107044246493087329)
                  ·
                    rfl

theorem cell20_272186_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 1, 1, 1, 6].length) (baseStart_272186 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_272186 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_272186 prefixEnd_272186 := by exact prefixLift 272186
  have htrace : WordTrace (prefixWord ++ tailWord_272186) baseStart_272186 baseEnd_272186 := by
    simpa [prefixWord, tailWord_272186, baseEnd_272186] using wordTrace_append hprefix tailTrace_272186
  have hstable : (prefixWord ++ tailWord_272186).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_272186).length < 2 ^ (prefixWord ++ tailWord_272186).sum := by decide
  have hdescent : baseEnd_272186 < baseStart_272186 := by decide
  rcases family_descends (prefixWord ++ tailWord_272186) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_272189 : List Nat := [1, 4, 1, 4, 1, 2, 3, 4]
def baseStart_272189 : Nat := 118140960795 + 272189 * 2 ^ 59
def prefixEnd_272189 : Nat := 4983230072969 + 3 ^ 40 * 272189 * 2
def baseEnd_272189 : Nat := 41411492108663938662439

theorem tailTrace_272189 : CollatzResearch.WordTrace tailWord_272189 prefixEnd_272189 41411492108663938662439 := by
  unfold tailWord_272189
  simp only [CollatzResearch.WordTrace]
  refine ⟨9927548410913214025355621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6618365607275476016903747 9927548410913214025355621)
  ·
    refine ⟨1861415327046227629754179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 9927548410913214025355621 1861415327046227629754179)
    ·
      refine ⟨2792122990569341444631269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1861415327046227629754179 2792122990569341444631269)
      ·
        refine ⟨523523060731751520868363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2792122990569341444631269 523523060731751520868363)
        ·
          refine ⟨785284591097627281302545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 523523060731751520868363 785284591097627281302545)
          ·
            refine ⟨588963443323220460976909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 785284591097627281302545 588963443323220460976909)
            ·
              refine ⟨220861291246207672866341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 588963443323220460976909 220861291246207672866341)
              ·
                refine ⟨41411492108663938662439, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 220861291246207672866341 41411492108663938662439)
                ·
                  rfl

theorem cell20_272189_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 2, 3, 4].length) (baseStart_272189 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_272189 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_272189 prefixEnd_272189 := by exact prefixLift 272189
  have htrace : WordTrace (prefixWord ++ tailWord_272189) baseStart_272189 baseEnd_272189 := by
    simpa [prefixWord, tailWord_272189, baseEnd_272189] using wordTrace_append hprefix tailTrace_272189
  have hstable : (prefixWord ++ tailWord_272189).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_272189).length < 2 ^ (prefixWord ++ tailWord_272189).sum := by decide
  have hdescent : baseEnd_272189 < baseStart_272189 := by decide
  rcases family_descends (prefixWord ++ tailWord_272189) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_272220 : List Nat := [2, 2, 4, 2, 2, 1, 2, 1, 4]
def baseStart_272220 : Nat := 118140960795 + 272220 * 2 ^ 59
def prefixEnd_272220 : Nat := 4983230072969 + 3 ^ 40 * 272220 * 2
def baseEnd_272220 : Nat := 124248625570693485953857

theorem tailTrace_272220 : CollatzResearch.WordTrace tailWord_272220 prefixEnd_272220 124248625570693485953857 := by
  unfold tailWord_272220
  simp only [CollatzResearch.WordTrace]
  refine ⟨4964339536900453159867057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6619119382533937546489409 4964339536900453159867057)
  ·
    refine ⟨3723254652675339869900293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4964339536900453159867057 3723254652675339869900293)
    ·
      refine ⟨698110247376626225606305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3723254652675339869900293 698110247376626225606305)
      ·
        refine ⟨523582685532469669204729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 698110247376626225606305 523582685532469669204729)
        ·
          refine ⟨392687014149352251903547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 523582685532469669204729 392687014149352251903547)
          ·
            refine ⟨589030521224028377855321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 392687014149352251903547 589030521224028377855321)
            ·
              refine ⟨441772890918021283391491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 589030521224028377855321 441772890918021283391491)
              ·
                refine ⟨662659336377031925087237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 441772890918021283391491 662659336377031925087237)
                ·
                  refine ⟨124248625570693485953857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 662659336377031925087237 124248625570693485953857)
                  ·
                    rfl

theorem cell20_272220_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 2, 1, 2, 1, 4].length) (baseStart_272220 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_272220 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_272220 prefixEnd_272220 := by exact prefixLift 272220
  have htrace : WordTrace (prefixWord ++ tailWord_272220) baseStart_272220 baseEnd_272220 := by
    simpa [prefixWord, tailWord_272220, baseEnd_272220] using wordTrace_append hprefix tailTrace_272220
  have hstable : (prefixWord ++ tailWord_272220).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_272220).length < 2 ^ (prefixWord ++ tailWord_272220).sum := by decide
  have hdescent : baseEnd_272220 < baseStart_272220 := by decide
  rcases family_descends (prefixWord ++ tailWord_272220) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_272224 : List Nat := [2, 1, 1, 3, 3, 2, 1, 3, 4]
def baseStart_272224 : Nat := 118140960795 + 272224 * 2 ^ 59
def prefixEnd_272224 : Nat := 4983230072969 + 3 ^ 40 * 272224 * 2
def baseEnd_272224 : Nat := 124250451279687249820507

theorem tailTrace_272224 : CollatzResearch.WordTrace tailWord_272224 prefixEnd_272224 124250451279687249820507 := by
  unfold tailWord_272224
  simp only [CollatzResearch.WordTrace]
  refine ⟨4964412482893207501439863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6619216643857610001919817 4964412482893207501439863)
  ·
    refine ⟨7446618724339811252159795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4964412482893207501439863 7446618724339811252159795)
    ·
      refine ⟨11169928086509716878239693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7446618724339811252159795 11169928086509716878239693)
      ·
        refine ⟨4188723032441143829339885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11169928086509716878239693 4188723032441143829339885)
        ·
          refine ⟨1570771137165428936002457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4188723032441143829339885 1570771137165428936002457)
          ·
            refine ⟨1178078352874071702001843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1570771137165428936002457 1178078352874071702001843)
            ·
              refine ⟨1767117529311107553002765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1178078352874071702001843 1767117529311107553002765)
              ·
                refine ⟨662669073491665332376037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1767117529311107553002765 662669073491665332376037)
                ·
                  refine ⟨124250451279687249820507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 662669073491665332376037 124250451279687249820507)
                  ·
                    rfl

theorem cell20_272224_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 2, 1, 3, 4].length) (baseStart_272224 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_272224 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_272224 prefixEnd_272224 := by exact prefixLift 272224
  have htrace : WordTrace (prefixWord ++ tailWord_272224) baseStart_272224 baseEnd_272224 := by
    simpa [prefixWord, tailWord_272224, baseEnd_272224] using wordTrace_append hprefix tailTrace_272224
  have hstable : (prefixWord ++ tailWord_272224).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_272224).length < 2 ^ (prefixWord ++ tailWord_272224).sum := by decide
  have hdescent : baseEnd_272224 < baseStart_272224 := by decide
  rcases family_descends (prefixWord ++ tailWord_272224) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_272231 : List Nat := [1, 1, 5, 1, 2, 1, 2, 7]
def baseStart_272231 : Nat := 118140960795 + 272231 * 2 ^ 59
def prefixEnd_272231 : Nat := 4983230072969 + 3 ^ 40 * 272231 * 2
def baseEnd_272231 : Nat := 41417882090142112195715

theorem tailTrace_272231 : CollatzResearch.WordTrace tailWord_272231 prefixEnd_272231 41417882090142112195715 := by
  unfold tailWord_272231
  simp only [CollatzResearch.WordTrace]
  refine ⟨9929080276761055198384547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6619386851174036798923031 9929080276761055198384547)
  ·
    refine ⟨14893620415141582797576821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9929080276761055198384547 14893620415141582797576821)
    ·
      refine ⟨1396276913919523387272827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 14893620415141582797576821 1396276913919523387272827)
      ·
        refine ⟨2094415370879285080909241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1396276913919523387272827 2094415370879285080909241)
        ·
          refine ⟨1570811528159463810681931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2094415370879285080909241 1570811528159463810681931)
          ·
            refine ⟨2356217292239195716022897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1570811528159463810681931 2356217292239195716022897)
            ·
              refine ⟨1767162969179396787017173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2356217292239195716022897 1767162969179396787017173)
              ·
                refine ⟨41417882090142112195715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1767162969179396787017173 41417882090142112195715)
                ·
                  rfl

theorem cell20_272231_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 2, 7].length) (baseStart_272231 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_272231 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_272231 prefixEnd_272231 := by exact prefixLift 272231
  have htrace : WordTrace (prefixWord ++ tailWord_272231) baseStart_272231 baseEnd_272231 := by
    simpa [prefixWord, tailWord_272231, baseEnd_272231] using wordTrace_append hprefix tailTrace_272231
  have hstable : (prefixWord ++ tailWord_272231).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_272231).length < 2 ^ (prefixWord ++ tailWord_272231).sum := by decide
  have hdescent : baseEnd_272231 < baseStart_272231 := by decide
  rcases family_descends (prefixWord ++ tailWord_272231) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_272254 : List Nat := [4, 2, 3, 1, 1, 3, 1, 3, 2]
def baseStart_272254 : Nat := 118140960795 + 272254 * 2 ^ 59
def prefixEnd_272254 : Nat := 4983230072969 + 3 ^ 40 * 272254 * 2
def baseEnd_272254 : Nat := 124264144097140478820385

theorem tailTrace_272254 : CollatzResearch.WordTrace tailWord_272254 prefixEnd_272254 124264144097140478820385 := by
  unfold tailWord_272254
  simp only [CollatzResearch.WordTrace]
  refine ⟨1241239894459716265808977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 6619946103785153417647877 1241239894459716265808977)
  ·
    refine ⟨930929920844787199356733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1241239894459716265808977 930929920844787199356733)
    ·
      refine ⟨349098720316795199758775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 930929920844787199356733 349098720316795199758775)
      ·
        refine ⟨523648080475192799638163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 349098720316795199758775 523648080475192799638163)
        ·
          refine ⟨785472120712789199457245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 523648080475192799638163 785472120712789199457245)
          ·
            refine ⟨294552045267295949796467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 785472120712789199457245 294552045267295949796467)
            ·
              refine ⟨441828067900943924694701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 294552045267295949796467 441828067900943924694701)
              ·
                refine ⟨165685525462853971760513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 441828067900943924694701 165685525462853971760513)
                ·
                  refine ⟨124264144097140478820385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 165685525462853971760513 124264144097140478820385)
                  ·
                    rfl

theorem cell20_272254_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 3, 1, 3, 2].length) (baseStart_272254 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_272254 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_272254 prefixEnd_272254 := by exact prefixLift 272254
  have htrace : WordTrace (prefixWord ++ tailWord_272254) baseStart_272254 baseEnd_272254 := by
    simpa [prefixWord, tailWord_272254, baseEnd_272254] using wordTrace_append hprefix tailTrace_272254
  have hstable : (prefixWord ++ tailWord_272254).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_272254).length < 2 ^ (prefixWord ++ tailWord_272254).sum := by decide
  have hdescent : baseEnd_272254 < baseStart_272254 := by decide
  rcases family_descends (prefixWord ++ tailWord_272254) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_272279 : List Nat := [1, 1, 3, 3, 1, 5, 1, 1, 4]
def baseStart_272279 : Nat := 118140960795 + 272279 * 2 ^ 59
def prefixEnd_272279 : Nat := 4983230072969 + 3 ^ 40 * 272279 * 2
def baseEnd_272279 : Nat := 124275554778351502986949

theorem tailTrace_272279 : CollatzResearch.WordTrace tailWord_272279 prefixEnd_272279 124275554778351502986949 := by
  unfold tailWord_272279
  simp only [CollatzResearch.WordTrace]
  refine ⟨9930830980587159396131891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6620553987058106264087927 9930830980587159396131891)
  ·
    refine ⟨14896246470880739094197837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9930830980587159396131891 14896246470880739094197837)
    ·
      refine ⟨5586092426580277160324189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14896246470880739094197837 5586092426580277160324189)
      ·
        refine ⟨2094784659967603935121571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5586092426580277160324189 2094784659967603935121571)
        ·
          refine ⟨3142176989951405902682357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2094784659967603935121571 3142176989951405902682357)
          ·
            refine ⟨294579092807944303376471, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 3142176989951405902682357 294579092807944303376471)
            ·
              refine ⟨441868639211916455064707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 294579092807944303376471 441868639211916455064707)
              ·
                refine ⟨662802958817874682597061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 441868639211916455064707 662802958817874682597061)
                ·
                  refine ⟨124275554778351502986949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 662802958817874682597061 124275554778351502986949)
                  ·
                    rfl

theorem cell20_272279_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 5, 1, 1, 4].length) (baseStart_272279 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_272279 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_272279 prefixEnd_272279 := by exact prefixLift 272279
  have htrace : WordTrace (prefixWord ++ tailWord_272279) baseStart_272279 baseEnd_272279 := by
    simpa [prefixWord, tailWord_272279, baseEnd_272279] using wordTrace_append hprefix tailTrace_272279
  have hstable : (prefixWord ++ tailWord_272279).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_272279).length < 2 ^ (prefixWord ++ tailWord_272279).sum := by decide
  have hdescent : baseEnd_272279 < baseStart_272279 := by decide
  rcases family_descends (prefixWord ++ tailWord_272279) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_272314 : List Nat := [3, 1, 1, 1, 2, 1, 2, 4, 5]
def baseStart_272314 : Nat := 118140960795 + 272314 * 2 ^ 59
def prefixEnd_272314 : Nat := 4983230072969 + 3 ^ 40 * 272314 * 2
def baseEnd_272314 : Nat := 124291529732046936820139

theorem tailTrace_272314 : CollatzResearch.WordTrace tailWord_272314 prefixEnd_272314 124291529732046936820139 := by
  unfold tailWord_272314
  simp only [CollatzResearch.WordTrace]
  refine ⟨2483026883865090093413999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6621405023640240249103997 2483026883865090093413999)
  ·
    refine ⟨3724540325797635140120999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2483026883865090093413999 3724540325797635140120999)
    ·
      refine ⟨5586810488696452710181499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3724540325797635140120999 5586810488696452710181499)
      ·
        refine ⟨8380215733044679065272249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5586810488696452710181499 8380215733044679065272249)
        ·
          refine ⟨6285161799783509298954187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8380215733044679065272249 6285161799783509298954187)
          ·
            refine ⟨9427742699675263948431281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6285161799783509298954187 9427742699675263948431281)
            ·
              refine ⟨7070807024756447961323461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9427742699675263948431281 7070807024756447961323461)
              ·
                refine ⟨1325776317141833992748149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7070807024756447961323461 1325776317141833992748149)
                ·
                  refine ⟨124291529732046936820139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1325776317141833992748149 124291529732046936820139)
                  ·
                    rfl

theorem cell20_272314_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 2, 4, 5].length) (baseStart_272314 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_272314 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_272314 prefixEnd_272314 := by exact prefixLift 272314
  have htrace : WordTrace (prefixWord ++ tailWord_272314) baseStart_272314 baseEnd_272314 := by
    simpa [prefixWord, tailWord_272314, baseEnd_272314] using wordTrace_append hprefix tailTrace_272314
  have hstable : (prefixWord ++ tailWord_272314).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_272314).length < 2 ^ (prefixWord ++ tailWord_272314).sum := by decide
  have hdescent : baseEnd_272314 < baseStart_272314 := by decide
  rcases family_descends (prefixWord ++ tailWord_272314) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_272331 : List Nat := [1, 1, 1, 1, 3, 4, 4, 2, 3]
def baseStart_272331 : Nat := 118140960795 + 272331 * 2 ^ 59
def prefixEnd_272331 : Nat := 4983230072969 + 3 ^ 40 * 272331 * 2
def baseEnd_272331 : Nat := 124299288995270433253403

theorem tailTrace_272331 : CollatzResearch.WordTrace tailWord_272331 prefixEnd_272331 124299288995270433253403 := by
  unfold tailWord_272331
  simp only [CollatzResearch.WordTrace]
  refine ⟨9932727576398772277024847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6621818384265848184683231 9932727576398772277024847)
  ·
    refine ⟨14899091364598158415537271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9932727576398772277024847 14899091364598158415537271)
    ·
      refine ⟨22348637046897237623305907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14899091364598158415537271 22348637046897237623305907)
      ·
        refine ⟨33522955570345856434958861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22348637046897237623305907 33522955570345856434958861)
        ·
          refine ⟨12571108338879696163109573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 33522955570345856434958861 12571108338879696163109573)
          ·
            refine ⟨2357082813539943030583045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 12571108338879696163109573 2357082813539943030583045)
            ·
              refine ⟨441953027538739318234321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2357082813539943030583045 441953027538739318234321)
              ·
                refine ⟨331464770654054488675741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 441953027538739318234321 331464770654054488675741)
                ·
                  refine ⟨124299288995270433253403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 331464770654054488675741 124299288995270433253403)
                  ·
                    rfl

theorem cell20_272331_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 4, 2, 3].length) (baseStart_272331 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_272331 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_272331 prefixEnd_272331 := by exact prefixLift 272331
  have htrace : WordTrace (prefixWord ++ tailWord_272331) baseStart_272331 baseEnd_272331 := by
    simpa [prefixWord, tailWord_272331, baseEnd_272331] using wordTrace_append hprefix tailTrace_272331
  have hstable : (prefixWord ++ tailWord_272331).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_272331).length < 2 ^ (prefixWord ++ tailWord_272331).sum := by decide
  have hdescent : baseEnd_272331 < baseStart_272331 := by decide
  rcases family_descends (prefixWord ++ tailWord_272331) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_272362 : List Nat := [3, 1, 3, 1, 2, 1, 5, 4]
def baseStart_272362 : Nat := 118140960795 + 272362 * 2 ^ 59
def prefixEnd_272362 : Nat := 4983230072969 + 3 ^ 40 * 272362 * 2
def baseEnd_272362 : Nat := 41437812746657367739981

theorem tailTrace_272362 : CollatzResearch.WordTrace tailWord_272362 prefixEnd_272362 41437812746657367739981 := by
  unfold tailWord_272362
  simp only [CollatzResearch.WordTrace]
  refine ⟨2483464559821616142850835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6622572159524309714268893 2483464559821616142850835)
  ·
    refine ⟨3725196839732424214276253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2483464559821616142850835 3725196839732424214276253)
    ·
      refine ⟨1396948814899659080353595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3725196839732424214276253 1396948814899659080353595)
      ·
        refine ⟨2095423222349488620530393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1396948814899659080353595 2095423222349488620530393)
        ·
          refine ⟨1571567416762116465397795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2095423222349488620530393 1571567416762116465397795)
          ·
            refine ⟨2357351125143174698096693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1571567416762116465397795 2357351125143174698096693)
            ·
              refine ⟨221001667982172627946565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 2357351125143174698096693 221001667982172627946565)
              ·
                refine ⟨41437812746657367739981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 221001667982172627946565 41437812746657367739981)
                ·
                  rfl

theorem cell20_272362_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 5, 4].length) (baseStart_272362 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_272362 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_272362 prefixEnd_272362 := by exact prefixLift 272362
  have htrace : WordTrace (prefixWord ++ tailWord_272362) baseStart_272362 baseEnd_272362 := by
    simpa [prefixWord, tailWord_272362, baseEnd_272362] using wordTrace_append hprefix tailTrace_272362
  have hstable : (prefixWord ++ tailWord_272362).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_272362).length < 2 ^ (prefixWord ++ tailWord_272362).sum := by decide
  have hdescent : baseEnd_272362 < baseStart_272362 := by decide
  rcases family_descends (prefixWord ++ tailWord_272362) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_272417 : List Nat := [1, 2, 3, 2, 4, 2, 2, 4]
def baseStart_272417 : Nat := 118140960795 + 272417 * 2 ^ 59
def prefixEnd_272417 : Nat := 4983230072969 + 3 ^ 40 * 272417 * 2
def baseEnd_272417 : Nat := 41446180579545452128795

theorem tailTrace_272417 : CollatzResearch.WordTrace tailWord_272417 prefixEnd_272417 41446180579545452128795 := by
  unfold tailWord_272417
  simp only [CollatzResearch.WordTrace]
  refine ⟨9935864254087208964655505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6623909502724805976437003 9935864254087208964655505)
  ·
    refine ⟨7451898190565406723491629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9935864254087208964655505 7451898190565406723491629)
    ·
      refine ⟨2794461821462027521309361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7451898190565406723491629 2794461821462027521309361)
      ·
        refine ⟨2095846366096520640982021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2794461821462027521309361 2095846366096520640982021)
        ·
          refine ⟨392971193643097620184129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2095846366096520640982021 392971193643097620184129)
          ·
            refine ⟨294728395232323215138097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 392971193643097620184129 294728395232323215138097)
            ·
              refine ⟨221046296424242411353573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 294728395232323215138097 221046296424242411353573)
              ·
                refine ⟨41446180579545452128795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 221046296424242411353573 41446180579545452128795)
                ·
                  rfl

theorem cell20_272417_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 4, 2, 2, 4].length) (baseStart_272417 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_272417 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_272417 prefixEnd_272417 := by exact prefixLift 272417
  have htrace : WordTrace (prefixWord ++ tailWord_272417) baseStart_272417 baseEnd_272417 := by
    simpa [prefixWord, tailWord_272417, baseEnd_272417] using wordTrace_append hprefix tailTrace_272417
  have hstable : (prefixWord ++ tailWord_272417).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_272417).length < 2 ^ (prefixWord ++ tailWord_272417).sum := by decide
  have hdescent : baseEnd_272417 < baseStart_272417 := by decide
  rcases family_descends (prefixWord ++ tailWord_272417) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_272421 : List Nat := [1, 3, 1, 2, 2, 4, 1, 6]
def baseStart_272421 : Nat := 118140960795 + 272421 * 2 ^ 59
def prefixEnd_272421 : Nat := 4983230072969 + 3 ^ 40 * 272421 * 2
def baseEnd_272421 : Nat := 41446789149210040084345

theorem tailTrace_272421 : CollatzResearch.WordTrace tailWord_272421 prefixEnd_272421 41446789149210040084345 := by
  unfold tailWord_272421
  simp only [CollatzResearch.WordTrace]
  refine ⟨9936010146072717647801117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6624006764048478431867411 9936010146072717647801117)
  ·
    refine ⟨3726003804777269117925419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9936010146072717647801117 3726003804777269117925419)
    ·
      refine ⟨5589005707165903676888129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3726003804777269117925419 5589005707165903676888129)
      ·
        refine ⟨4191754280374427757666097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5589005707165903676888129 4191754280374427757666097)
        ·
          refine ⟨3143815710280820818249573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4191754280374427757666097 3143815710280820818249573)
          ·
            refine ⟨589465445677653903421795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3143815710280820818249573 589465445677653903421795)
            ·
              refine ⟨884198168516480855132693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 589465445677653903421795 884198168516480855132693)
              ·
                refine ⟨41446789149210040084345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 884198168516480855132693 41446789149210040084345)
                ·
                  rfl

theorem cell20_272421_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 4, 1, 6].length) (baseStart_272421 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_272421 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_272421 prefixEnd_272421 := by exact prefixLift 272421
  have htrace : WordTrace (prefixWord ++ tailWord_272421) baseStart_272421 baseEnd_272421 := by
    simpa [prefixWord, tailWord_272421, baseEnd_272421] using wordTrace_append hprefix tailTrace_272421
  have hstable : (prefixWord ++ tailWord_272421).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_272421).length < 2 ^ (prefixWord ++ tailWord_272421).sum := by decide
  have hdescent : baseEnd_272421 < baseStart_272421 := by decide
  rcases family_descends (prefixWord ++ tailWord_272421) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_272435 : List Nat := [1, 1, 1, 2, 4, 1, 2, 2, 6]
def baseStart_272435 : Nat := 118140960795 + 272435 * 2 ^ 59
def prefixEnd_272435 : Nat := 4983230072969 + 3 ^ 40 * 272435 * 2
def baseEnd_272435 : Nat := 124346757429108293786311

theorem tailTrace_272435 : CollatzResearch.WordTrace tailWord_272435 prefixEnd_272435 124346757429108293786311 := by
  unfold tailWord_272435
  simp only [CollatzResearch.WordTrace]
  refine ⟨9936520768021998038810759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6624347178681332025873839 9936520768021998038810759)
  ·
    refine ⟨14904781152032997058216139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9936520768021998038810759 14904781152032997058216139)
    ·
      refine ⟨22357171728049495587324209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14904781152032997058216139 22357171728049495587324209)
      ·
        refine ⟨16767878796037121690493157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22357171728049495587324209 16767878796037121690493157)
        ·
          refine ⟨3143977274256960316967467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 16767878796037121690493157 3143977274256960316967467)
          ·
            refine ⟨4715965911385440475451201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3143977274256960316967467 4715965911385440475451201)
            ·
              refine ⟨3536974433539080356588401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4715965911385440475451201 3536974433539080356588401)
              ·
                refine ⟨2652730825154310267441301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3536974433539080356588401 2652730825154310267441301)
                ·
                  refine ⟨124346757429108293786311, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2652730825154310267441301 124346757429108293786311)
                  ·
                    rfl

theorem cell20_272435_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 2, 2, 6].length) (baseStart_272435 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_272435 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_272435 prefixEnd_272435 := by exact prefixLift 272435
  have htrace : WordTrace (prefixWord ++ tailWord_272435) baseStart_272435 baseEnd_272435 := by
    simpa [prefixWord, tailWord_272435, baseEnd_272435] using wordTrace_append hprefix tailTrace_272435
  have hstable : (prefixWord ++ tailWord_272435).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_272435).length < 2 ^ (prefixWord ++ tailWord_272435).sum := by decide
  have hdescent : baseEnd_272435 < baseStart_272435 := by decide
  rcases family_descends (prefixWord ++ tailWord_272435) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_272445 : List Nat := [1, 4, 1, 3, 1, 1, 2, 4, 3]
def baseStart_272445 : Nat := 118140960795 + 272445 * 2 ^ 59
def prefixEnd_272445 : Nat := 4983230072969 + 3 ^ 40 * 272445 * 2
def baseEnd_272445 : Nat := 124351321701592703452937

theorem tailTrace_272445 : CollatzResearch.WordTrace tailWord_272445 prefixEnd_272445 124351321701592703452937 := by
  unfold tailWord_272445
  simp only [CollatzResearch.WordTrace]
  refine ⟨9936885497985769746674789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6624590331990513164449859 9936885497985769746674789)
  ·
    refine ⟨1863166030872331827501523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 9936885497985769746674789 1863166030872331827501523)
    ·
      refine ⟨2794749046308497741252285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1863166030872331827501523 2794749046308497741252285)
      ·
        refine ⟨1048030892365686652969607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2794749046308497741252285 1048030892365686652969607)
        ·
          refine ⟨1572046338548529979454411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1048030892365686652969607 1572046338548529979454411)
          ·
            refine ⟨2358069507822794969181617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1572046338548529979454411 2358069507822794969181617)
            ·
              refine ⟨1768552130867096226886213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2358069507822794969181617 1768552130867096226886213)
              ·
                refine ⟨331603524537580542541165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1768552130867096226886213 331603524537580542541165)
                ·
                  refine ⟨124351321701592703452937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 331603524537580542541165 124351321701592703452937)
                  ·
                    rfl

theorem cell20_272445_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 2, 4, 3].length) (baseStart_272445 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_272445 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_272445 prefixEnd_272445 := by exact prefixLift 272445
  have htrace : WordTrace (prefixWord ++ tailWord_272445) baseStart_272445 baseEnd_272445 := by
    simpa [prefixWord, tailWord_272445, baseEnd_272445] using wordTrace_append hprefix tailTrace_272445
  have hstable : (prefixWord ++ tailWord_272445).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_272445).length < 2 ^ (prefixWord ++ tailWord_272445).sum := by decide
  have hdescent : baseEnd_272445 < baseStart_272445 := by decide
  rcases family_descends (prefixWord ++ tailWord_272445) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_272448 : List Nat := [2, 1, 1, 2, 2, 5, 3, 2, 2]
def baseStart_272448 : Nat := 118140960795 + 272448 * 2 ^ 59
def prefixEnd_272448 : Nat := 4983230072969 + 3 ^ 40 * 272448 * 2
def baseEnd_272448 : Nat := 124352690983338026352925

theorem tailTrace_272448 : CollatzResearch.WordTrace tailWord_272448 prefixEnd_272448 124352690983338026352925 := by
  unfold tailWord_272448
  simp only [CollatzResearch.WordTrace]
  refine ⟨4968497458487450629516999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6624663277983267506022665 4968497458487450629516999)
  ·
    refine ⟨7452746187731175944275499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4968497458487450629516999 7452746187731175944275499)
    ·
      refine ⟨11179119281596763916413249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7452746187731175944275499 11179119281596763916413249)
      ·
        refine ⟨8384339461197572937309937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11179119281596763916413249 8384339461197572937309937)
        ·
          refine ⟨6288254595898179702982453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8384339461197572937309937 6288254595898179702982453)
          ·
            refine ⟨589523868365454347154605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 6288254595898179702982453 589523868365454347154605)
            ·
              refine ⟨221071450637045380182977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 589523868365454347154605 221071450637045380182977)
              ·
                refine ⟨165803587977784035137233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 221071450637045380182977 165803587977784035137233)
                ·
                  refine ⟨124352690983338026352925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 165803587977784035137233 124352690983338026352925)
                  ·
                    rfl

theorem cell20_272448_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 5, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 5, 3, 2, 2].length) (baseStart_272448 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_272448 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_272448 prefixEnd_272448 := by exact prefixLift 272448
  have htrace : WordTrace (prefixWord ++ tailWord_272448) baseStart_272448 baseEnd_272448 := by
    simpa [prefixWord, tailWord_272448, baseEnd_272448] using wordTrace_append hprefix tailTrace_272448
  have hstable : (prefixWord ++ tailWord_272448).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_272448).length < 2 ^ (prefixWord ++ tailWord_272448).sum := by decide
  have hdescent : baseEnd_272448 < baseStart_272448 := by decide
  rcases family_descends (prefixWord ++ tailWord_272448) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_272462 : List Nat := [4, 1, 1, 1, 1, 4, 4, 1, 3]
def baseStart_272462 : Nat := 118140960795 + 272462 * 2 ^ 59
def prefixEnd_272462 : Nat := 4983230072969 + 3 ^ 40 * 272462 * 2
def baseEnd_272462 : Nat := 124359080964816199886201

theorem tailTrace_272462 : CollatzResearch.WordTrace tailWord_272462 prefixEnd_272462 124359080964816199886201 := by
  unfold tailWord_272462
  simp only [CollatzResearch.WordTrace]
  refine ⟨1242188192365522706255455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 6625003692616121100029093 1242188192365522706255455)
  ·
    refine ⟨1863282288548284059383183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1242188192365522706255455 1863282288548284059383183)
    ·
      refine ⟨2794923432822426089074775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1863282288548284059383183 2794923432822426089074775)
      ·
        refine ⟨4192385149233639133612163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2794923432822426089074775 4192385149233639133612163)
        ·
          refine ⟨6288577723850458700418245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4192385149233639133612163 6288577723850458700418245)
          ·
            refine ⟨1179108323221961006328421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 6288577723850458700418245 1179108323221961006328421)
            ·
              refine ⟨221082810604117688686579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1179108323221961006328421 221082810604117688686579)
              ·
                refine ⟨331624215906176533029869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 221082810604117688686579 331624215906176533029869)
                ·
                  refine ⟨124359080964816199886201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 331624215906176533029869 124359080964816199886201)
                  ·
                    rfl

theorem cell20_272462_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 4, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 4, 4, 1, 3].length) (baseStart_272462 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_272462 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_272462 prefixEnd_272462 := by exact prefixLift 272462
  have htrace : WordTrace (prefixWord ++ tailWord_272462) baseStart_272462 baseEnd_272462 := by
    simpa [prefixWord, tailWord_272462, baseEnd_272462] using wordTrace_append hprefix tailTrace_272462
  have hstable : (prefixWord ++ tailWord_272462).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_272462).length < 2 ^ (prefixWord ++ tailWord_272462).sum := by decide
  have hdescent : baseEnd_272462 < baseStart_272462 := by decide
  rcases family_descends (prefixWord ++ tailWord_272462) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_272473 : List Nat := [1, 2, 1, 2, 2, 1, 4, 1, 6]
def baseStart_272473 : Nat := 118140960795 + 272473 * 2 ^ 59
def prefixEnd_272473 : Nat := 4983230072969 + 3 ^ 40 * 272473 * 2
def baseEnd_272473 : Nat := 124364101664549050519489

theorem tailTrace_272473 : CollatzResearch.WordTrace tailWord_272473 prefixEnd_272473 124364101664549050519489 := by
  unfold tailWord_272473
  simp only [CollatzResearch.WordTrace]
  refine ⟨9937906741884330528694073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6625271161256220352462715 9937906741884330528694073)
  ·
    refine ⟨7453430056413247896520555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9937906741884330528694073 7453430056413247896520555)
    ·
      refine ⟨11180145084619871844780833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7453430056413247896520555 11180145084619871844780833)
      ·
        refine ⟨8385108813464903883585625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11180145084619871844780833 8385108813464903883585625)
        ·
          refine ⟨6288831610098677912689219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8385108813464903883585625 6288831610098677912689219)
          ·
            refine ⟨9433247415148016869033829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6288831610098677912689219 9433247415148016869033829)
            ·
              refine ⟨1768733890340253162943843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9433247415148016869033829 1768733890340253162943843)
              ·
                refine ⟨2653100835510379744415765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1768733890340253162943843 2653100835510379744415765)
                ·
                  refine ⟨124364101664549050519489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2653100835510379744415765 124364101664549050519489)
                  ·
                    rfl

theorem cell20_272473_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 4, 1, 6].length) (baseStart_272473 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_272473 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_272473 prefixEnd_272473 := by exact prefixLift 272473
  have htrace : WordTrace (prefixWord ++ tailWord_272473) baseStart_272473 baseEnd_272473 := by
    simpa [prefixWord, tailWord_272473, baseEnd_272473] using wordTrace_append hprefix tailTrace_272473
  have hstable : (prefixWord ++ tailWord_272473).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_272473).length < 2 ^ (prefixWord ++ tailWord_272473).sum := by decide
  have hdescent : baseEnd_272473 < baseStart_272473 := by decide
  rcases family_descends (prefixWord ++ tailWord_272473) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_272545 : List Nat := [1, 2, 3, 3, 1, 2, 1, 5, 2]
def baseStart_272545 : Nat := 118140960795 + 272545 * 2 ^ 59
def prefixEnd_272545 : Nat := 4983230072969 + 3 ^ 40 * 272545 * 2
def baseEnd_272545 : Nat := 124396964426436800119195

theorem tailTrace_272545 : CollatzResearch.WordTrace tailWord_272545 prefixEnd_272545 124396964426436800119195 := by
  unfold tailWord_272545
  simp only [CollatzResearch.WordTrace]
  refine ⟨9940532797623486825315089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6627021865082324550210059 9940532797623486825315089)
  ·
    refine ⟨7455399598217615118986317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9940532797623486825315089 7455399598217615118986317)
    ·
      refine ⟨2795774849331605669619869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7455399598217615118986317 2795774849331605669619869)
      ·
        refine ⟨1048415568499352126107451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2795774849331605669619869 1048415568499352126107451)
        ·
          refine ⟨1572623352749028189161177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1048415568499352126107451 1572623352749028189161177)
          ·
            refine ⟨1179467514561771141870883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1572623352749028189161177 1179467514561771141870883)
            ·
              refine ⟨1769201271842656712806325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1179467514561771141870883 1769201271842656712806325)
              ·
                refine ⟨165862619235249066825593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1769201271842656712806325 165862619235249066825593)
                ·
                  refine ⟨124396964426436800119195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 165862619235249066825593 124396964426436800119195)
                  ·
                    rfl

theorem cell20_272545_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 2, 1, 5, 2].length) (baseStart_272545 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_272545 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_272545 prefixEnd_272545 := by exact prefixLift 272545
  have htrace : WordTrace (prefixWord ++ tailWord_272545) baseStart_272545 baseEnd_272545 := by
    simpa [prefixWord, tailWord_272545, baseEnd_272545] using wordTrace_append hprefix tailTrace_272545
  have hstable : (prefixWord ++ tailWord_272545).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_272545).length < 2 ^ (prefixWord ++ tailWord_272545).sum := by decide
  have hdescent : baseEnd_272545 < baseStart_272545 := by decide
  rcases family_descends (prefixWord ++ tailWord_272545) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_272549 : List Nat := [1, 3, 1, 2, 1, 3, 1, 2, 6]
def baseStart_272549 : Nat := 118140960795 + 272549 * 2 ^ 59
def prefixEnd_272549 : Nat := 4983230072969 + 3 ^ 40 * 272549 * 2
def baseEnd_272549 : Nat := 124398790135430563985845

theorem tailTrace_272549 : CollatzResearch.WordTrace tailWord_272549 prefixEnd_272549 124398790135430563985845 := by
  unfold tailWord_272549
  simp only [CollatzResearch.WordTrace]
  refine ⟨9940678689608995508460701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6627119126405997005640467 9940678689608995508460701)
  ·
    refine ⟨3727754508603373315672763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9940678689608995508460701 3727754508603373315672763)
    ·
      refine ⟨5591631762905059973509145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3727754508603373315672763 5591631762905059973509145)
      ·
        refine ⟨4193723822178794980131859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5591631762905059973509145 4193723822178794980131859)
        ·
          refine ⟨6290585733268192470197789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4193723822178794980131859 6290585733268192470197789)
          ·
            refine ⟨2358969649975572176324171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6290585733268192470197789 2358969649975572176324171)
            ·
              refine ⟨3538454474963358264486257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2358969649975572176324171 3538454474963358264486257)
              ·
                refine ⟨2653840856222518698364693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3538454474963358264486257 2653840856222518698364693)
                ·
                  refine ⟨124398790135430563985845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2653840856222518698364693 124398790135430563985845)
                  ·
                    rfl

theorem cell20_272549_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 1, 2, 6].length) (baseStart_272549 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_272549 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_272549 prefixEnd_272549 := by exact prefixLift 272549
  have htrace : WordTrace (prefixWord ++ tailWord_272549) baseStart_272549 baseEnd_272549 := by
    simpa [prefixWord, tailWord_272549, baseEnd_272549] using wordTrace_append hprefix tailTrace_272549
  have hstable : (prefixWord ++ tailWord_272549).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_272549).length < 2 ^ (prefixWord ++ tailWord_272549).sum := by decide
  have hdescent : baseEnd_272549 < baseStart_272549 := by decide
  rcases family_descends (prefixWord ++ tailWord_272549) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_272576 : List Nat := [2, 1, 1, 2, 5, 2, 3, 1, 3]
def baseStart_272576 : Nat := 118140960795 + 272576 * 2 ^ 59
def prefixEnd_272576 : Nat := 4983230072969 + 3 ^ 40 * 272576 * 2
def baseEnd_272576 : Nat := 124411113671138470085735

theorem tailTrace_272576 : CollatzResearch.WordTrace tailWord_272576 prefixEnd_272576 124411113671138470085735 := by
  unfold tailWord_272576
  simp only [CollatzResearch.WordTrace]
  refine ⟨4970831730255589559846791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6627775640340786079795721 4970831730255589559846791)
  ·
    refine ⟨7456247595383384339770187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4970831730255589559846791 7456247595383384339770187)
    ·
      refine ⟨11184371393075076509655281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7456247595383384339770187 11184371393075076509655281)
      ·
        refine ⟨8388278544806307382241461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11184371393075076509655281 8388278544806307382241461)
        ·
          refine ⟨786401113575591317085137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 8388278544806307382241461 786401113575591317085137)
          ·
            refine ⟨589800835181693487813853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 786401113575591317085137 589800835181693487813853)
            ·
              refine ⟨221175313193135057930195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 589800835181693487813853 221175313193135057930195)
              ·
                refine ⟨331762969789702586895293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 221175313193135057930195 331762969789702586895293)
                ·
                  refine ⟨124411113671138470085735, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 331762969789702586895293 124411113671138470085735)
                  ·
                    rfl

theorem cell20_272576_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 2, 3, 1, 3].length) (baseStart_272576 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_272576 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_272576 prefixEnd_272576 := by exact prefixLift 272576
  have htrace : WordTrace (prefixWord ++ tailWord_272576) baseStart_272576 baseEnd_272576 := by
    simpa [prefixWord, tailWord_272576, baseEnd_272576] using wordTrace_append hprefix tailTrace_272576
  have hstable : (prefixWord ++ tailWord_272576).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_272576).length < 2 ^ (prefixWord ++ tailWord_272576).sum := by decide
  have hdescent : baseEnd_272576 < baseStart_272576 := by decide
  rcases family_descends (prefixWord ++ tailWord_272576) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_272587 : List Nat := [1, 1, 1, 1, 3, 2, 3, 4, 4]
def baseStart_272587 : Nat := 118140960795 + 272587 * 2 ^ 59
def prefixEnd_272587 : Nat := 4983230072969 + 3 ^ 40 * 272587 * 2
def baseEnd_272587 : Nat := 124416134370871320719023

theorem tailTrace_272587 : CollatzResearch.WordTrace tailWord_272587 prefixEnd_272587 124416134370871320719023 := by
  unfold tailWord_272587
  simp only [CollatzResearch.WordTrace]
  refine ⟨9942064663471327998344015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6628043108980885332229343 9942064663471327998344015)
  ·
    refine ⟨14913096995206991997516023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9942064663471327998344015 14913096995206991997516023)
    ·
      refine ⟨22369645492810487996274035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14913096995206991997516023 22369645492810487996274035)
      ·
        refine ⟨33554468239215731994411053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22369645492810487996274035 33554468239215731994411053)
        ·
          refine ⟨12582925589705899497904145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 33554468239215731994411053 12582925589705899497904145)
          ·
            refine ⟨9437194192279424623428109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12582925589705899497904145 9437194192279424623428109)
            ·
              refine ⟨3538947822104784233785541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9437194192279424623428109 3538947822104784233785541)
              ·
                refine ⟨663552716644647043834789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3538947822104784233785541 663552716644647043834789)
                ·
                  refine ⟨124416134370871320719023, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 663552716644647043834789 124416134370871320719023)
                  ·
                    rfl

theorem cell20_272587_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 3, 4, 4].length) (baseStart_272587 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_272587 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_272587 prefixEnd_272587 := by exact prefixLift 272587
  have htrace : WordTrace (prefixWord ++ tailWord_272587) baseStart_272587 baseEnd_272587 := by
    simpa [prefixWord, tailWord_272587, baseEnd_272587] using wordTrace_append hprefix tailTrace_272587
  have hstable : (prefixWord ++ tailWord_272587).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_272587).length < 2 ^ (prefixWord ++ tailWord_272587).sum := by decide
  have hdescent : baseEnd_272587 < baseStart_272587 := by decide
  rcases family_descends (prefixWord ++ tailWord_272587) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_272590 : List Nat := [4, 1, 1, 1, 4, 1, 4, 4]
def baseStart_272590 : Nat := 118140960795 + 272590 * 2 ^ 59
def prefixEnd_272590 : Nat := 4983230072969 + 3 ^ 40 * 272590 * 2
def baseEnd_272590 : Nat := 41472501217538881206337

theorem tailTrace_272590 : CollatzResearch.WordTrace tailWord_272590 prefixEnd_272590 41472501217538881206337 := by
  unfold tailWord_272590
  simp only [CollatzResearch.WordTrace]
  refine ⟨1242771760307557438837903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 6628116054973639673802149 1242771760307557438837903)
  ·
    refine ⟨1864157640461336158256855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1242771760307557438837903 1864157640461336158256855)
    ·
      refine ⟨2796236460692004237385283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1864157640461336158256855 2796236460692004237385283)
      ·
        refine ⟨4194354691038006356077925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2796236460692004237385283 4194354691038006356077925)
        ·
          refine ⟨786441504569626191764611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4194354691038006356077925 786441504569626191764611)
          ·
            refine ⟨1179662256854439287646917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 786441504569626191764611 1179662256854439287646917)
            ·
              refine ⟨221186673160207366433797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1179662256854439287646917 221186673160207366433797)
              ·
                refine ⟨41472501217538881206337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 221186673160207366433797 41472501217538881206337)
                ·
                  rfl

theorem cell20_272590_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 1, 4, 4].length) (baseStart_272590 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_272590 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_272590 prefixEnd_272590 := by exact prefixLift 272590
  have htrace : WordTrace (prefixWord ++ tailWord_272590) baseStart_272590 baseEnd_272590 := by
    simpa [prefixWord, tailWord_272590, baseEnd_272590] using wordTrace_append hprefix tailTrace_272590
  have hstable : (prefixWord ++ tailWord_272590).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_272590).length < 2 ^ (prefixWord ++ tailWord_272590).sum := by decide
  have hdescent : baseEnd_272590 < baseStart_272590 := by decide
  rcases family_descends (prefixWord ++ tailWord_272590) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_272600 : List Nat := [2, 1, 2, 2, 4, 3, 1, 3, 2]
def baseStart_272600 : Nat := 118140960795 + 272600 * 2 ^ 59
def prefixEnd_272600 : Nat := 4983230072969 + 3 ^ 40 * 272600 * 2
def baseEnd_272600 : Nat := 124422067925101053285637

theorem tailTrace_272600 : CollatzResearch.WordTrace tailWord_272600 prefixEnd_272600 124422067925101053285637 := by
  unfold tailWord_272600
  simp only [CollatzResearch.WordTrace]
  refine ⟨4971269406212115609283627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6628359208282820812378169 4971269406212115609283627)
  ·
    refine ⟨7456904109318173413925441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4971269406212115609283627 7456904109318173413925441)
    ·
      refine ⟨5592678081988630060444081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7456904109318173413925441 5592678081988630060444081)
      ·
        refine ⟨4194508561491472545333061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5592678081988630060444081 4194508561491472545333061)
        ·
          refine ⟨786470355279651102249949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4194508561491472545333061 786470355279651102249949)
          ·
            refine ⟨294926383229869163343731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 786470355279651102249949 294926383229869163343731)
            ·
              refine ⟨442389574844803745015597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 294926383229869163343731 442389574844803745015597)
              ·
                refine ⟨165896090566801404380849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 442389574844803745015597 165896090566801404380849)
                ·
                  refine ⟨124422067925101053285637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 165896090566801404380849 124422067925101053285637)
                  ·
                    rfl

theorem cell20_272600_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 3, 1, 3, 2].length) (baseStart_272600 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_272600 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_272600 prefixEnd_272600 := by exact prefixLift 272600
  have htrace : WordTrace (prefixWord ++ tailWord_272600) baseStart_272600 baseEnd_272600 := by
    simpa [prefixWord, tailWord_272600, baseEnd_272600] using wordTrace_append hprefix tailTrace_272600
  have hstable : (prefixWord ++ tailWord_272600).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_272600).length < 2 ^ (prefixWord ++ tailWord_272600).sum := by decide
  have hdescent : baseEnd_272600 < baseStart_272600 := by decide
  rcases family_descends (prefixWord ++ tailWord_272600) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_272618 : List Nat := [3, 1, 3, 1, 1, 2, 1, 3, 5]
def baseStart_272618 : Nat := 118140960795 + 272618 * 2 ^ 59
def prefixEnd_272618 : Nat := 4983230072969 + 3 ^ 40 * 272618 * 2
def baseEnd_272618 : Nat := 124430283615572990685563

theorem tailTrace_272618 : CollatzResearch.WordTrace tailWord_272618 prefixEnd_272618 124430283615572990685563 := by
  unfold tailWord_272618
  simp only [CollatzResearch.WordTrace]
  refine ⟨2485798831589755073180627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6628796884239346861815005 2485798831589755073180627)
  ·
    refine ⟨3728698247384632609770941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2485798831589755073180627 3728698247384632609770941)
    ·
      refine ⟨1398261842769237228664103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3728698247384632609770941 1398261842769237228664103)
      ·
        refine ⟨2097392764153855842996155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1398261842769237228664103 2097392764153855842996155)
        ·
          refine ⟨3146089146230783764494233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2097392764153855842996155 3146089146230783764494233)
          ·
            refine ⟨2359566859673087823370675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3146089146230783764494233 2359566859673087823370675)
            ·
              refine ⟨3539350289509631735056013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2359566859673087823370675 3539350289509631735056013)
              ·
                refine ⟨1327256358566111900646005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3539350289509631735056013 1327256358566111900646005)
                ·
                  refine ⟨124430283615572990685563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1327256358566111900646005 124430283615572990685563)
                  ·
                    rfl

theorem cell20_272618_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 1, 3, 5].length) (baseStart_272618 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_272618 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_272618 prefixEnd_272618 := by exact prefixLift 272618
  have htrace : WordTrace (prefixWord ++ tailWord_272618) baseStart_272618 baseEnd_272618 := by
    simpa [prefixWord, tailWord_272618, baseEnd_272618] using wordTrace_append hprefix tailTrace_272618
  have hstable : (prefixWord ++ tailWord_272618).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_272618).length < 2 ^ (prefixWord ++ tailWord_272618).sum := by decide
  have hdescent : baseEnd_272618 < baseStart_272618 := by decide
  rcases family_descends (prefixWord ++ tailWord_272618) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_272676 : List Nat := [2, 3, 1, 3, 1, 2, 4, 2, 2]
def baseStart_272676 : Nat := 118140960795 + 272676 * 2 ^ 59
def prefixEnd_272676 : Nat := 4983230072969 + 3 ^ 40 * 272676 * 2
def baseEnd_272676 : Nat := 124456756395982566751993

theorem tailTrace_272676 : CollatzResearch.WordTrace tailWord_272676 prefixEnd_272676 124456756395982566751993 := by
  unfold tailWord_272676
  simp only [CollatzResearch.WordTrace]
  refine ⟨4972655380074448099166941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6630207173432597465555921 4972655380074448099166941)
  ·
    refine ⟨1864745767527918037187603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4972655380074448099166941 1864745767527918037187603)
    ·
      refine ⟨2797118651291877055781405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1864745767527918037187603 2797118651291877055781405)
      ·
        refine ⟨1048919494234453895918027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2797118651291877055781405 1048919494234453895918027)
        ·
          refine ⟨1573379241351680843877041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1048919494234453895918027 1573379241351680843877041)
          ·
            refine ⟨1180034431013760632907781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1573379241351680843877041 1180034431013760632907781)
            ·
              refine ⟨221256455815080118670209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1180034431013760632907781 221256455815080118670209)
              ·
                refine ⟨165942341861310089002657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 221256455815080118670209 165942341861310089002657)
                ·
                  refine ⟨124456756395982566751993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 165942341861310089002657 124456756395982566751993)
                  ·
                    rfl

theorem cell20_272676_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 2, 4, 2, 2].length) (baseStart_272676 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_272676 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_272676 prefixEnd_272676 := by exact prefixLift 272676
  have htrace : WordTrace (prefixWord ++ tailWord_272676) baseStart_272676 baseEnd_272676 := by
    simpa [prefixWord, tailWord_272676, baseEnd_272676] using wordTrace_append hprefix tailTrace_272676
  have hstable : (prefixWord ++ tailWord_272676).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_272676).length < 2 ^ (prefixWord ++ tailWord_272676).sum := by decide
  have hdescent : baseEnd_272676 < baseStart_272676 := by decide
  rcases family_descends (prefixWord ++ tailWord_272676) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_272679 : List Nat := [1, 1, 8, 1, 2, 1, 1, 5]
def baseStart_272679 : Nat := 118140960795 + 272679 * 2 ^ 59
def prefixEnd_272679 : Nat := 4983230072969 + 3 ^ 40 * 272679 * 2
def baseEnd_272679 : Nat := 41486041892575963217327

theorem tailTrace_272679 : CollatzResearch.WordTrace tailWord_272679 prefixEnd_272679 41486041892575963217327 := by
  unfold tailWord_272679
  simp only [CollatzResearch.WordTrace]
  refine ⟨9945420179138027710693091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6630280119425351807128727 9945420179138027710693091)
  ·
    refine ⟨14918130268707041566039637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9945420179138027710693091 14918130268707041566039637)
    ·
      refine ⟨174821839086410643352027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 8 14918130268707041566039637 174821839086410643352027)
      ·
        refine ⟨262232758629615965028041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 174821839086410643352027 262232758629615965028041)
        ·
          refine ⟨196674568972211973771031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 262232758629615965028041 196674568972211973771031)
          ·
            refine ⟨295011853458317960656547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 196674568972211973771031 295011853458317960656547)
            ·
              refine ⟨442517780187476940984821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 295011853458317960656547 442517780187476940984821)
              ·
                refine ⟨41486041892575963217327, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 442517780187476940984821 41486041892575963217327)
                ·
                  rfl

theorem cell20_272679_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 8, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 8, 1, 2, 1, 1, 5].length) (baseStart_272679 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_272679 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_272679 prefixEnd_272679 := by exact prefixLift 272679
  have htrace : WordTrace (prefixWord ++ tailWord_272679) baseStart_272679 baseEnd_272679 := by
    simpa [prefixWord, tailWord_272679, baseEnd_272679] using wordTrace_append hprefix tailTrace_272679
  have hstable : (prefixWord ++ tailWord_272679).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_272679).length < 2 ^ (prefixWord ++ tailWord_272679).sum := by decide
  have hdescent : baseEnd_272679 < baseStart_272679 := by decide
  rcases family_descends (prefixWord ++ tailWord_272679) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_272725 : List Nat := [1, 3, 2, 2, 4, 1, 7]
def baseStart_272725 : Nat := 118140960795 + 272725 * 2 ^ 59
def prefixEnd_272725 : Nat := 4983230072969 + 3 ^ 40 * 272725 * 2
def baseEnd_272725 : Nat := 13831013481239574902051

theorem tailTrace_272725 : CollatzResearch.WordTrace tailWord_272725 prefixEnd_272725 13831013481239574902051 := by
  unfold tailWord_272725
  simp only [CollatzResearch.WordTrace]
  refine ⟨9947097936971377566867629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6631398624647585044578419 9947097936971377566867629)
  ·
    refine ⟨3730161726364266587575361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9947097936971377566867629 3730161726364266587575361)
    ·
      refine ⟨2797621294773199940681521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3730161726364266587575361 2797621294773199940681521)
      ·
        refine ⟨2098215971079899955511141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2797621294773199940681521 2098215971079899955511141)
        ·
          refine ⟨393415494577481241658339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2098215971079899955511141 393415494577481241658339)
          ·
            refine ⟨590123241866221862487509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 393415494577481241658339 590123241866221862487509)
            ·
              refine ⟨13831013481239574902051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 590123241866221862487509 13831013481239574902051)
              ·
                rfl

theorem cell20_272725_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 4, 1, 7].length) (baseStart_272725 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_272725 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_272725 prefixEnd_272725 := by exact prefixLift 272725
  have htrace : WordTrace (prefixWord ++ tailWord_272725) baseStart_272725 baseEnd_272725 := by
    simpa [prefixWord, tailWord_272725, baseEnd_272725] using wordTrace_append hprefix tailTrace_272725
  have hstable : (prefixWord ++ tailWord_272725).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_272725).length < 2 ^ (prefixWord ++ tailWord_272725).sum := by decide
  have hdescent : baseEnd_272725 < baseStart_272725 := by decide
  rcases family_descends (prefixWord ++ tailWord_272725) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_272763 : List Nat := [1, 1, 1, 1, 1, 7, 4, 4]
def baseStart_272763 : Nat := 118140960795 + 272763 * 2 ^ 59
def prefixEnd_272763 : Nat := 4983230072969 + 3 ^ 40 * 272763 * 2
def baseEnd_272763 : Nat := 41498821855532310283879

theorem tailTrace_272763 : CollatzResearch.WordTrace tailWord_272763 prefixEnd_272763 41498821855532310283879 := by
  unfold tailWord_272763
  simp only [CollatzResearch.WordTrace]
  refine ⟨9948483910833710056750943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6632322607222473371167295 9948483910833710056750943)
  ·
    refine ⟨14922725866250565085126415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9948483910833710056750943 14922725866250565085126415)
    ·
      refine ⟨22384088799375847627689623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14922725866250565085126415 22384088799375847627689623)
      ·
        refine ⟨33576133199063771441534435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22384088799375847627689623 33576133199063771441534435)
        ·
          refine ⟨50364199798595657162301653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33576133199063771441534435 50364199798595657162301653)
          ·
            refine ⟨1180410932779585714741445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 50364199798595657162301653 1180410932779585714741445)
            ·
              refine ⟨221327049896172321514021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1180410932779585714741445 221327049896172321514021)
              ·
                refine ⟨41498821855532310283879, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 221327049896172321514021 41498821855532310283879)
                ·
                  rfl

theorem cell20_272763_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 7, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 7, 4, 4].length) (baseStart_272763 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_272763 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_272763 prefixEnd_272763 := by exact prefixLift 272763
  have htrace : WordTrace (prefixWord ++ tailWord_272763) baseStart_272763 baseEnd_272763 := by
    simpa [prefixWord, tailWord_272763, baseEnd_272763] using wordTrace_append hprefix tailTrace_272763
  have hstable : (prefixWord ++ tailWord_272763).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_272763).length < 2 ^ (prefixWord ++ tailWord_272763).sum := by decide
  have hdescent : baseEnd_272763 < baseStart_272763 := by decide
  rcases family_descends (prefixWord ++ tailWord_272763) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_272794 : List Nat := [3, 1, 1, 4, 1, 2, 3, 1, 4]
def baseStart_272794 : Nat := 118140960795 + 272794 * 2 ^ 59
def prefixEnd_272794 : Nat := 4983230072969 + 3 ^ 40 * 272794 * 2
def baseEnd_272794 : Nat := 124510614811298600818177

theorem tailTrace_272794 : CollatzResearch.WordTrace tailWord_272794 prefixEnd_272794 124510614811298600818177 := by
  unfold tailWord_272794
  simp only [CollatzResearch.WordTrace]
  refine ⟨2487403643430350587782359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6633076382480934900752957 2487403643430350587782359)
  ·
    refine ⟨3731105465145525881673539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2487403643430350587782359 3731105465145525881673539)
    ·
      refine ⟨5596658197718288822510309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3731105465145525881673539 5596658197718288822510309)
      ·
        refine ⟨1049373412072179154220683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 5596658197718288822510309 1049373412072179154220683)
        ·
          refine ⟨1574060118108268731331025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1049373412072179154220683 1574060118108268731331025)
          ·
            refine ⟨1180545088581201548498269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1574060118108268731331025 1180545088581201548498269)
            ·
              refine ⟨442704408217950580686851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1180545088581201548498269 442704408217950580686851)
              ·
                refine ⟨664056612326925871030277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 442704408217950580686851 664056612326925871030277)
                ·
                  refine ⟨124510614811298600818177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 664056612326925871030277 124510614811298600818177)
                  ·
                    rfl

theorem cell20_272794_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 2, 3, 1, 4].length) (baseStart_272794 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_272794 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_272794 prefixEnd_272794 := by exact prefixLift 272794
  have htrace : WordTrace (prefixWord ++ tailWord_272794) baseStart_272794 baseEnd_272794 := by
    simpa [prefixWord, tailWord_272794, baseEnd_272794] using wordTrace_append hprefix tailTrace_272794
  have hstable : (prefixWord ++ tailWord_272794).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_272794).length < 2 ^ (prefixWord ++ tailWord_272794).sum := by decide
  have hdescent : baseEnd_272794 < baseStart_272794 := by decide
  rcases family_descends (prefixWord ++ tailWord_272794) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_272832 : List Nat := [2, 1, 1, 2, 3, 1, 1, 7, 2]
def baseStart_272832 : Nat := 118140960795 + 272832 * 2 ^ 59
def prefixEnd_272832 : Nat := 4983230072969 + 3 ^ 40 * 272832 * 2
def baseEnd_272832 : Nat := 124527959046739357551355

theorem tailTrace_272832 : CollatzResearch.WordTrace tailWord_272832 prefixEnd_272832 124527959046739357551355 := by
  unfold tailWord_272832
  simp only [CollatzResearch.WordTrace]
  refine ⟨4975500273791867420506375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6634000365055823227341833 4975500273791867420506375)
  ·
    refine ⟨7463250410687801130759563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4975500273791867420506375 7463250410687801130759563)
    ·
      refine ⟨11194875616031701696139345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7463250410687801130759563 11194875616031701696139345)
      ·
        refine ⟨8396156712023776272104509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11194875616031701696139345 8396156712023776272104509)
        ·
          refine ⟨3148558767008916102039191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8396156712023776272104509 3148558767008916102039191)
          ·
            refine ⟨4722838150513374153058787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3148558767008916102039191 4722838150513374153058787)
            ·
              refine ⟨7084257225770061229588181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4722838150513374153058787 7084257225770061229588181)
              ·
                refine ⟨166037278728985810068473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 7084257225770061229588181 166037278728985810068473)
                ·
                  refine ⟨124527959046739357551355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 166037278728985810068473 124527959046739357551355)
                  ·
                    rfl

theorem cell20_272832_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 1, 7, 2].length) (baseStart_272832 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_272832 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_272832 prefixEnd_272832 := by exact prefixLift 272832
  have htrace : WordTrace (prefixWord ++ tailWord_272832) baseStart_272832 baseEnd_272832 := by
    simpa [prefixWord, tailWord_272832, baseEnd_272832] using wordTrace_append hprefix tailTrace_272832
  have hstable : (prefixWord ++ tailWord_272832).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_272832).length < 2 ^ (prefixWord ++ tailWord_272832).sum := by decide
  have hdescent : baseEnd_272832 < baseStart_272832 := by decide
  rcases family_descends (prefixWord ++ tailWord_272832) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_272866 : List Nat := [3, 3, 3, 2, 1, 1, 1, 2, 4]
def baseStart_272866 : Nat := 118140960795 + 272866 * 2 ^ 59
def prefixEnd_272866 : Nat := 4983230072969 + 3 ^ 40 * 272866 * 2
def baseEnd_272866 : Nat := 124543477573186350417883

theorem tailTrace_272866 : CollatzResearch.WordTrace tailWord_272866 prefixEnd_272866 124543477573186350417883 := by
  unfold tailWord_272866
  simp only [CollatzResearch.WordTrace]
  refine ⟨2488060157365139661937613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6634827086307039098500301 2488060157365139661937613)
  ·
    refine ⟨933022559011927373226605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2488060157365139661937613 933022559011927373226605)
    ·
      refine ⟨349883459629472764959977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 933022559011927373226605 349883459629472764959977)
      ·
        refine ⟨262412594722104573719983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 349883459629472764959977 262412594722104573719983)
        ·
          refine ⟨393618892083156860579975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 262412594722104573719983 393618892083156860579975)
          ·
            refine ⟨590428338124735290869963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 393618892083156860579975 590428338124735290869963)
            ·
              refine ⟨885642507187102936304945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 590428338124735290869963 885642507187102936304945)
              ·
                refine ⟨664231880390327202228709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 885642507187102936304945 664231880390327202228709)
                ·
                  refine ⟨124543477573186350417883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 664231880390327202228709 124543477573186350417883)
                  ·
                    rfl

theorem cell20_272866_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 2, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 2, 1, 1, 1, 2, 4].length) (baseStart_272866 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_272866 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_272866 prefixEnd_272866 := by exact prefixLift 272866
  have htrace : WordTrace (prefixWord ++ tailWord_272866) baseStart_272866 baseEnd_272866 := by
    simpa [prefixWord, tailWord_272866, baseEnd_272866] using wordTrace_append hprefix tailTrace_272866
  have hstable : (prefixWord ++ tailWord_272866).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_272866).length < 2 ^ (prefixWord ++ tailWord_272866).sum := by decide
  have hdescent : baseEnd_272866 < baseStart_272866 := by decide
  rcases family_descends (prefixWord ++ tailWord_272866) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_272908 : List Nat := [2, 2, 1, 2, 4, 2, 2, 1, 4]
def baseStart_272908 : Nat := 118140960795 + 272908 * 2 ^ 59
def prefixEnd_272908 : Nat := 4983230072969 + 3 ^ 40 * 272908 * 2
def baseEnd_272908 : Nat := 124562647517620871017711

theorem tailTrace_272908 : CollatzResearch.WordTrace tailWord_272908 prefixEnd_272908 124562647517620871017711 := by
  unfold tailWord_272908
  simp only [CollatzResearch.WordTrace]
  refine ⟨4976886247654199910389689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6635848330205599880519585 4976886247654199910389689)
  ·
    refine ⟨3732664685740649932792267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4976886247654199910389689 3732664685740649932792267)
    ·
      refine ⟨5598997028610974899188401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3732664685740649932792267 5598997028610974899188401)
      ·
        refine ⟨4199247771458231174391301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5598997028610974899188401 4199247771458231174391301)
        ·
          refine ⟨787358957148418345198369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4199247771458231174391301 787358957148418345198369)
          ·
            refine ⟨590519217861313758898777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 787358957148418345198369 590519217861313758898777)
            ·
              refine ⟨442889413395985319174083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 590519217861313758898777 442889413395985319174083)
              ·
                refine ⟨664334120093977978761125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 442889413395985319174083 664334120093977978761125)
                ·
                  refine ⟨124562647517620871017711, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 664334120093977978761125 124562647517620871017711)
                  ·
                    rfl

theorem cell20_272908_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 2, 2, 1, 4].length) (baseStart_272908 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_272908 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_272908 prefixEnd_272908 := by exact prefixLift 272908
  have htrace : WordTrace (prefixWord ++ tailWord_272908) baseStart_272908 baseEnd_272908 := by
    simpa [prefixWord, tailWord_272908, baseEnd_272908] using wordTrace_append hprefix tailTrace_272908
  have hstable : (prefixWord ++ tailWord_272908).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_272908).length < 2 ^ (prefixWord ++ tailWord_272908).sum := by decide
  have hdescent : baseEnd_272908 < baseStart_272908 := by decide
  rcases family_descends (prefixWord ++ tailWord_272908) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_272922 : List Nat := [3, 1, 1, 3, 1, 1, 2, 5, 3]
def baseStart_272922 : Nat := 118140960795 + 272922 * 2 ^ 59
def prefixEnd_272922 : Nat := 4983230072969 + 3 ^ 40 * 272922 * 2
def baseEnd_272922 : Nat := 124569037499099044550987

theorem tailTrace_272922 : CollatzResearch.WordTrace tailWord_272922 prefixEnd_272922 124569037499099044550987 := by
  unfold tailWord_272922
  simp only [CollatzResearch.WordTrace]
  refine ⟨2488570779314420052947255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6636188744838453474526013 2488570779314420052947255)
  ·
    refine ⟨3732856168971630079420883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2488570779314420052947255 3732856168971630079420883)
    ·
      refine ⟨5599284253457445119131325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3732856168971630079420883 5599284253457445119131325)
      ·
        refine ⟨2099731595046541919674247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5599284253457445119131325 2099731595046541919674247)
        ·
          refine ⟨3149597392569812879511371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2099731595046541919674247 3149597392569812879511371)
          ·
            refine ⟨4724396088854719319267057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3149597392569812879511371 4724396088854719319267057)
            ·
              refine ⟨3543297066641039489450293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4724396088854719319267057 3543297066641039489450293)
              ·
                refine ⟨332184099997597452135965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 3543297066641039489450293 332184099997597452135965)
                ·
                  refine ⟨124569037499099044550987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 332184099997597452135965 124569037499099044550987)
                  ·
                    rfl

theorem cell20_272922_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 2, 5, 3].length) (baseStart_272922 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_272922 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_272922 prefixEnd_272922 := by exact prefixLift 272922
  have htrace : WordTrace (prefixWord ++ tailWord_272922) baseStart_272922 baseEnd_272922 := by
    simpa [prefixWord, tailWord_272922, baseEnd_272922] using wordTrace_append hprefix tailTrace_272922
  have hstable : (prefixWord ++ tailWord_272922).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_272922).length < 2 ^ (prefixWord ++ tailWord_272922).sum := by decide
  have hdescent : baseEnd_272922 < baseStart_272922 := by decide
  rcases family_descends (prefixWord ++ tailWord_272922) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_272929 : List Nat := [1, 2, 3, 2, 2, 1, 1, 4, 4]
def baseStart_272929 : Nat := 118140960795 + 272929 * 2 ^ 59
def prefixEnd_272929 : Nat := 4983230072969 + 3 ^ 40 * 272929 * 2
def baseEnd_272929 : Nat := 124572232489838131317625

theorem tailTrace_272929 : CollatzResearch.WordTrace tailWord_272929 prefixEnd_272929 124572232489838131317625 := by
  unfold tailWord_272929
  simp only [CollatzResearch.WordTrace]
  refine ⟨9954538428232320407293841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6636358952154880271529227 9954538428232320407293841)
  ·
    refine ⟨7465903821174240305470381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9954538428232320407293841 7465903821174240305470381)
    ·
      refine ⟨2799713932940340114551393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7465903821174240305470381 2799713932940340114551393)
      ·
        refine ⟨2099785449705255085913545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2799713932940340114551393 2099785449705255085913545)
        ·
          refine ⟨1574839087278941314435159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2099785449705255085913545 1574839087278941314435159)
          ·
            refine ⟨2362258630918411971652739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1574839087278941314435159 2362258630918411971652739)
            ·
              refine ⟨3543387946377617957479109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2362258630918411971652739 3543387946377617957479109)
              ·
                refine ⟨664385239945803367027333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3543387946377617957479109 664385239945803367027333)
                ·
                  refine ⟨124572232489838131317625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 664385239945803367027333 124572232489838131317625)
                  ·
                    rfl

theorem cell20_272929_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 1, 4, 4].length) (baseStart_272929 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_272929 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_272929 prefixEnd_272929 := by exact prefixLift 272929
  have htrace : WordTrace (prefixWord ++ tailWord_272929) baseStart_272929 baseEnd_272929 := by
    simpa [prefixWord, tailWord_272929, baseEnd_272929] using wordTrace_append hprefix tailTrace_272929
  have hstable : (prefixWord ++ tailWord_272929).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_272929).length < 2 ^ (prefixWord ++ tailWord_272929).sum := by decide
  have hdescent : baseEnd_272929 < baseStart_272929 := by decide
  rcases family_descends (prefixWord ++ tailWord_272929) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_272932 : List Nat := [2, 3, 1, 5, 1, 1, 1, 6]
def baseStart_272932 : Nat := 118140960795 + 272932 * 2 ^ 59
def prefixEnd_272932 : Nat := 4983230072969 + 3 ^ 40 * 272932 * 2
def baseEnd_272932 : Nat := 41524533923861151405871

theorem tailTrace_272932 : CollatzResearch.WordTrace tailWord_272932 prefixEnd_272932 41524533923861151405871 := by
  unfold tailWord_272932
  simp only [CollatzResearch.WordTrace]
  refine ⟨4977323923610725959826525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6636431898147634613102033 4977323923610725959826525)
  ·
    refine ⟨1866496471354022234934947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4977323923610725959826525 1866496471354022234934947)
    ·
      refine ⟨2799744707031033352402421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1866496471354022234934947 2799744707031033352402421)
      ·
        refine ⟨262476066284159376787727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 2799744707031033352402421 262476066284159376787727)
        ·
          refine ⟨393714099426239065181591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 262476066284159376787727 393714099426239065181591)
          ·
            refine ⟨590571149139358597772387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 393714099426239065181591 590571149139358597772387)
            ·
              refine ⟨885856723709037896658581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 590571149139358597772387 885856723709037896658581)
              ·
                refine ⟨41524533923861151405871, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 885856723709037896658581 41524533923861151405871)
                ·
                  rfl

theorem cell20_272932_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 5, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 5, 1, 1, 1, 6].length) (baseStart_272932 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_272932 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_272932 prefixEnd_272932 := by exact prefixLift 272932
  have htrace : WordTrace (prefixWord ++ tailWord_272932) baseStart_272932 baseEnd_272932 := by
    simpa [prefixWord, tailWord_272932, baseEnd_272932] using wordTrace_append hprefix tailTrace_272932
  have hstable : (prefixWord ++ tailWord_272932).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_272932).length < 2 ^ (prefixWord ++ tailWord_272932).sum := by decide
  have hdescent : baseEnd_272932 < baseStart_272932 := by decide
  rcases family_descends (prefixWord ++ tailWord_272932) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_272973 : List Nat := [1, 6, 1, 1, 2, 3, 2, 1, 3]
def baseStart_272973 : Nat := 118140960795 + 272973 * 2 ^ 59
def prefixEnd_272973 : Nat := 4983230072969 + 3 ^ 40 * 272973 * 2
def baseEnd_272973 : Nat := 124592315288769533850779

theorem tailTrace_272973 : CollatzResearch.WordTrace tailWord_272973 prefixEnd_272973 124592315288769533850779 := by
  unfold tailWord_272973
  simp only [CollatzResearch.WordTrace]
  refine ⟨9956143240072915921895573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6637428826715277281263715 9956143240072915921895573)
  ·
    refine ⟨466694214378417933838855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 9956143240072915921895573 466694214378417933838855)
    ·
      refine ⟨700041321567626900758283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 466694214378417933838855 700041321567626900758283)
      ·
        refine ⟨1050061982351440351137425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 700041321567626900758283 1050061982351440351137425)
        ·
          refine ⟨787546486763580263353069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1050061982351440351137425 787546486763580263353069)
          ·
            refine ⟨295329932536342598757401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 787546486763580263353069 295329932536342598757401)
            ·
              refine ⟨221497449402256949068051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 295329932536342598757401 221497449402256949068051)
              ·
                refine ⟨332246174103385423602077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 221497449402256949068051 332246174103385423602077)
                ·
                  refine ⟨124592315288769533850779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 332246174103385423602077 124592315288769533850779)
                  ·
                    rfl

theorem cell20_272973_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 3, 2, 1, 3].length) (baseStart_272973 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_272973 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_272973 prefixEnd_272973 := by exact prefixLift 272973
  have htrace : WordTrace (prefixWord ++ tailWord_272973) baseStart_272973 baseEnd_272973 := by
    simpa [prefixWord, tailWord_272973, baseEnd_272973] using wordTrace_append hprefix tailTrace_272973
  have hstable : (prefixWord ++ tailWord_272973).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_272973).length < 2 ^ (prefixWord ++ tailWord_272973).sum := by decide
  have hdescent : baseEnd_272973 < baseStart_272973 := by decide
  rcases family_descends (prefixWord ++ tailWord_272973) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_272974 : List Nat := [4, 1, 1, 1, 1, 2, 3, 7]
def baseStart_272974 : Nat := 118140960795 + 272974 * 2 ^ 59
def prefixEnd_272974 : Nat := 4983230072969 + 3 ^ 40 * 272974 * 2
def baseEnd_272974 : Nat := 41530923905339324939147

theorem tailTrace_272974 : CollatzResearch.WordTrace tailWord_272974 prefixEnd_272974 41530923905339324939147 := by
  unfold tailWord_272974
  simp only [CollatzResearch.WordTrace]
  refine ⟨1244522464133661636585247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 6637453142046195395121317 1244522464133661636585247)
  ·
    refine ⟨1866783696200492454877871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1244522464133661636585247 1866783696200492454877871)
    ·
      refine ⟨2800175544300738682316807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1866783696200492454877871 2800175544300738682316807)
      ·
        refine ⟨4200263316451108023475211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2800175544300738682316807 4200263316451108023475211)
        ·
          refine ⟨6300394974676662035212817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4200263316451108023475211 6300394974676662035212817)
          ·
            refine ⟨4725296231007496526409613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6300394974676662035212817 4725296231007496526409613)
            ·
              refine ⟨1771986086627811197403605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4725296231007496526409613 1771986086627811197403605)
              ·
                refine ⟨41530923905339324939147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1771986086627811197403605 41530923905339324939147)
                ·
                  rfl

theorem cell20_272974_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 3, 7].length) (baseStart_272974 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_272974 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_272974 prefixEnd_272974 := by exact prefixLift 272974
  have htrace : WordTrace (prefixWord ++ tailWord_272974) baseStart_272974 baseEnd_272974 := by
    simpa [prefixWord, tailWord_272974, baseEnd_272974] using wordTrace_append hprefix tailTrace_272974
  have hstable : (prefixWord ++ tailWord_272974).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_272974).length < 2 ^ (prefixWord ++ tailWord_272974).sum := by decide
  have hdescent : baseEnd_272974 < baseStart_272974 := by decide
  rcases family_descends (prefixWord ++ tailWord_272974) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_272977 : List Nat := [1, 2, 2, 1, 3, 3, 4, 1, 3]
def baseStart_272977 : Nat := 118140960795 + 272977 * 2 ^ 59
def prefixEnd_272977 : Nat := 4983230072969 + 3 ^ 40 * 272977 * 2
def baseEnd_272977 : Nat := 124594140997763297717429

theorem tailTrace_272977 : CollatzResearch.WordTrace tailWord_272977 prefixEnd_272977 124594140997763297717429 := by
  unfold tailWord_272977
  simp only [CollatzResearch.WordTrace]
  refine ⟨9956289132058424605041185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6637526088038949736694123 9956289132058424605041185)
  ·
    refine ⟨7467216849043818453780889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9956289132058424605041185 7467216849043818453780889)
    ·
      refine ⟨5600412636782863840335667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7467216849043818453780889 5600412636782863840335667)
      ·
        refine ⟨8400618955174295760503501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5600412636782863840335667 8400618955174295760503501)
        ·
          refine ⟨3150232108190360910188813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8400618955174295760503501 3150232108190360910188813)
          ·
            refine ⟨1181337040571385341320805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3150232108190360910188813 1181337040571385341320805)
            ·
              refine ⟨221500695107134751497651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1181337040571385341320805 221500695107134751497651)
              ·
                refine ⟨332251042660702127246477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 221500695107134751497651 332251042660702127246477)
                ·
                  refine ⟨124594140997763297717429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 332251042660702127246477 124594140997763297717429)
                  ·
                    rfl

theorem cell20_272977_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 3, 4, 1, 3].length) (baseStart_272977 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_272977 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_272977 prefixEnd_272977 := by exact prefixLift 272977
  have htrace : WordTrace (prefixWord ++ tailWord_272977) baseStart_272977 baseEnd_272977 := by
    simpa [prefixWord, tailWord_272977, baseEnd_272977] using wordTrace_append hprefix tailTrace_272977
  have hstable : (prefixWord ++ tailWord_272977).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_272977).length < 2 ^ (prefixWord ++ tailWord_272977).sum := by decide
  have hdescent : baseEnd_272977 < baseStart_272977 := by decide
  rcases family_descends (prefixWord ++ tailWord_272977) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_273014 : List Nat := [5, 1, 1, 2, 4, 1, 2, 2, 2]
def baseStart_273014 : Nat := 118140960795 + 273014 * 2 ^ 59
def prefixEnd_273014 : Nat := 4983230072969 + 3 ^ 40 * 273014 * 2
def baseEnd_273014 : Nat := 124611028805955613483945

theorem tailTrace_273014 : CollatzResearch.WordTrace tailWord_273014 prefixEnd_273014 124611028805955613483945 := by
  unfold tailWord_273014
  simp only [CollatzResearch.WordTrace]
  refine ⟨622352414557773745258631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 6638425755282919949425397 622352414557773745258631)
  ·
    refine ⟨933528621836660617887947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 622352414557773745258631 933528621836660617887947)
    ·
      refine ⟨1400292932754990926831921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 933528621836660617887947 1400292932754990926831921)
      ·
        refine ⟨1050219699566243195123941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1400292932754990926831921 1050219699566243195123941)
        ·
          refine ⟨196916193668670599085739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1050219699566243195123941 196916193668670599085739)
          ·
            refine ⟨295374290503005898628609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 196916193668670599085739 295374290503005898628609)
            ·
              refine ⟨221530717877254423971457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 295374290503005898628609 221530717877254423971457)
              ·
                refine ⟨166148038407940817978593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 221530717877254423971457 166148038407940817978593)
                ·
                  refine ⟨124611028805955613483945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 166148038407940817978593 124611028805955613483945)
                  ·
                    rfl

theorem cell20_273014_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 4, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 4, 1, 2, 2, 2].length) (baseStart_273014 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_273014 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_273014 prefixEnd_273014 := by exact prefixLift 273014
  have htrace : WordTrace (prefixWord ++ tailWord_273014) baseStart_273014 baseEnd_273014 := by
    simpa [prefixWord, tailWord_273014, baseEnd_273014] using wordTrace_append hprefix tailTrace_273014
  have hstable : (prefixWord ++ tailWord_273014).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_273014).length < 2 ^ (prefixWord ++ tailWord_273014).sum := by decide
  have hdescent : baseEnd_273014 < baseStart_273014 := by decide
  rcases family_descends (prefixWord ++ tailWord_273014) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_273029 : List Nat := [1, 3, 1, 1, 4, 4, 1, 5]
def baseStart_273029 : Nat := 118140960795 + 273029 * 2 ^ 59
def prefixEnd_273029 : Nat := 4983230072969 + 3 ^ 40 * 273029 * 2
def baseEnd_273029 : Nat := 41539291738227409327961

theorem tailTrace_273029 : CollatzResearch.WordTrace tailWord_273029 prefixEnd_273029 41539291738227409327961 := by
  unfold tailWord_273029
  simp only [CollatzResearch.WordTrace]
  refine ⟨9958185727870037485934141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6638790485246691657289427 9958185727870037485934141)
  ·
    refine ⟨3734319647951264057225303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9958185727870037485934141 3734319647951264057225303)
    ·
      refine ⟨5601479471926896085837955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3734319647951264057225303 5601479471926896085837955)
      ·
        refine ⟨8402219207890344128756933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5601479471926896085837955 8402219207890344128756933)
        ·
          refine ⟨1575416101479439524141925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 8402219207890344128756933 1575416101479439524141925)
          ·
            refine ⟨295390519027394910776611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1575416101479439524141925 295390519027394910776611)
            ·
              refine ⟨443085778541092366164917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 295390519027394910776611 443085778541092366164917)
              ·
                refine ⟨41539291738227409327961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 443085778541092366164917 41539291738227409327961)
                ·
                  rfl

theorem cell20_273029_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 4, 1, 5].length) (baseStart_273029 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_273029 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_273029 prefixEnd_273029 := by exact prefixLift 273029
  have htrace : WordTrace (prefixWord ++ tailWord_273029) baseStart_273029 baseEnd_273029 := by
    simpa [prefixWord, tailWord_273029, baseEnd_273029] using wordTrace_append hprefix tailTrace_273029
  have hstable : (prefixWord ++ tailWord_273029).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_273029).length < 2 ^ (prefixWord ++ tailWord_273029).sum := by decide
  have hdescent : baseEnd_273029 < baseStart_273029 := by decide
  rcases family_descends (prefixWord ++ tailWord_273029) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_273066 : List Nat := [3, 1, 5, 2, 2, 1, 1, 2, 3]
def baseStart_273066 : Nat := 118140960795 + 273066 * 2 ^ 59
def prefixEnd_273066 : Nat := 4983230072969 + 3 ^ 40 * 273066 * 2
def baseEnd_273066 : Nat := 124634763022874543750399

theorem tailTrace_273066 : CollatzResearch.WordTrace tailWord_273066 prefixEnd_273066 124634763022874543750399 := by
  unfold tailWord_273066
  simp only [CollatzResearch.WordTrace]
  refine ⟨2489883807183998201257763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6639690152490661870020701 2489883807183998201257763)
  ·
    refine ⟨3734825710775997301886645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2489883807183998201257763 3734825710775997301886645)
    ·
      refine ⟨350139910385249747051873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 3734825710775997301886645 350139910385249747051873)
      ·
        refine ⟨262604932788937310288905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 350139910385249747051873 262604932788937310288905)
        ·
          refine ⟨196953699591702982716679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 262604932788937310288905 196953699591702982716679)
          ·
            refine ⟨295430549387554474075019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 196953699591702982716679 295430549387554474075019)
            ·
              refine ⟨443145824081331711112529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 295430549387554474075019 443145824081331711112529)
              ·
                refine ⟨332359368060998783334397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 443145824081331711112529 332359368060998783334397)
                ·
                  refine ⟨124634763022874543750399, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 332359368060998783334397 124634763022874543750399)
                  ·
                    rfl

theorem cell20_273066_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 2, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 2, 2, 1, 1, 2, 3].length) (baseStart_273066 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_273066 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_273066 prefixEnd_273066 := by exact prefixLift 273066
  have htrace : WordTrace (prefixWord ++ tailWord_273066) baseStart_273066 baseEnd_273066 := by
    simpa [prefixWord, tailWord_273066, baseEnd_273066] using wordTrace_append hprefix tailTrace_273066
  have hstable : (prefixWord ++ tailWord_273066).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_273066).length < 2 ^ (prefixWord ++ tailWord_273066).sum := by decide
  have hdescent : baseEnd_273066 < baseStart_273066 := by decide
  rcases family_descends (prefixWord ++ tailWord_273066) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_273070 : List Nat := [4, 1, 4, 1, 1, 1, 3, 2, 3]
def baseStart_273070 : Nat := 118140960795 + 273070 * 2 ^ 59
def prefixEnd_273070 : Nat := 4983230072969 + 3 ^ 40 * 273070 * 2
def baseEnd_273070 : Nat := 124636588731868307617049

theorem tailTrace_273070 : CollatzResearch.WordTrace tailWord_273070 prefixEnd_273070 124636588731868307617049 := by
  unfold tailWord_273070
  simp only [CollatzResearch.WordTrace]
  refine ⟨1244960140090187686022083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 6639787413814334325451109 1244960140090187686022083)
  ·
    refine ⟨1867440210135281529033125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1244960140090187686022083 1867440210135281529033125)
    ·
      refine ⟨350145039400365286693711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1867440210135281529033125 350145039400365286693711)
      ·
        refine ⟨525217559100547930040567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 350145039400365286693711 525217559100547930040567)
        ·
          refine ⟨787826338650821895060851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 525217559100547930040567 787826338650821895060851)
          ·
            refine ⟨1181739507976232842591277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 787826338650821895060851 1181739507976232842591277)
            ·
              refine ⟨443152315491087315971729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1181739507976232842591277 443152315491087315971729)
              ·
                refine ⟨332364236618315486978797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 443152315491087315971729 332364236618315486978797)
                ·
                  refine ⟨124636588731868307617049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 332364236618315486978797 124636588731868307617049)
                  ·
                    rfl

theorem cell20_273070_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 1, 3, 2, 3].length) (baseStart_273070 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_273070 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_273070 prefixEnd_273070 := by exact prefixLift 273070
  have htrace : WordTrace (prefixWord ++ tailWord_273070) baseStart_273070 baseEnd_273070 := by
    simpa [prefixWord, tailWord_273070, baseEnd_273070] using wordTrace_append hprefix tailTrace_273070
  have hstable : (prefixWord ++ tailWord_273070).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_273070).length < 2 ^ (prefixWord ++ tailWord_273070).sum := by decide
  have hdescent : baseEnd_273070 < baseStart_273070 := by decide
  rcases family_descends (prefixWord ++ tailWord_273070) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_273077 : List Nat := [1, 3, 3, 3, 1, 1, 2, 4, 2]
def baseStart_273077 : Nat := 118140960795 + 273077 * 2 ^ 59
def prefixEnd_273077 : Nat := 4983230072969 + 3 ^ 40 * 273077 * 2
def baseEnd_273077 : Nat := 124639783722607394383687

theorem tailTrace_273077 : CollatzResearch.WordTrace tailWord_273077 prefixEnd_273077 124639783722607394383687 := by
  unfold tailWord_273077
  simp only [CollatzResearch.WordTrace]
  refine ⟨9959936431696141683681485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6639957621130761122454323 9959936431696141683681485)
  ·
    refine ⟨3734976161886053131380557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9959936431696141683681485 3734976161886053131380557)
    ·
      refine ⟨1400616060707269924267709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3734976161886053131380557 1400616060707269924267709)
      ·
        refine ⟨525231022765226221600391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1400616060707269924267709 525231022765226221600391)
        ·
          refine ⟨787846534147839332400587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 525231022765226221600391 787846534147839332400587)
          ·
            refine ⟨1181769801221758998600881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 787846534147839332400587 1181769801221758998600881)
            ·
              refine ⟨886327350916319248950661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1181769801221758998600881 886327350916319248950661)
              ·
                refine ⟨166186378296809859178249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 886327350916319248950661 166186378296809859178249)
                ·
                  refine ⟨124639783722607394383687, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 166186378296809859178249 124639783722607394383687)
                  ·
                    rfl

theorem cell20_273077_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 1, 2, 4, 2].length) (baseStart_273077 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_273077 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_273077 prefixEnd_273077 := by exact prefixLift 273077
  have htrace : WordTrace (prefixWord ++ tailWord_273077) baseStart_273077 baseEnd_273077 := by
    simpa [prefixWord, tailWord_273077, baseEnd_273077] using wordTrace_append hprefix tailTrace_273077
  have hstable : (prefixWord ++ tailWord_273077).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_273077).length < 2 ^ (prefixWord ++ tailWord_273077).sum := by decide
  have hdescent : baseEnd_273077 < baseStart_273077 := by decide
  rcases family_descends (prefixWord ++ tailWord_273077) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_273181 : List Nat := [1, 4, 2, 4, 1, 8]
def baseStart_273181 : Nat := 118140960795 + 273181 * 2 ^ 59
def prefixEnd_273181 : Nat := 4983230072969 + 3 ^ 40 * 273181 * 2
def baseEnd_273181 : Nat := 4618046376164639070985

theorem tailTrace_273181 : CollatzResearch.WordTrace tailWord_273181 prefixEnd_273181 4618046376164639070985 := by
  unfold tailWord_273181
  simp only [CollatzResearch.WordTrace]
  refine ⟨9963729623319367445467397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6642486415546244963644931 9963729623319367445467397)
  ·
    refine ⟨1868199304372381396025137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 9963729623319367445467397 1868199304372381396025137)
    ·
      refine ⟨1401149478279286047018853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1868199304372381396025137 1401149478279286047018853)
      ·
        refine ⟨262715527177366133816035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1401149478279286047018853 262715527177366133816035)
        ·
          refine ⟨394073290766049200724053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 262715527177366133816035 394073290766049200724053)
          ·
            refine ⟨4618046376164639070985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 394073290766049200724053 4618046376164639070985)
            ·
              rfl

theorem cell20_273181_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 4, 1, 8].length) (baseStart_273181 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_273181 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_273181 prefixEnd_273181 := by exact prefixLift 273181
  have htrace : WordTrace (prefixWord ++ tailWord_273181) baseStart_273181 baseEnd_273181 := by
    simpa [prefixWord, tailWord_273181, baseEnd_273181] using wordTrace_append hprefix tailTrace_273181
  have hstable : (prefixWord ++ tailWord_273181).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_273181).length < 2 ^ (prefixWord ++ tailWord_273181).sum := by decide
  have hdescent : baseEnd_273181 < baseStart_273181 := by decide
  rcases family_descends (prefixWord ++ tailWord_273181) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_273198 : List Nat := [4, 1, 3, 2, 1, 3, 1, 5]
def baseStart_273198 : Nat := 118140960795 + 273198 * 2 ^ 59
def prefixEnd_273198 : Nat := 4983230072969 + 3 ^ 40 * 273198 * 2
def baseEnd_273198 : Nat := 41565003806556250449953

theorem tailTrace_273198 : CollatzResearch.WordTrace tailWord_273198 prefixEnd_273198 41565003806556250449953 := by
  unfold tailWord_273198
  simp only [CollatzResearch.WordTrace]
  refine ⟨1245543708032222418604531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 6642899776171852899224165 1245543708032222418604531)
  ·
    refine ⟨1868315562048333627906797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1245543708032222418604531 1868315562048333627906797)
    ·
      refine ⟨700618335768125110465049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1868315562048333627906797 700618335768125110465049)
      ·
        refine ⟨525463751826093832848787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 700618335768125110465049 525463751826093832848787)
        ·
          refine ⟨788195627739140749273181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 525463751826093832848787 788195627739140749273181)
          ·
            refine ⟨295573360402177780977443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 788195627739140749273181 295573360402177780977443)
            ·
              refine ⟨443360040603266671466165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 295573360402177780977443 443360040603266671466165)
              ·
                refine ⟨41565003806556250449953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 443360040603266671466165 41565003806556250449953)
                ·
                  rfl

theorem cell20_273198_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 3, 1, 5].length) (baseStart_273198 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_273198 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_273198 prefixEnd_273198 := by exact prefixLift 273198
  have htrace : WordTrace (prefixWord ++ tailWord_273198) baseStart_273198 baseEnd_273198 := by
    simpa [prefixWord, tailWord_273198, baseEnd_273198] using wordTrace_append hprefix tailTrace_273198
  have hstable : (prefixWord ++ tailWord_273198).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_273198).length < 2 ^ (prefixWord ++ tailWord_273198).sum := by decide
  have hdescent : baseEnd_273198 < baseStart_273198 := by decide
  rcases family_descends (prefixWord ++ tailWord_273198) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_273247 : List Nat := [1, 1, 2, 3, 1, 3, 3, 1, 5]
def baseStart_273247 : Nat := 118140960795 + 273247 * 2 ^ 59
def prefixEnd_273247 : Nat := 4983230072969 + 3 ^ 40 * 273247 * 2
def baseEnd_273247 : Nat := 124717376354842358716325

theorem tailTrace_273247 : CollatzResearch.WordTrace tailWord_273247 prefixEnd_273247 124717376354842358716325 := by
  unfold tailWord_273247
  simp only [CollatzResearch.WordTrace]
  refine ⟨9966136841080260717369995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6644091227386840478246663 9966136841080260717369995)
  ·
    refine ⟨14949205261620391076054993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9966136841080260717369995 14949205261620391076054993)
    ·
      refine ⟨11211903946215293307041245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14949205261620391076054993 11211903946215293307041245)
      ·
        refine ⟨4204463979830734990140467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11211903946215293307041245 4204463979830734990140467)
        ·
          refine ⟨6306695969746102485210701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4204463979830734990140467 6306695969746102485210701)
          ·
            refine ⟨2365010988654788431954013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6306695969746102485210701 2365010988654788431954013)
            ·
              refine ⟨886879120745545661982755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2365010988654788431954013 886879120745545661982755)
              ·
                refine ⟨1330318681118318492974133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 886879120745545661982755 1330318681118318492974133)
                ·
                  refine ⟨124717376354842358716325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1330318681118318492974133 124717376354842358716325)
                  ·
                    rfl

theorem cell20_273247_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 3, 1, 5].length) (baseStart_273247 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_273247 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_273247 prefixEnd_273247 := by exact prefixLift 273247
  have htrace : WordTrace (prefixWord ++ tailWord_273247) baseStart_273247 baseEnd_273247 := by
    simpa [prefixWord, tailWord_273247, baseEnd_273247] using wordTrace_append hprefix tailTrace_273247
  have hstable : (prefixWord ++ tailWord_273247).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_273247).length < 2 ^ (prefixWord ++ tailWord_273247).sum := by decide
  have hdescent : baseEnd_273247 < baseStart_273247 := by decide
  rcases family_descends (prefixWord ++ tailWord_273247) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_273285 : List Nat := [1, 3, 1, 1, 3, 3, 1, 2, 5]
def baseStart_273285 : Nat := 118140960795 + 273285 * 2 ^ 59
def prefixEnd_273285 : Nat := 4983230072969 + 3 ^ 40 * 273285 * 2
def baseEnd_273285 : Nat := 124734720590283115449503

theorem tailTrace_273285 : CollatzResearch.WordTrace tailWord_273285 prefixEnd_273285 124734720590283115449503 := by
  unfold tailWord_273285
  simp only [CollatzResearch.WordTrace]
  refine ⟨9967522814942593207253309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6645015209961728804835539 9967522814942593207253309)
  ·
    refine ⟨3737821055603472452719991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9967522814942593207253309 3737821055603472452719991)
    ·
      refine ⟨5606731583405208679079987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3737821055603472452719991 5606731583405208679079987)
      ·
        refine ⟨8410097375107813018619981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5606731583405208679079987 8410097375107813018619981)
        ·
          refine ⟨3153786515665429881982493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8410097375107813018619981 3153786515665429881982493)
          ·
            refine ⟨1182669943374536205743435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3153786515665429881982493 1182669943374536205743435)
            ·
              refine ⟨1774004915061804308615153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1182669943374536205743435 1774004915061804308615153)
              ·
                refine ⟨1330503686296353231461365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1774004915061804308615153 1330503686296353231461365)
                ·
                  refine ⟨124734720590283115449503, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1330503686296353231461365 124734720590283115449503)
                  ·
                    rfl

theorem cell20_273285_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 3, 1, 2, 5].length) (baseStart_273285 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_273285 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_273285 prefixEnd_273285 := by exact prefixLift 273285
  have htrace : WordTrace (prefixWord ++ tailWord_273285) baseStart_273285 baseEnd_273285 := by
    simpa [prefixWord, tailWord_273285, baseEnd_273285] using wordTrace_append hprefix tailTrace_273285
  have hstable : (prefixWord ++ tailWord_273285).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_273285).length < 2 ^ (prefixWord ++ tailWord_273285).sum := by decide
  have hdescent : baseEnd_273285 < baseStart_273285 := by decide
  rcases family_descends (prefixWord ++ tailWord_273285) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan20Incremental
