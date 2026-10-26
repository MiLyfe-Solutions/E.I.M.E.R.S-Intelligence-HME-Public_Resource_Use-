import V185TrunkScan23Chunk0561

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_3321962 : List Nat := [3, 1, 3, 2, 3, 2, 2, 7]
def baseStart_3321962 : Nat := 118140960795 + 3321962 * 2 ^ 59
def prefixEnd_3321962 : Nat := 4983230072969 + 3 ^ 40 * 3321962 * 2
def baseEnd_3321962 : Nat := 63176415628564334892503

theorem tailTrace_3321962 : CollatzResearch.WordTrace tailWord_3321962 prefixEnd_3321962 63176415628564334892503 := by
  unfold tailWord_3321962
  simp only [CollatzResearch.WordTrace]
  refine ⟨30290476997776623696498035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 80774605327404329857328093 30290476997776623696498035)
  ·
    refine ⟨45435715496664935544747053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30290476997776623696498035 45435715496664935544747053)
    ·
      refine ⟨17038393311249350829280145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 45435715496664935544747053 17038393311249350829280145)
      ·
        refine ⟨12778794983437013121960109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17038393311249350829280145 12778794983437013121960109)
        ·
          refine ⟨4792048118788879920735041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12778794983437013121960109 4792048118788879920735041)
          ·
            refine ⟨3594036089091659940551281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4792048118788879920735041 3594036089091659940551281)
            ·
              refine ⟨2695527066818744955413461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3594036089091659940551281 2695527066818744955413461)
              ·
                refine ⟨63176415628564334892503, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2695527066818744955413461 63176415628564334892503)
                ·
                  rfl

theorem cell23_3321962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 3, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 3, 2, 2, 7].length) (baseStart_3321962 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3321962 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3321962 prefixEnd_3321962 := by exact prefixLift 3321962
  have htrace : WordTrace (prefixWord ++ tailWord_3321962) baseStart_3321962 baseEnd_3321962 := by
    simpa [prefixWord, tailWord_3321962, baseEnd_3321962] using wordTrace_append hprefix tailTrace_3321962
  have hstable : (prefixWord ++ tailWord_3321962).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3321962).length < 2 ^ (prefixWord ++ tailWord_3321962).sum := by decide
  have hdescent : baseEnd_3321962 < baseStart_3321962 := by decide
  rcases family_descends (prefixWord ++ tailWord_3321962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3321968 : List Nat := [2, 1, 1, 1, 5, 2, 1, 1, 2, 2, 5]
def baseStart_3321968 : Nat := 118140960795 + 3321968 * 2 ^ 59
def prefixEnd_3321968 : Nat := 4983230072969 + 3 ^ 40 * 3321968 * 2
def baseEnd_3321968 : Nat := 1705766302855164018622553

theorem tailTrace_3321968 : CollatzResearch.WordTrace tailWord_3321968 prefixEnd_3321968 1705766302855164018622553 := by
  unfold tailWord_3321968
  simp only [CollatzResearch.WordTrace]
  refine ⟨60581063414542378905355279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80774751219389838540473705 60581063414542378905355279)
  ·
    refine ⟨90871595121813568358032919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60581063414542378905355279 90871595121813568358032919)
    ·
      refine ⟨136307392682720352537049379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90871595121813568358032919 136307392682720352537049379)
      ·
        refine ⟨204461089024080528805574069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 136307392682720352537049379 204461089024080528805574069)
        ·
          refine ⟨19168227096007549575522569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 204461089024080528805574069 19168227096007549575522569)
          ·
            refine ⟨14376170322005662181641927, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19168227096007549575522569 14376170322005662181641927)
            ·
              refine ⟨21564255483008493272462891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14376170322005662181641927 21564255483008493272462891)
              ·
                refine ⟨32346383224512739908694337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21564255483008493272462891 32346383224512739908694337)
                ·
                  refine ⟨24259787418384554931520753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32346383224512739908694337 24259787418384554931520753)
                  ·
                    refine ⟨18194840563788416198640565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 24259787418384554931520753 18194840563788416198640565)
                    ·
                      refine ⟨1705766302855164018622553, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 18194840563788416198640565 1705766302855164018622553)
                      ·
                        rfl

theorem cell23_3321968_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 2, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 2, 1, 1, 2, 2, 5].length) (baseStart_3321968 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3321968 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3321968 prefixEnd_3321968 := by exact prefixLift 3321968
  have htrace : WordTrace (prefixWord ++ tailWord_3321968) baseStart_3321968 baseEnd_3321968 := by
    simpa [prefixWord, tailWord_3321968, baseEnd_3321968] using wordTrace_append hprefix tailTrace_3321968
  have hstable : (prefixWord ++ tailWord_3321968).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3321968).length < 2 ^ (prefixWord ++ tailWord_3321968).sum := by decide
  have hdescent : baseEnd_3321968 < baseStart_3321968 := by decide
  rcases family_descends (prefixWord ++ tailWord_3321968) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3322012 : List Nat := [2, 2, 3, 2, 1, 1, 2, 3, 1, 4, 2]
def baseStart_3322012 : Nat := 118140960795 + 3322012 * 2 ^ 59
def prefixEnd_3322012 : Nat := 4983230072969 + 3 ^ 40 * 3322012 * 2
def baseEnd_3322012 : Nat := 1705788896003961846472351

theorem tailTrace_3322012 : CollatzResearch.WordTrace tailWord_3322012 prefixEnd_3322012 1705788896003961846472351 := by
  unfold tailWord_3322012
  simp only [CollatzResearch.WordTrace]
  refine ⟨60581865820462676662656145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80775821093950235550208193 60581865820462676662656145)
  ·
    refine ⟨45436399365347007496992109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60581865820462676662656145 45436399365347007496992109)
    ·
      refine ⟨17038649762005127811372041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 45436399365347007496992109 17038649762005127811372041)
      ·
        refine ⟨12778987321503845858529031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17038649762005127811372041 12778987321503845858529031)
        ·
          refine ⟨19168480982255768787793547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12778987321503845858529031 19168480982255768787793547)
          ·
            refine ⟨28752721473383653181690321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19168480982255768787793547 28752721473383653181690321)
            ·
              refine ⟨21564541105037739886267741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28752721473383653181690321 21564541105037739886267741)
              ·
                refine ⟨8086702914389152457350403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21564541105037739886267741 8086702914389152457350403)
                ·
                  refine ⟨12130054371583728686025605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8086702914389152457350403 12130054371583728686025605)
                  ·
                    refine ⟨2274385194671949128629801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 12130054371583728686025605 2274385194671949128629801)
                    ·
                      refine ⟨1705788896003961846472351, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2274385194671949128629801 1705788896003961846472351)
                      ·
                        rfl

theorem cell23_3322012_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 2, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 2, 3, 1, 4, 2].length) (baseStart_3322012 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3322012 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3322012 prefixEnd_3322012 := by exact prefixLift 3322012
  have htrace : WordTrace (prefixWord ++ tailWord_3322012) baseStart_3322012 baseEnd_3322012 := by
    simpa [prefixWord, tailWord_3322012, baseEnd_3322012] using wordTrace_append hprefix tailTrace_3322012
  have hstable : (prefixWord ++ tailWord_3322012).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3322012).length < 2 ^ (prefixWord ++ tailWord_3322012).sum := by decide
  have hdescent : baseEnd_3322012 < baseStart_3322012 := by decide
  rcases family_descends (prefixWord ++ tailWord_3322012) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3322015 : List Nat := [1, 1, 2, 6, 1, 1, 1, 2, 2, 1, 5]
def baseStart_3322015 : Nat := 118140960795 + 3322015 * 2 ^ 59
def prefixEnd_3322015 : Nat := 4983230072969 + 3 ^ 40 * 3322015 * 2
def baseEnd_3322015 : Nat := 1705790436445925334734837

theorem tailTrace_3322015 : CollatzResearch.WordTrace tailWord_3322015 prefixEnd_3322015 1705790436445925334734837 := by
  unfold tailWord_3322015
  simp only [CollatzResearch.WordTrace]
  refine ⟨121163841059914484837671499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80775894039942989891780999 121163841059914484837671499)
  ·
    refine ⟨181745761589871727256507249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121163841059914484837671499 181745761589871727256507249)
    ·
      refine ⟨136309321192403795442380437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 181745761589871727256507249 136309321192403795442380437)
      ·
        refine ⟨6389499430893927911361583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 136309321192403795442380437 6389499430893927911361583)
        ·
          refine ⟨9584249146340891867042375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6389499430893927911361583 9584249146340891867042375)
          ·
            refine ⟨14376373719511337800563563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9584249146340891867042375 14376373719511337800563563)
            ·
              refine ⟨21564560579267006700845345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14376373719511337800563563 21564560579267006700845345)
              ·
                refine ⟨16173420434450255025634009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21564560579267006700845345 16173420434450255025634009)
                ·
                  refine ⟨12130065325837691269225507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16173420434450255025634009 12130065325837691269225507)
                  ·
                    refine ⟨18195097988756536903838261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12130065325837691269225507 18195097988756536903838261)
                    ·
                      refine ⟨1705790436445925334734837, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 18195097988756536903838261 1705790436445925334734837)
                      ·
                        rfl

theorem cell23_3322015_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 1, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 1, 1, 2, 2, 1, 5].length) (baseStart_3322015 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3322015 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3322015 prefixEnd_3322015 := by exact prefixLift 3322015
  have htrace : WordTrace (prefixWord ++ tailWord_3322015) baseStart_3322015 baseEnd_3322015 := by
    simpa [prefixWord, tailWord_3322015, baseEnd_3322015] using wordTrace_append hprefix tailTrace_3322015
  have hstable : (prefixWord ++ tailWord_3322015).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3322015).length < 2 ^ (prefixWord ++ tailWord_3322015).sum := by decide
  have hdescent : baseEnd_3322015 < baseStart_3322015 := by decide
  rcases family_descends (prefixWord ++ tailWord_3322015) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3322029 : List Nat := [1, 5, 2, 1, 2, 2, 1, 2, 1, 4, 2]
def baseStart_3322029 : Nat := 118140960795 + 3322029 * 2 ^ 59
def prefixEnd_3322029 : Nat := 4983230072969 + 3 ^ 40 * 3322029 * 2
def baseEnd_3322029 : Nat := 1705797625175088279959773

theorem tailTrace_3322029 : CollatzResearch.WordTrace tailWord_3322029 prefixEnd_3322029 1705797625175088279959773 := by
  unfold tailWord_3322029
  simp only [CollatzResearch.WordTrace]
  refine ⟨121164351681863765228681141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80776234454575843485787427 121164351681863765228681141)
  ·
    refine ⟨11359157970174727990188857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 121164351681863765228681141 11359157970174727990188857)
    ·
      refine ⟨8519368477631045992641643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11359157970174727990188857 8519368477631045992641643)
      ·
        refine ⟨12779052716446568988962465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8519368477631045992641643 12779052716446568988962465)
        ·
          refine ⟨9584289537334926741721849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12779052716446568988962465 9584289537334926741721849)
          ·
            refine ⟨7188217153001195056291387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9584289537334926741721849 7188217153001195056291387)
            ·
              refine ⟨10782325729501792584437081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7188217153001195056291387 10782325729501792584437081)
              ·
                refine ⟨8086744297126344438327811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10782325729501792584437081 8086744297126344438327811)
                ·
                  refine ⟨12130116445689516657491717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8086744297126344438327811 12130116445689516657491717)
                  ·
                    refine ⟨2274396833566784373279697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 12130116445689516657491717 2274396833566784373279697)
                    ·
                      refine ⟨1705797625175088279959773, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2274396833566784373279697 1705797625175088279959773)
                      ·
                        rfl

theorem cell23_3322029_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 2, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 2, 1, 2, 1, 4, 2].length) (baseStart_3322029 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3322029 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3322029 prefixEnd_3322029 := by exact prefixLift 3322029
  have htrace : WordTrace (prefixWord ++ tailWord_3322029) baseStart_3322029 baseEnd_3322029 := by
    simpa [prefixWord, tailWord_3322029, baseEnd_3322029] using wordTrace_append hprefix tailTrace_3322029
  have hstable : (prefixWord ++ tailWord_3322029).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3322029).length < 2 ^ (prefixWord ++ tailWord_3322029).sum := by decide
  have hdescent : baseEnd_3322029 < baseStart_3322029 := by decide
  rcases family_descends (prefixWord ++ tailWord_3322029) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3322035 : List Nat := [1, 1, 1, 2, 3, 2, 1, 7, 5]
def baseStart_3322035 : Nat := 118140960795 + 3322035 * 2 ^ 59
def prefixEnd_3322035 : Nat := 4983230072969 + 3 ^ 40 * 3322035 * 2
def baseEnd_3322035 : Nat := 189533411784335028498305

theorem tailTrace_3322035 : CollatzResearch.WordTrace tailWord_3322035 prefixEnd_3322035 189533411784335028498305 := by
  unfold tailWord_3322035
  simp only [CollatzResearch.WordTrace]
  refine ⟨121164570519842028253399559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80776380346561352168933039 121164570519842028253399559)
  ·
    refine ⟨181746855779763042380099339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121164570519842028253399559 181746855779763042380099339)
    ·
      refine ⟨272620283669644563570149009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 181746855779763042380099339 272620283669644563570149009)
      ·
        refine ⟨204465212752233422677611757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 272620283669644563570149009 204465212752233422677611757)
        ·
          refine ⟨76674454782087533504104409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 204465212752233422677611757 76674454782087533504104409)
          ·
            refine ⟨57505841086565650128078307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 76674454782087533504104409 57505841086565650128078307)
            ·
              refine ⟨86258761629848475192117461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 57505841086565650128078307 86258761629848475192117461)
              ·
                refine ⟨2021689725699573637315253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 86258761629848475192117461 2021689725699573637315253)
                ·
                  refine ⟨189533411784335028498305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2021689725699573637315253 189533411784335028498305)
                  ·
                    rfl

theorem cell23_3322035_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 1, 7, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 1, 7, 5].length) (baseStart_3322035 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3322035 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3322035 prefixEnd_3322035 := by exact prefixLift 3322035
  have htrace : WordTrace (prefixWord ++ tailWord_3322035) baseStart_3322035 baseEnd_3322035 := by
    simpa [prefixWord, tailWord_3322035, baseEnd_3322035] using wordTrace_append hprefix tailTrace_3322035
  have hstable : (prefixWord ++ tailWord_3322035).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3322035).length < 2 ^ (prefixWord ++ tailWord_3322035).sum := by decide
  have hdescent : baseEnd_3322035 < baseStart_3322035 := by decide
  rcases family_descends (prefixWord ++ tailWord_3322035) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3322045 : List Nat := [1, 4, 1, 2, 1, 1, 1, 4, 2, 3, 3]
def baseStart_3322045 : Nat := 118140960795 + 3322045 * 2 ^ 59
def prefixEnd_3322045 : Nat := 4983230072969 + 3 ^ 40 * 3322045 * 2
def baseEnd_3322045 : Nat := 1705805840865560217359699

theorem tailTrace_3322045 : CollatzResearch.WordTrace tailWord_3322045 prefixEnd_3322045 1705805840865560217359699 := by
  unfold tailWord_3322045
  simp only [CollatzResearch.WordTrace]
  refine ⟨121164935249805799961263589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80776623499870533307509059 121164935249805799961263589)
  ·
    refine ⟨22718425359338587492736923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 121164935249805799961263589 22718425359338587492736923)
    ·
      refine ⟨34077638039007881239105385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22718425359338587492736923 34077638039007881239105385)
      ·
        refine ⟨25558228529255910929329039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34077638039007881239105385 25558228529255910929329039)
        ·
          refine ⟨38337342793883866393993559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25558228529255910929329039 38337342793883866393993559)
          ·
            refine ⟨57506014190825799590990339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38337342793883866393993559 57506014190825799590990339)
            ·
              refine ⟨86259021286238699386485509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 57506014190825799590990339 86259021286238699386485509)
              ·
                refine ⟨16173566491169756134966033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 86259021286238699386485509 16173566491169756134966033)
                ·
                  refine ⟨12130174868377317101224525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16173566491169756134966033 12130174868377317101224525)
                  ·
                    refine ⟨4548815575641493912959197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12130174868377317101224525 4548815575641493912959197)
                    ·
                      refine ⟨1705805840865560217359699, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4548815575641493912959197 1705805840865560217359699)
                      ·
                        rfl

theorem cell23_3322045_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 1, 4, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 1, 4, 2, 3, 3].length) (baseStart_3322045 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3322045 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3322045 prefixEnd_3322045 := by exact prefixLift 3322045
  have htrace : WordTrace (prefixWord ++ tailWord_3322045) baseStart_3322045 baseEnd_3322045 := by
    simpa [prefixWord, tailWord_3322045, baseEnd_3322045] using wordTrace_append hprefix tailTrace_3322045
  have hstable : (prefixWord ++ tailWord_3322045).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3322045).length < 2 ^ (prefixWord ++ tailWord_3322045).sum := by decide
  have hdescent : baseEnd_3322045 < baseStart_3322045 := by decide
  rcases family_descends (prefixWord ++ tailWord_3322045) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3322062 : List Nat := [4, 1, 1, 1, 4, 2, 1, 1, 2, 3, 3]
def baseStart_3322062 : Nat := 118140960795 + 3322062 * 2 ^ 59
def prefixEnd_3322062 : Nat := 4983230072969 + 3 ^ 40 * 3322062 * 2
def baseEnd_3322062 : Nat := 1705814570036686650847121

theorem tailTrace_3322062 : CollatzResearch.WordTrace tailWord_3322062 prefixEnd_3322062 1705814570036686650847121 := by
  unfold tailWord_3322062
  simp only [CollatzResearch.WordTrace]
  refine ⟨15145694411343026483079055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 80777036860496141243088293 15145694411343026483079055)
  ·
    refine ⟨22718541617014539724618583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15145694411343026483079055 22718541617014539724618583)
    ·
      refine ⟨34077812425521809586927875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22718541617014539724618583 34077812425521809586927875)
      ·
        refine ⟨51116718638282714380391813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34077812425521809586927875 51116718638282714380391813)
        ·
          refine ⟨9584384744678008946323465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 51116718638282714380391813 9584384744678008946323465)
          ·
            refine ⟨7188288558508506709742599, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9584384744678008946323465 7188288558508506709742599)
            ·
              refine ⟨10782432837762760064613899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7188288558508506709742599 10782432837762760064613899)
              ·
                refine ⟨16173649256644140096920849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10782432837762760064613899 16173649256644140096920849)
                ·
                  refine ⟨12130236942483105072690637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16173649256644140096920849 12130236942483105072690637)
                  ·
                    refine ⟨4548838853431164402258989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12130236942483105072690637 4548838853431164402258989)
                    ·
                      refine ⟨1705814570036686650847121, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4548838853431164402258989 1705814570036686650847121)
                      ·
                        rfl

theorem cell23_3322062_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 2, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 2, 1, 1, 2, 3, 3].length) (baseStart_3322062 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3322062 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3322062 prefixEnd_3322062 := by exact prefixLift 3322062
  have htrace : WordTrace (prefixWord ++ tailWord_3322062) baseStart_3322062 baseEnd_3322062 := by
    simpa [prefixWord, tailWord_3322062, baseEnd_3322062] using wordTrace_append hprefix tailTrace_3322062
  have hstable : (prefixWord ++ tailWord_3322062).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3322062).length < 2 ^ (prefixWord ++ tailWord_3322062).sum := by decide
  have hdescent : baseEnd_3322062 < baseStart_3322062 := by decide
  rcases family_descends (prefixWord ++ tailWord_3322062) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3322102 : List Nat := [5, 1, 1, 1, 1, 1, 2, 4, 2, 1, 4]
def baseStart_3322102 : Nat := 118140960795 + 3322102 * 2 ^ 59
def prefixEnd_3322102 : Nat := 4983230072969 + 3 ^ 40 * 3322102 * 2
def baseEnd_3322102 : Nat := 1705835109262866494346937

theorem tailTrace_3322102 : CollatzResearch.WordTrace tailWord_3322102 prefixEnd_3322102 1705835109262866494346937 := by
  unfold tailWord_3322102
  simp only [CollatzResearch.WordTrace]
  refine ⟨7572938388162456168505535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 80778009473732865797392373 7572938388162456168505535)
  ·
    refine ⟨11359407582243684252758303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7572938388162456168505535 11359407582243684252758303)
    ·
      refine ⟨17039111373365526379137455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11359407582243684252758303 17039111373365526379137455)
      ·
        refine ⟨25558667060048289568706183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17039111373365526379137455 25558667060048289568706183)
        ·
          refine ⟨38338000590072434353059275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25558667060048289568706183 38338000590072434353059275)
          ·
            refine ⟨57507000885108651529588913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38338000590072434353059275 57507000885108651529588913)
            ·
              refine ⟨43130250663831488647191685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 57507000885108651529588913 43130250663831488647191685)
              ·
                refine ⟨8086921999468404121348441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 43130250663831488647191685 8086921999468404121348441)
                ·
                  refine ⟨6065191499601303091011331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8086921999468404121348441 6065191499601303091011331)
                  ·
                    refine ⟨9097787249401954636516997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6065191499601303091011331 9097787249401954636516997)
                    ·
                      refine ⟨1705835109262866494346937, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9097787249401954636516997 1705835109262866494346937)
                      ·
                        rfl

theorem cell23_3322102_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 2, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 2, 4, 2, 1, 4].length) (baseStart_3322102 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3322102 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3322102 prefixEnd_3322102 := by exact prefixLift 3322102
  have htrace : WordTrace (prefixWord ++ tailWord_3322102) baseStart_3322102 baseEnd_3322102 := by
    simpa [prefixWord, tailWord_3322102, baseEnd_3322102] using wordTrace_append hprefix tailTrace_3322102
  have hstable : (prefixWord ++ tailWord_3322102).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3322102).length < 2 ^ (prefixWord ++ tailWord_3322102).sum := by decide
  have hdescent : baseEnd_3322102 < baseStart_3322102 := by decide
  rcases family_descends (prefixWord ++ tailWord_3322102) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3322146 : List Nat := [3, 3, 1, 1, 3, 1, 3, 3, 1, 4]
def baseStart_3322146 : Nat := 118140960795 + 3322146 * 2 ^ 59
def prefixEnd_3322146 : Nat := 4983230072969 + 3 ^ 40 * 3322146 * 2
def baseEnd_3322146 : Nat := 568619234137221440732245

theorem tailTrace_3322146 : CollatzResearch.WordTrace tailWord_3322146 prefixEnd_3322146 568619234137221440732245 := by
  unfold tailWord_3322146
  simp only [CollatzResearch.WordTrace]
  refine ⟨30292154755609973552672573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 80779079348293262807126861 30292154755609973552672573)
  ·
    refine ⟨11359558033353740082252215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 30292154755609973552672573 11359558033353740082252215)
    ·
      refine ⟨17039337050030610123378323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11359558033353740082252215 17039337050030610123378323)
      ·
        refine ⟨25559005575045915185067485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17039337050030610123378323 25559005575045915185067485)
        ·
          refine ⟨9584627090642218194400307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25559005575045915185067485 9584627090642218194400307)
          ·
            refine ⟨14376940635963327291600461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9584627090642218194400307 14376940635963327291600461)
            ·
              refine ⟨5391352738486247734350173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14376940635963327291600461 5391352738486247734350173)
              ·
                refine ⟨2021757276932342900381315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5391352738486247734350173 2021757276932342900381315)
                ·
                  refine ⟨3032635915398514350571973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2021757276932342900381315 3032635915398514350571973)
                  ·
                    refine ⟨568619234137221440732245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3032635915398514350571973 568619234137221440732245)
                    ·
                      rfl

theorem cell23_3322146_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 1, 3, 3, 1, 4].length) (baseStart_3322146 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3322146 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3322146 prefixEnd_3322146 := by exact prefixLift 3322146
  have htrace : WordTrace (prefixWord ++ tailWord_3322146) baseStart_3322146 baseEnd_3322146 := by
    simpa [prefixWord, tailWord_3322146, baseEnd_3322146] using wordTrace_append hprefix tailTrace_3322146
  have hstable : (prefixWord ++ tailWord_3322146).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3322146).length < 2 ^ (prefixWord ++ tailWord_3322146).sum := by decide
  have hdescent : baseEnd_3322146 < baseStart_3322146 := by decide
  rcases family_descends (prefixWord ++ tailWord_3322146) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3322185 : List Nat := [1, 2, 1, 1, 2, 3, 1, 5, 1, 6]
def baseStart_3322185 : Nat := 118140960795 + 3322185 * 2 ^ 59
def prefixEnd_3322185 : Nat := 4983230072969 + 3 ^ 40 * 3322185 * 2
def baseEnd_3322185 : Nat := 568625909385729889869685

theorem tailTrace_3322185 : CollatzResearch.WordTrace tailWord_3322185 prefixEnd_3322185 568625909385729889869685 := by
  unfold tailWord_3322185
  simp only [CollatzResearch.WordTrace]
  refine ⟨121170041469298603871360009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80780027646199069247573339 121170041469298603871360009)
  ·
    refine ⟨90877531101973952903520007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 121170041469298603871360009 90877531101973952903520007)
    ·
      refine ⟨136316296652960929355280011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90877531101973952903520007 136316296652960929355280011)
      ·
        refine ⟨204474444979441394032920017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 136316296652960929355280011 204474444979441394032920017)
        ·
          refine ⟨153355833734581045524690013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 204474444979441394032920017 153355833734581045524690013)
          ·
            refine ⟨57508437650467892071758755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 153355833734581045524690013 57508437650467892071758755)
            ·
              refine ⟨86262656475701838107638133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 57508437650467892071758755 86262656475701838107638133)
              ·
                refine ⟨8087124044597047322591075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 86262656475701838107638133 8087124044597047322591075)
                ·
                  refine ⟨12130686066895570983886613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8087124044597047322591075 12130686066895570983886613)
                  ·
                    refine ⟨568625909385729889869685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 12130686066895570983886613 568625909385729889869685)
                    ·
                      rfl

theorem cell23_3322185_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 1, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 1, 5, 1, 6].length) (baseStart_3322185 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3322185 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3322185 prefixEnd_3322185 := by exact prefixLift 3322185
  have htrace : WordTrace (prefixWord ++ tailWord_3322185) baseStart_3322185 baseEnd_3322185 := by
    simpa [prefixWord, tailWord_3322185, baseEnd_3322185] using wordTrace_append hprefix tailTrace_3322185
  have hstable : (prefixWord ++ tailWord_3322185).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3322185).length < 2 ^ (prefixWord ++ tailWord_3322185).sum := by decide
  have hdescent : baseEnd_3322185 < baseStart_3322185 := by decide
  rcases family_descends (prefixWord ++ tailWord_3322185) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3322192 : List Nat := [2, 1, 1, 1, 1, 7, 1, 1, 3, 1, 4]
def baseStart_3322192 : Nat := 118140960795 + 3322192 * 2 ^ 59
def prefixEnd_3322192 : Nat := 4983230072969 + 3 ^ 40 * 3322192 * 2
def baseEnd_3322192 : Nat := 1705881322521771142221523

theorem tailTrace_3322192 : CollatzResearch.WordTrace tailWord_3322192 prefixEnd_3322192 1705881322521771142221523 := by
  unfold tailWord_3322192
  simp only [CollatzResearch.WordTrace]
  refine ⟨60585148390136622033432415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80780197853515496044576553 60585148390136622033432415)
  ·
    refine ⟨90877722585204933050148623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60585148390136622033432415 90877722585204933050148623)
    ·
      refine ⟨136316583877807399575222935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90877722585204933050148623 136316583877807399575222935)
      ·
        refine ⟨204474875816711099362834403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 136316583877807399575222935 204474875816711099362834403)
        ·
          refine ⟨306712313725066649044251605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 204474875816711099362834403 306712313725066649044251605)
          ·
            refine ⟨7188569852931249586974647, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 306712313725066649044251605 7188569852931249586974647)
            ·
              refine ⟨10782854779396874380461971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7188569852931249586974647 10782854779396874380461971)
              ·
                refine ⟨16174282169095311570692957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10782854779396874380461971 16174282169095311570692957)
                ·
                  refine ⟨6065355813410741839009859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16174282169095311570692957 6065355813410741839009859)
                  ·
                    refine ⟨9098033720116112758514789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6065355813410741839009859 9098033720116112758514789)
                    ·
                      refine ⟨1705881322521771142221523, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9098033720116112758514789 1705881322521771142221523)
                      ·
                        rfl

theorem cell23_3322192_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 7, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 7, 1, 1, 3, 1, 4].length) (baseStart_3322192 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3322192 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3322192 prefixEnd_3322192 := by exact prefixLift 3322192
  have htrace : WordTrace (prefixWord ++ tailWord_3322192) baseStart_3322192 baseEnd_3322192 := by
    simpa [prefixWord, tailWord_3322192, baseEnd_3322192] using wordTrace_append hprefix tailTrace_3322192
  have hstable : (prefixWord ++ tailWord_3322192).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3322192).length < 2 ^ (prefixWord ++ tailWord_3322192).sum := by decide
  have hdescent : baseEnd_3322192 < baseStart_3322192 := by decide
  rcases family_descends (prefixWord ++ tailWord_3322192) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3322196 : List Nat := [2, 4, 1, 1, 2, 3, 2, 1, 2, 3, 2]
def baseStart_3322196 : Nat := 118140960795 + 3322196 * 2 ^ 59
def prefixEnd_3322196 : Nat := 4983230072969 + 3 ^ 40 * 3322196 * 2
def baseEnd_3322196 : Nat := 1705883376444389126571505

theorem tailTrace_3322196 : CollatzResearch.WordTrace tailWord_3322196 prefixEnd_3322196 1705883376444389126571505 := by
  unfold tailWord_3322196
  simp only [CollatzResearch.WordTrace]
  refine ⟨60585221336129376375005221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80780295114839168500006961 60585221336129376375005221)
  ·
    refine ⟨11359729000524258070313479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 60585221336129376375005221 11359729000524258070313479)
    ·
      refine ⟨17039593500786387105470219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11359729000524258070313479 17039593500786387105470219)
      ·
        refine ⟨25559390251179580658205329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17039593500786387105470219 25559390251179580658205329)
        ·
          refine ⟨19169542688384685493653997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25559390251179580658205329 19169542688384685493653997)
          ·
            refine ⟨7188578508144257060120249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19169542688384685493653997 7188578508144257060120249)
            ·
              refine ⟨5391433881108192795090187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7188578508144257060120249 5391433881108192795090187)
              ·
                refine ⟨8087150821662289192635281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5391433881108192795090187 8087150821662289192635281)
                ·
                  refine ⟨6065363116246716894476461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8087150821662289192635281 6065363116246716894476461)
                  ·
                    refine ⟨2274511168592518835428673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6065363116246716894476461 2274511168592518835428673)
                    ·
                      refine ⟨1705883376444389126571505, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2274511168592518835428673 1705883376444389126571505)
                      ·
                        rfl

theorem cell23_3322196_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 3, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 3, 2, 1, 2, 3, 2].length) (baseStart_3322196 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3322196 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3322196 prefixEnd_3322196 := by exact prefixLift 3322196
  have htrace : WordTrace (prefixWord ++ tailWord_3322196) baseStart_3322196 baseEnd_3322196 := by
    simpa [prefixWord, tailWord_3322196, baseEnd_3322196] using wordTrace_append hprefix tailTrace_3322196
  have hstable : (prefixWord ++ tailWord_3322196).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3322196).length < 2 ^ (prefixWord ++ tailWord_3322196).sum := by decide
  have hdescent : baseEnd_3322196 < baseStart_3322196 := by decide
  rcases family_descends (prefixWord ++ tailWord_3322196) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3322215 : List Nat := [1, 1, 5, 1, 3, 12]
def baseStart_3322215 : Nat := 118140960795 + 3322215 * 2 ^ 59
def prefixEnd_3322215 : Nat := 4983230072969 + 3 ^ 40 * 3322215 * 2
def baseEnd_3322215 : Nat := 7020136348052775935119

theorem tailTrace_3322215 : CollatzResearch.WordTrace tailWord_3322215 prefixEnd_3322215 7020136348052775935119 := by
  unfold tailWord_3322215
  simp only [CollatzResearch.WordTrace]
  refine ⟨121171135659189918994952099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80780757106126612663301399 121171135659189918994952099)
  ·
    refine ⟨181756703488784878492428149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121171135659189918994952099 181756703488784878492428149)
    ·
      refine ⟨17039690952073582358665139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 181756703488784878492428149 17039690952073582358665139)
      ·
        refine ⟨25559536428110373537997709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17039690952073582358665139 25559536428110373537997709)
        ·
          refine ⟨9584826160541390076749141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25559536428110373537997709 9584826160541390076749141)
          ·
            refine ⟨7020136348052775935119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 12 9584826160541390076749141 7020136348052775935119)
            ·
              rfl

theorem cell23_3322215_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 12].length) (baseStart_3322215 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3322215 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3322215 prefixEnd_3322215 := by exact prefixLift 3322215
  have htrace : WordTrace (prefixWord ++ tailWord_3322215) baseStart_3322215 baseEnd_3322215 := by
    simpa [prefixWord, tailWord_3322215, baseEnd_3322215] using wordTrace_append hprefix tailTrace_3322215
  have hstable : (prefixWord ++ tailWord_3322215).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3322215).length < 2 ^ (prefixWord ++ tailWord_3322215).sum := by decide
  have hdescent : baseEnd_3322215 < baseStart_3322215 := by decide
  rcases family_descends (prefixWord ++ tailWord_3322215) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3322220 : List Nat := [2, 2, 1, 1, 6, 2, 2, 2, 1, 1, 3]
def baseStart_3322220 : Nat := 118140960795 + 3322220 * 2 ^ 59
def prefixEnd_3322220 : Nat := 4983230072969 + 3 ^ 40 * 3322220 * 2
def baseEnd_3322220 : Nat := 1705895699980097032671395

theorem tailTrace_3322220 : CollatzResearch.WordTrace tailWord_3322220 prefixEnd_3322220 1705895699980097032671395 := by
  unfold tailWord_3322220
  simp only [CollatzResearch.WordTrace]
  refine ⟨60585659012085902424442057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80780878682781203232589409 60585659012085902424442057)
  ·
    refine ⟨45439244259064426818331543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60585659012085902424442057 45439244259064426818331543)
    ·
      refine ⟨68158866388596640227497315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45439244259064426818331543 68158866388596640227497315)
      ·
        refine ⟨102238299582894960341245973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68158866388596640227497315 102238299582894960341245973)
        ·
          refine ⟨4792420292948201265995905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 102238299582894960341245973 4792420292948201265995905)
          ·
            refine ⟨3594315219711150949496929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4792420292948201265995905 3594315219711150949496929)
            ·
              refine ⟨2695736414783363212122697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3594315219711150949496929 2695736414783363212122697)
              ·
                refine ⟨2021802311087522409092023, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2695736414783363212122697 2021802311087522409092023)
                ·
                  refine ⟨3032703466631283613638035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2021802311087522409092023 3032703466631283613638035)
                  ·
                    refine ⟨4549055199946925420457053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3032703466631283613638035 4549055199946925420457053)
                    ·
                      refine ⟨1705895699980097032671395, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4549055199946925420457053 1705895699980097032671395)
                      ·
                        rfl

theorem cell23_3322220_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 6, 2, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 6, 2, 2, 2, 1, 1, 3].length) (baseStart_3322220 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3322220 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3322220 prefixEnd_3322220 := by exact prefixLift 3322220
  have htrace : WordTrace (prefixWord ++ tailWord_3322220) baseStart_3322220 baseEnd_3322220 := by
    simpa [prefixWord, tailWord_3322220, baseEnd_3322220] using wordTrace_append hprefix tailTrace_3322220
  have hstable : (prefixWord ++ tailWord_3322220).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3322220).length < 2 ^ (prefixWord ++ tailWord_3322220).sum := by decide
  have hdescent : baseEnd_3322220 < baseStart_3322220 := by decide
  rcases family_descends (prefixWord ++ tailWord_3322220) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3322229 : List Nat := [1, 3, 4, 1, 2, 1, 1, 2, 3, 2, 3]
def baseStart_3322229 : Nat := 118140960795 + 3322229 * 2 ^ 59
def prefixEnd_3322229 : Nat := 4983230072969 + 3 ^ 40 * 3322229 * 2
def baseEnd_3322229 : Nat := 1705900321305987497458853

theorem tailTrace_3322229 : CollatzResearch.WordTrace tailWord_3322229 prefixEnd_3322229 1705900321305987497458853 := by
  unfold tailWord_3322229
  simp only [CollatzResearch.WordTrace]
  refine ⟨121171646281139199385961741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80781097520759466257307827 121171646281139199385961741)
  ·
    refine ⟨45439367355427199769735653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 121171646281139199385961741 45439367355427199769735653)
    ·
      refine ⟨8519881379142599956825435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 45439367355427199769735653 8519881379142599956825435)
      ·
        refine ⟨12779822068713899935238153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8519881379142599956825435 12779822068713899935238153)
        ·
          refine ⟨9584866551535424951428615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12779822068713899935238153 9584866551535424951428615)
          ·
            refine ⟨14377299827303137427142923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9584866551535424951428615 14377299827303137427142923)
            ·
              refine ⟨21565949740954706140714385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14377299827303137427142923 21565949740954706140714385)
              ·
                refine ⟨16174462305716029605535789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21565949740954706140714385 16174462305716029605535789)
                ·
                  refine ⟨6065423364643511102075921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16174462305716029605535789 6065423364643511102075921)
                  ·
                    refine ⟨4549067523482633326556941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6065423364643511102075921 4549067523482633326556941)
                    ·
                      refine ⟨1705900321305987497458853, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4549067523482633326556941 1705900321305987497458853)
                      ·
                        rfl

theorem cell23_3322229_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 1, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 1, 1, 2, 3, 2, 3].length) (baseStart_3322229 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3322229 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3322229 prefixEnd_3322229 := by exact prefixLift 3322229
  have htrace : WordTrace (prefixWord ++ tailWord_3322229) baseStart_3322229 baseEnd_3322229 := by
    simpa [prefixWord, tailWord_3322229, baseEnd_3322229] using wordTrace_append hprefix tailTrace_3322229
  have hstable : (prefixWord ++ tailWord_3322229).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3322229).length < 2 ^ (prefixWord ++ tailWord_3322229).sum := by decide
  have hdescent : baseEnd_3322229 < baseStart_3322229 := by decide
  rcases family_descends (prefixWord ++ tailWord_3322229) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3322245 : List Nat := [1, 3, 1, 1, 3, 1, 1, 1, 4, 7]
def baseStart_3322245 : Nat := 118140960795 + 3322245 * 2 ^ 59
def prefixEnd_3322245 : Nat := 4983230072969 + 3 ^ 40 * 3322245 * 2
def baseEnd_3322245 : Nat := 568636178998819811619593

theorem tailTrace_3322245 : CollatzResearch.WordTrace tailWord_3322245 prefixEnd_3322245 568636178998819811619593 := by
  unfold tailWord_3322245
  simp only [CollatzResearch.WordTrace]
  refine ⟨121172229849081234118544189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80781486566054156079029459 121172229849081234118544189)
  ·
    refine ⟨45439586193405462794454071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 121172229849081234118544189 45439586193405462794454071)
    ·
      refine ⟨68159379290108194191681107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45439586193405462794454071 68159379290108194191681107)
      ·
        refine ⟨102239068935162291287521661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68159379290108194191681107 102239068935162291287521661)
        ·
          refine ⟨38339650850685859232820623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 102239068935162291287521661 38339650850685859232820623)
          ·
            refine ⟨57509476276028788849230935, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38339650850685859232820623 57509476276028788849230935)
            ·
              refine ⟨86264214414043183273846403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 57509476276028788849230935 86264214414043183273846403)
              ·
                refine ⟨129396321621064774910769605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 86264214414043183273846403 129396321621064774910769605)
                ·
                  refine ⟨24261810303949645295769301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 129396321621064774910769605 24261810303949645295769301)
                  ·
                    refine ⟨568636178998819811619593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 24261810303949645295769301 568636178998819811619593)
                    ·
                      rfl

theorem cell23_3322245_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 1, 1, 4, 7].length) (baseStart_3322245 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3322245 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3322245 prefixEnd_3322245 := by exact prefixLift 3322245
  have htrace : WordTrace (prefixWord ++ tailWord_3322245) baseStart_3322245 baseEnd_3322245 := by
    simpa [prefixWord, tailWord_3322245, baseEnd_3322245] using wordTrace_append hprefix tailTrace_3322245
  have hstable : (prefixWord ++ tailWord_3322245).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3322245).length < 2 ^ (prefixWord ++ tailWord_3322245).sum := by decide
  have hdescent : baseEnd_3322245 < baseStart_3322245 := by decide
  rcases family_descends (prefixWord ++ tailWord_3322245) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3322260 : List Nat := [2, 4, 2, 1, 4, 1, 2, 1, 1, 1, 4]
def baseStart_3322260 : Nat := 118140960795 + 3322260 * 2 ^ 59
def prefixEnd_3322260 : Nat := 4983230072969 + 3 ^ 40 * 3322260 * 2
def baseEnd_3322260 : Nat := 1705916239206276876171211

theorem tailTrace_3322260 : CollatzResearch.WordTrace tailWord_3322260 prefixEnd_3322260 1705916239206276876171211 := by
  unfold tailWord_3322260
  simp only [CollatzResearch.WordTrace]
  refine ⟨60586388472013445840170117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80781851296017927786893489 60586388472013445840170117)
  ·
    refine ⟨11359947838502521095031897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 60586388472013445840170117 11359947838502521095031897)
    ·
      refine ⟨8519960878876890821273923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11359947838502521095031897 8519960878876890821273923)
      ·
        refine ⟨12779941318315336231910885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8519960878876890821273923 12779941318315336231910885)
        ·
          refine ⟨2396238997184125543483291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 12779941318315336231910885 2396238997184125543483291)
          ·
            refine ⟨3594358495776188315224937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2396238997184125543483291 3594358495776188315224937)
            ·
              refine ⟨2695768871832141236418703, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3594358495776188315224937 2695768871832141236418703)
              ·
                refine ⟨4043653307748211854628055, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2695768871832141236418703 4043653307748211854628055)
                ·
                  refine ⟨6065479961622317781942083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4043653307748211854628055 6065479961622317781942083)
                  ·
                    refine ⟨9098219942433476672913125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6065479961622317781942083 9098219942433476672913125)
                    ·
                      refine ⟨1705916239206276876171211, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9098219942433476672913125 1705916239206276876171211)
                      ·
                        rfl

theorem cell23_3322260_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 4, 1, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 4, 1, 2, 1, 1, 1, 4].length) (baseStart_3322260 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3322260 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3322260 prefixEnd_3322260 := by exact prefixLift 3322260
  have htrace : WordTrace (prefixWord ++ tailWord_3322260) baseStart_3322260 baseEnd_3322260 := by
    simpa [prefixWord, tailWord_3322260, baseEnd_3322260] using wordTrace_append hprefix tailTrace_3322260
  have hstable : (prefixWord ++ tailWord_3322260).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3322260).length < 2 ^ (prefixWord ++ tailWord_3322260).sum := by decide
  have hdescent : baseEnd_3322260 < baseStart_3322260 := by decide
  rcases family_descends (prefixWord ++ tailWord_3322260) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3322276 : List Nat := [2, 3, 1, 2, 1, 1, 5, 2, 2, 1, 3]
def baseStart_3322276 : Nat := 118140960795 + 3322276 * 2 ^ 59
def prefixEnd_3322276 : Nat := 4983230072969 + 3 ^ 40 * 3322276 * 2
def baseEnd_3322276 : Nat := 1705924454896748813571137

theorem tailTrace_3322276 : CollatzResearch.WordTrace tailWord_3322276 prefixEnd_3322276 1705924454896748813571137 := by
  unfold tailWord_3322276
  simp only [CollatzResearch.WordTrace]
  refine ⟨60586680255984463206461341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80782240341312617608615121 60586680255984463206461341)
  ·
    refine ⟨22720005095994173702423003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 60586680255984463206461341 22720005095994173702423003)
    ·
      refine ⟨34080007643991260553634505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22720005095994173702423003 34080007643991260553634505)
      ·
        refine ⟨25560005732993445415225879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34080007643991260553634505 25560005732993445415225879)
        ·
          refine ⟨38340008599490168122838819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25560005732993445415225879 38340008599490168122838819)
          ·
            refine ⟨57510012899235252184258229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38340008599490168122838819 57510012899235252184258229)
            ·
              refine ⟨5391563709303304892274209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 57510012899235252184258229 5391563709303304892274209)
              ·
                refine ⟨4043672781977478669205657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5391563709303304892274209 4043672781977478669205657)
                ·
                  refine ⟨3032754586483109001904243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4043672781977478669205657 3032754586483109001904243)
                  ·
                    refine ⟨4549131879724663502856365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3032754586483109001904243 4549131879724663502856365)
                    ·
                      refine ⟨1705924454896748813571137, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4549131879724663502856365 1705924454896748813571137)
                      ·
                        rfl

theorem cell23_3322276_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 5, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 5, 2, 2, 1, 3].length) (baseStart_3322276 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3322276 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3322276 prefixEnd_3322276 := by exact prefixLift 3322276
  have htrace : WordTrace (prefixWord ++ tailWord_3322276) baseStart_3322276 baseEnd_3322276 := by
    simpa [prefixWord, tailWord_3322276, baseEnd_3322276] using wordTrace_append hprefix tailTrace_3322276
  have hstable : (prefixWord ++ tailWord_3322276).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3322276).length < 2 ^ (prefixWord ++ tailWord_3322276).sum := by decide
  have hdescent : baseEnd_3322276 < baseStart_3322276 := by decide
  rcases family_descends (prefixWord ++ tailWord_3322276) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3322293 : List Nat := [1, 3, 3, 2, 4, 1, 1, 1, 1, 3, 3]
def baseStart_3322293 : Nat := 118140960795 + 3322293 * 2 ^ 59
def prefixEnd_3322293 : Nat := 4983230072969 + 3 ^ 40 * 3322293 * 2
def baseEnd_3322293 : Nat := 1705933184067875247058559

theorem tailTrace_3322293 : CollatzResearch.WordTrace tailWord_3322293 prefixEnd_3322293 1705933184067875247058559 := by
  unfold tailWord_3322293
  simp only [CollatzResearch.WordTrace]
  refine ⟨121173980552907338316291533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80782653701938225544194355 121173980552907338316291533)
  ·
    refine ⟨45440242707340251868609325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 121173980552907338316291533 45440242707340251868609325)
    ·
      refine ⟨17040091015252594450728497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 45440242707340251868609325 17040091015252594450728497)
      ·
        refine ⟨12780068261439445838046373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17040091015252594450728497 12780068261439445838046373)
        ·
          refine ⟨2396262799019896094633695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 12780068261439445838046373 2396262799019896094633695)
          ·
            refine ⟨3594394198529844141950543, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2396262799019896094633695 3594394198529844141950543)
            ·
              refine ⟨5391591297794766212925815, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3594394198529844141950543 5391591297794766212925815)
              ·
                refine ⟨8087386946692149319388723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5391591297794766212925815 8087386946692149319388723)
                ·
                  refine ⟨12131080420038223979083085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8087386946692149319388723 12131080420038223979083085)
                  ·
                    refine ⟨4549155157514333992156157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12131080420038223979083085 4549155157514333992156157)
                    ·
                      refine ⟨1705933184067875247058559, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4549155157514333992156157 1705933184067875247058559)
                      ·
                        rfl

theorem cell23_3322293_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 4, 1, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 4, 1, 1, 1, 1, 3, 3].length) (baseStart_3322293 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3322293 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3322293 prefixEnd_3322293 := by exact prefixLift 3322293
  have htrace : WordTrace (prefixWord ++ tailWord_3322293) baseStart_3322293 baseEnd_3322293 := by
    simpa [prefixWord, tailWord_3322293, baseEnd_3322293] using wordTrace_append hprefix tailTrace_3322293
  have hstable : (prefixWord ++ tailWord_3322293).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3322293).length < 2 ^ (prefixWord ++ tailWord_3322293).sum := by decide
  have hdescent : baseEnd_3322293 < baseStart_3322293 := by decide
  rcases family_descends (prefixWord ++ tailWord_3322293) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3322333 : List Nat := [1, 4, 3, 1, 1, 1, 2, 4, 2, 2, 2]
def baseStart_3322333 : Nat := 118140960795 + 3322333 * 2 ^ 59
def prefixEnd_3322333 : Nat := 4983230072969 + 3 ^ 40 * 3322333 * 2
def baseEnd_3322333 : Nat := 1705953723294055090558375

theorem tailTrace_3322333 : CollatzResearch.WordTrace tailWord_3322333 prefixEnd_3322333 1705953723294055090558375 := by
  unfold tailWord_3322333
  simp only [CollatzResearch.WordTrace]
  refine ⟨121175439472762425147747653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80783626315174950098498435 121175439472762425147747653)
  ·
    refine ⟨22720394901142954715202685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 121175439472762425147747653 22720394901142954715202685)
    ·
      refine ⟨8520148087928608018201007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22720394901142954715202685 8520148087928608018201007)
      ·
        refine ⟨12780222131892912027301511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8520148087928608018201007 12780222131892912027301511)
        ·
          refine ⟨19170333197839368040952267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12780222131892912027301511 19170333197839368040952267)
          ·
            refine ⟨28755499796759052061428401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19170333197839368040952267 28755499796759052061428401)
            ·
              refine ⟨21566624847569289046071301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28755499796759052061428401 21566624847569289046071301)
              ·
                refine ⟨4043742158919241696138369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 21566624847569289046071301 4043742158919241696138369)
                ·
                  refine ⟨3032806619189431272103777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4043742158919241696138369 3032806619189431272103777)
                  ·
                    refine ⟨2274604964392073454077833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3032806619189431272103777 2274604964392073454077833)
                    ·
                      refine ⟨1705953723294055090558375, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2274604964392073454077833 1705953723294055090558375)
                      ·
                        rfl

theorem cell23_3322333_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 2, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 2, 4, 2, 2, 2].length) (baseStart_3322333 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3322333 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3322333 prefixEnd_3322333 := by exact prefixLift 3322333
  have htrace : WordTrace (prefixWord ++ tailWord_3322333) baseStart_3322333 baseEnd_3322333 := by
    simpa [prefixWord, tailWord_3322333, baseEnd_3322333] using wordTrace_append hprefix tailTrace_3322333
  have hstable : (prefixWord ++ tailWord_3322333).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3322333).length < 2 ^ (prefixWord ++ tailWord_3322333).sum := by decide
  have hdescent : baseEnd_3322333 < baseStart_3322333 := by decide
  rcases family_descends (prefixWord ++ tailWord_3322333) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3322350 : List Nat := [4, 1, 2, 1, 2, 2, 4, 1, 2, 2, 2]
def baseStart_3322350 : Nat := 118140960795 + 3322350 * 2 ^ 59
def prefixEnd_3322350 : Nat := 4983230072969 + 3 ^ 40 * 3322350 * 2
def baseEnd_3322350 : Nat := 1705962452465181524045797

theorem tailTrace_3322350 : CollatzResearch.WordTrace tailWord_3322350 prefixEnd_3322350 1705962452465181524045797 := by
  unfold tailWord_3322350
  simp only [CollatzResearch.WordTrace]
  refine ⟨15147007439212604631389563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 80784039675800558034077669 15147007439212604631389563)
  ·
    refine ⟨22720511158818906947084345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15147007439212604631389563 22720511158818906947084345)
    ·
      refine ⟨17040383369114180210313259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22720511158818906947084345 17040383369114180210313259)
      ·
        refine ⟨25560575053671270315469889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17040383369114180210313259 25560575053671270315469889)
        ·
          refine ⟨19170431290253452736602417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25560575053671270315469889 19170431290253452736602417)
          ·
            refine ⟨14377823467690089552451813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19170431290253452736602417 14377823467690089552451813)
            ·
              refine ⟨2695841900191891791084715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 14377823467690089552451813 2695841900191891791084715)
              ·
                refine ⟨4043762850287837686627073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2695841900191891791084715 4043762850287837686627073)
                ·
                  refine ⟨3032822137715878264970305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4043762850287837686627073 3032822137715878264970305)
                  ·
                    refine ⟨2274616603286908698727729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3032822137715878264970305 2274616603286908698727729)
                    ·
                      refine ⟨1705962452465181524045797, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2274616603286908698727729 1705962452465181524045797)
                      ·
                        rfl

theorem cell23_3322350_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 2, 4, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 2, 4, 1, 2, 2, 2].length) (baseStart_3322350 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3322350 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3322350 prefixEnd_3322350 := by exact prefixLift 3322350
  have htrace : WordTrace (prefixWord ++ tailWord_3322350) baseStart_3322350 baseEnd_3322350 := by
    simpa [prefixWord, tailWord_3322350, baseEnd_3322350] using wordTrace_append hprefix tailTrace_3322350
  have hstable : (prefixWord ++ tailWord_3322350).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3322350).length < 2 ^ (prefixWord ++ tailWord_3322350).sum := by decide
  have hdescent : baseEnd_3322350 < baseStart_3322350 := by decide
  rcases family_descends (prefixWord ++ tailWord_3322350) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3322352 : List Nat := [2, 1, 1, 1, 3, 3, 1, 2, 4, 5]
def baseStart_3322352 : Nat := 118140960795 + 3322352 * 2 ^ 59
def prefixEnd_3322352 : Nat := 4983230072969 + 3 ^ 40 * 3322352 * 2
def baseEnd_3322352 : Nat := 568654493142163505406929

theorem tailTrace_3322352 : CollatzResearch.WordTrace tailWord_3322352 prefixEnd_3322352 568654493142163505406929 := by
  unfold tailWord_3322352
  simp only [CollatzResearch.WordTrace]
  refine ⟨60588066229846795696344655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80784088306462394261792873 60588066229846795696344655)
  ·
    refine ⟨90882099344770193544516983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60588066229846795696344655 90882099344770193544516983)
    ·
      refine ⟨136323149017155290316775475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90882099344770193544516983 136323149017155290316775475)
      ·
        refine ⟨204484723525732935475163213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 136323149017155290316775475 204484723525732935475163213)
        ·
          refine ⟨76681771322149850803186205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 204484723525732935475163213 76681771322149850803186205)
          ·
            refine ⟨28755664245806194051194827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 76681771322149850803186205 28755664245806194051194827)
            ·
              refine ⟨43133496368709291076792241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28755664245806194051194827 43133496368709291076792241)
              ·
                refine ⟨32350122276531968307594181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 43133496368709291076792241 32350122276531968307594181)
                ·
                  refine ⟨6065647926849744057673909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 32350122276531968307594181 6065647926849744057673909)
                  ·
                    refine ⟨568654493142163505406929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6065647926849744057673909 568654493142163505406929)
                    ·
                      rfl

theorem cell23_3322352_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 1, 2, 4, 5].length) (baseStart_3322352 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3322352 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3322352 prefixEnd_3322352 := by exact prefixLift 3322352
  have htrace : WordTrace (prefixWord ++ tailWord_3322352) baseStart_3322352 baseEnd_3322352 := by
    simpa [prefixWord, tailWord_3322352, baseEnd_3322352] using wordTrace_append hprefix tailTrace_3322352
  have hstable : (prefixWord ++ tailWord_3322352).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3322352).length < 2 ^ (prefixWord ++ tailWord_3322352).sum := by decide
  have hdescent : baseEnd_3322352 < baseStart_3322352 := by decide
  rcases family_descends (prefixWord ++ tailWord_3322352) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3322369 : List Nat := [1, 2, 4, 1, 3, 1, 1, 3, 2, 5]
def baseStart_3322369 : Nat := 118140960795 + 3322369 * 2 ^ 59
def prefixEnd_3322369 : Nat := 4983230072969 + 3 ^ 40 * 3322369 * 2
def baseEnd_3322369 : Nat := 568657402865872316569403

theorem tailTrace_3322369 : CollatzResearch.WordTrace tailWord_3322369 prefixEnd_3322369 568657402865872316569403 := by
  unfold tailWord_3322369
  simp only [CollatzResearch.WordTrace]
  refine ⟨121176752500632003296058161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80784501667088002197372107 121176752500632003296058161)
  ·
    refine ⟨90882564375474002472043621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 121176752500632003296058161 90882564375474002472043621)
    ·
      refine ⟨17040480820401375463508179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 90882564375474002472043621 17040480820401375463508179)
      ·
        refine ⟨25560721230602063195262269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17040480820401375463508179 25560721230602063195262269)
        ·
          refine ⟨9585270461475773698223351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25560721230602063195262269 9585270461475773698223351)
          ·
            refine ⟨14377905692213660547335027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9585270461475773698223351 14377905692213660547335027)
            ·
              refine ⟨21566858538320490821002541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14377905692213660547335027 21566858538320490821002541)
              ·
                refine ⟨8087571951870184057875953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21566858538320490821002541 8087571951870184057875953)
                ·
                  refine ⟨6065678963902638043406965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8087571951870184057875953 6065678963902638043406965)
                  ·
                    refine ⟨568657402865872316569403, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6065678963902638043406965 568657402865872316569403)
                    ·
                      rfl

theorem cell23_3322369_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 1, 1, 3, 2, 5].length) (baseStart_3322369 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3322369 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3322369 prefixEnd_3322369 := by exact prefixLift 3322369
  have htrace : WordTrace (prefixWord ++ tailWord_3322369) baseStart_3322369 baseEnd_3322369 := by
    simpa [prefixWord, tailWord_3322369, baseEnd_3322369] using wordTrace_append hprefix tailTrace_3322369
  have hstable : (prefixWord ++ tailWord_3322369).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3322369).length < 2 ^ (prefixWord ++ tailWord_3322369).sum := by decide
  have hdescent : baseEnd_3322369 < baseStart_3322369 := by decide
  rcases family_descends (prefixWord ++ tailWord_3322369) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3322389 : List Nat := [1, 3, 2, 1, 3, 1, 1, 4, 2, 1, 4]
def baseStart_3322389 : Nat := 118140960795 + 3322389 * 2 ^ 59
def prefixEnd_3322389 : Nat := 4983230072969 + 3 ^ 40 * 3322389 * 2
def baseEnd_3322389 : Nat := 1705982478210706871458117

theorem tailTrace_3322389 : CollatzResearch.WordTrace tailWord_3322389 prefixEnd_3322389 1705982478210706871458117 := by
  unfold tailWord_3322389
  simp only [CollatzResearch.WordTrace]
  refine ⟨121177481960559546711786221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80784987973706364474524147 121177481960559546711786221)
  ·
    refine ⟨45441555735209830016919833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 121177481960559546711786221 45441555735209830016919833)
    ·
      refine ⟨34081166801407372512689875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45441555735209830016919833 34081166801407372512689875)
      ·
        refine ⟨51121750202111058769034813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34081166801407372512689875 51121750202111058769034813)
        ·
          refine ⟨19170656325791647038388055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 51121750202111058769034813 19170656325791647038388055)
          ·
            refine ⟨28755984488687470557582083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19170656325791647038388055 28755984488687470557582083)
            ·
              refine ⟨43133976733031205836373125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28755984488687470557582083 43133976733031205836373125)
              ·
                refine ⟨8087620637443351094319961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 43133976733031205836373125 8087620637443351094319961)
                ·
                  refine ⟨6065715478082513320739971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8087620637443351094319961 6065715478082513320739971)
                  ·
                    refine ⟨9098573217123769981109957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6065715478082513320739971 9098573217123769981109957)
                    ·
                      refine ⟨1705982478210706871458117, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9098573217123769981109957 1705982478210706871458117)
                      ·
                        rfl

theorem cell23_3322389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 1, 4, 2, 1, 4].length) (baseStart_3322389 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3322389 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3322389 prefixEnd_3322389 := by exact prefixLift 3322389
  have htrace : WordTrace (prefixWord ++ tailWord_3322389) baseStart_3322389 baseEnd_3322389 := by
    simpa [prefixWord, tailWord_3322389, baseEnd_3322389] using wordTrace_append hprefix tailTrace_3322389
  have hstable : (prefixWord ++ tailWord_3322389).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3322389).length < 2 ^ (prefixWord ++ tailWord_3322389).sum := by decide
  have hdescent : baseEnd_3322389 < baseStart_3322389 := by decide
  rcases family_descends (prefixWord ++ tailWord_3322389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3322399 : List Nat := [1, 1, 2, 4, 1, 1, 1, 5, 3, 4]
def baseStart_3322399 : Nat := 118140960795 + 3322399 * 2 ^ 59
def prefixEnd_3322399 : Nat := 4983230072969 + 3 ^ 40 * 3322399 * 2
def baseEnd_3322399 : Nat := 568662537672417277444357

theorem tailTrace_3322399 : CollatzResearch.WordTrace tailWord_3322399 prefixEnd_3322399 568662537672417277444357 := by
  unfold tailWord_3322399
  simp only [CollatzResearch.WordTrace]
  refine ⟨121177846690523318419650251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80785231127015545613100167 121177846690523318419650251)
  ·
    refine ⟨181766770035784977629475377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121177846690523318419650251 181766770035784977629475377)
    ·
      refine ⟨136325077526838733222106533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 181766770035784977629475377 136325077526838733222106533)
      ·
        refine ⟨25560952036282262479144975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 136325077526838733222106533 25560952036282262479144975)
        ·
          refine ⟨38341428054423393718717463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25560952036282262479144975 38341428054423393718717463)
          ·
            refine ⟨57512142081635090578076195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38341428054423393718717463 57512142081635090578076195)
            ·
              refine ⟨86268213122452635867114293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 57512142081635090578076195 86268213122452635867114293)
              ·
                refine ⟨8087644980229934612541965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 86268213122452635867114293 8087644980229934612541965)
                ·
                  refine ⟨3032866867586225479703237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8087644980229934612541965 3032866867586225479703237)
                  ·
                    refine ⟨568662537672417277444357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3032866867586225479703237 568662537672417277444357)
                    ·
                      rfl

theorem cell23_3322399_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 1, 5, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 1, 5, 3, 4].length) (baseStart_3322399 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3322399 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3322399 prefixEnd_3322399 := by exact prefixLift 3322399
  have htrace : WordTrace (prefixWord ++ tailWord_3322399) baseStart_3322399 baseEnd_3322399 := by
    simpa [prefixWord, tailWord_3322399, baseEnd_3322399] using wordTrace_append hprefix tailTrace_3322399
  have hstable : (prefixWord ++ tailWord_3322399).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3322399).length < 2 ^ (prefixWord ++ tailWord_3322399).sum := by decide
  have hdescent : baseEnd_3322399 < baseStart_3322399 := by decide
  rcases family_descends (prefixWord ++ tailWord_3322399) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3322420 : List Nat := [2, 5, 1, 3, 1, 2, 1, 1, 2, 5]
def baseStart_3322420 : Nat := 118140960795 + 3322420 * 2 ^ 59
def prefixEnd_3322420 : Nat := 4983230072969 + 3 ^ 40 * 3322420 * 2
def baseEnd_3322420 : Nat := 568666132036998750056825

theorem tailTrace_3322420 : CollatzResearch.WordTrace tailWord_3322420 prefixEnd_3322420 568666132036998750056825 := by
  unfold tailWord_3322420
  simp only [CollatzResearch.WordTrace]
  refine ⟨60589306311723619503082357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80785741748964826004109809 60589306311723619503082357)
  ·
    refine ⟨5680247466724089328413971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 60589306311723619503082357 5680247466724089328413971)
    ·
      refine ⟨8520371200086133992620957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5680247466724089328413971 8520371200086133992620957)
      ·
        refine ⟨3195139200032300247232859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8520371200086133992620957 3195139200032300247232859)
        ·
          refine ⟨4792708800048450370849289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3195139200032300247232859 4792708800048450370849289)
          ·
            refine ⟨3594531600036337778136967, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4792708800048450370849289 3594531600036337778136967)
            ·
              refine ⟨5391797400054506667205451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3594531600036337778136967 5391797400054506667205451)
              ·
                refine ⟨8087696100081760000808177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5391797400054506667205451 8087696100081760000808177)
                ·
                  refine ⟨6065772075061320000606133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8087696100081760000808177 6065772075061320000606133)
                  ·
                    refine ⟨568666132036998750056825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6065772075061320000606133 568666132036998750056825)
                    ·
                      rfl

theorem cell23_3322420_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 3, 1, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 3, 1, 2, 1, 1, 2, 5].length) (baseStart_3322420 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3322420 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3322420 prefixEnd_3322420 := by exact prefixLift 3322420
  have htrace : WordTrace (prefixWord ++ tailWord_3322420) baseStart_3322420 baseEnd_3322420 := by
    simpa [prefixWord, tailWord_3322420, baseEnd_3322420] using wordTrace_append hprefix tailTrace_3322420
  have hstable : (prefixWord ++ tailWord_3322420).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3322420).length < 2 ^ (prefixWord ++ tailWord_3322420).sum := by decide
  have hdescent : baseEnd_3322420 < baseStart_3322420 := by decide
  rcases family_descends (prefixWord ++ tailWord_3322420) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3322426 : List Nat := [3, 1, 1, 1, 3, 3, 3, 1, 2, 2, 3]
def baseStart_3322426 : Nat := 118140960795 + 3322426 * 2 ^ 59
def prefixEnd_3322426 : Nat := 4983230072969 + 3 ^ 40 * 3322426 * 2
def baseEnd_3322426 : Nat := 1706001476994923226695447

theorem tailTrace_3322426 : CollatzResearch.WordTrace tailWord_3322426 prefixEnd_3322426 1706001476994923226695447 := by
  unfold tailWord_3322426
  simp only [CollatzResearch.WordTrace]
  refine ⟨30294707865356375507720783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 80785887640950334687255421 30294707865356375507720783)
  ·
    refine ⟨45442061798034563261581175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30294707865356375507720783 45442061798034563261581175)
    ·
      refine ⟨68163092697051844892371763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45442061798034563261581175 68163092697051844892371763)
      ·
        refine ⟨102244639045577767338557645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68163092697051844892371763 102244639045577767338557645)
        ·
          refine ⟨38341739642091662751959117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 102244639045577767338557645 38341739642091662751959117)
          ·
            refine ⟨14378152365784373531984669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 38341739642091662751959117 14378152365784373531984669)
            ·
              refine ⟨5391807137169140074494251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14378152365784373531984669 5391807137169140074494251)
              ·
                refine ⟨8087710705753710111741377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5391807137169140074494251 8087710705753710111741377)
                ·
                  refine ⟨6065783029315282583806033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8087710705753710111741377 6065783029315282583806033)
                  ·
                    refine ⟨4549337271986461937854525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6065783029315282583806033 4549337271986461937854525)
                    ·
                      refine ⟨1706001476994923226695447, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4549337271986461937854525 1706001476994923226695447)
                      ·
                        rfl

theorem cell23_3322426_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 3, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 3, 3, 1, 2, 2, 3].length) (baseStart_3322426 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3322426 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3322426 prefixEnd_3322426 := by exact prefixLift 3322426
  have htrace : WordTrace (prefixWord ++ tailWord_3322426) baseStart_3322426 baseEnd_3322426 := by
    simpa [prefixWord, tailWord_3322426, baseEnd_3322426] using wordTrace_append hprefix tailTrace_3322426
  have hstable : (prefixWord ++ tailWord_3322426).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3322426).length < 2 ^ (prefixWord ++ tailWord_3322426).sum := by decide
  have hdescent : baseEnd_3322426 < baseStart_3322426 := by decide
  rcases family_descends (prefixWord ++ tailWord_3322426) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3322433 : List Nat := [1, 2, 5, 1, 1, 2, 1, 5, 1, 4]
def baseStart_3322433 : Nat := 118140960795 + 3322433 * 2 ^ 59
def prefixEnd_3322433 : Nat := 4983230072969 + 3 ^ 40 * 3322433 * 2
def baseEnd_3322433 : Nat := 568668357119834899769305

theorem tailTrace_3322433 : CollatzResearch.WordTrace tailWord_3322433 prefixEnd_3322433 568668357119834899769305 := by
  unfold tailWord_3322433
  simp only [CollatzResearch.WordTrace]
  refine ⟨121179086772400142226387953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80786057848266761484258635 121179086772400142226387953)
  ·
    refine ⟨90884315079300106669790965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 121179086772400142226387953 90884315079300106669790965)
    ·
      refine ⟨8520404538684385000292903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 90884315079300106669790965 8520404538684385000292903)
      ·
        refine ⟨12780606808026577500439355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8520404538684385000292903 12780606808026577500439355)
        ·
          refine ⟨19170910212039866250659033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12780606808026577500439355 19170910212039866250659033)
          ·
            refine ⟨14378182659029899687994275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19170910212039866250659033 14378182659029899687994275)
            ·
              refine ⟨21567273988544849531991413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14378182659029899687994275 21567273988544849531991413)
              ·
                refine ⟨2021931936426079643624195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 21567273988544849531991413 2021931936426079643624195)
                ·
                  refine ⟨3032897904639119465436293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2021931936426079643624195 3032897904639119465436293)
                  ·
                    refine ⟨568668357119834899769305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3032897904639119465436293 568668357119834899769305)
                    ·
                      rfl

theorem cell23_3322433_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 2, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 2, 1, 5, 1, 4].length) (baseStart_3322433 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3322433 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3322433 prefixEnd_3322433 := by exact prefixLift 3322433
  have htrace : WordTrace (prefixWord ++ tailWord_3322433) baseStart_3322433 baseEnd_3322433 := by
    simpa [prefixWord, tailWord_3322433, baseEnd_3322433] using wordTrace_append hprefix tailTrace_3322433
  have hstable : (prefixWord ++ tailWord_3322433).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3322433).length < 2 ^ (prefixWord ++ tailWord_3322433).sum := by decide
  have hdescent : baseEnd_3322433 < baseStart_3322433 := by decide
  rcases family_descends (prefixWord ++ tailWord_3322433) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3322456 : List Nat := [2, 1, 2, 2, 1, 2, 3, 3, 3, 1, 3]
def baseStart_3322456 : Nat := 118140960795 + 3322456 * 2 ^ 59
def prefixEnd_3322456 : Nat := 4983230072969 + 3 ^ 40 * 3322456 * 2
def baseEnd_3322456 : Nat := 1706016881414558109320309

theorem tailTrace_3322456 : CollatzResearch.WordTrace tailWord_3322456 prefixEnd_3322456 1706016881414558109320309 := by
  unfold tailWord_3322456
  simp only [CollatzResearch.WordTrace]
  refine ⟨60589962825658408577237611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80786617100877878102983481 60589962825658408577237611)
  ·
    refine ⟨90884944238487612865856417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60589962825658408577237611 90884944238487612865856417)
    ·
      refine ⟨68163708178865709649392313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 90884944238487612865856417 68163708178865709649392313)
      ·
        refine ⟨51122781134149282237044235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 68163708178865709649392313 51122781134149282237044235)
        ·
          refine ⟨76684171701223923355566353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51122781134149282237044235 76684171701223923355566353)
          ·
            refine ⟨57513128775917942516674765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 76684171701223923355566353 57513128775917942516674765)
            ·
              refine ⟨21567423290969228443753037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 57513128775917942516674765 21567423290969228443753037)
              ·
                refine ⟨8087783734113460666407389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21567423290969228443753037 8087783734113460666407389)
                ·
                  refine ⟨3032918900292547749902771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8087783734113460666407389 3032918900292547749902771)
                  ·
                    refine ⟨4549378350438821624854157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3032918900292547749902771 4549378350438821624854157)
                    ·
                      refine ⟨1706016881414558109320309, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4549378350438821624854157 1706016881414558109320309)
                      ·
                        rfl

theorem cell23_3322456_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 3, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 3, 3, 3, 1, 3].length) (baseStart_3322456 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3322456 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3322456 prefixEnd_3322456 := by exact prefixLift 3322456
  have htrace : WordTrace (prefixWord ++ tailWord_3322456) baseStart_3322456 baseEnd_3322456 := by
    simpa [prefixWord, tailWord_3322456, baseEnd_3322456] using wordTrace_append hprefix tailTrace_3322456
  have hstable : (prefixWord ++ tailWord_3322456).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3322456).length < 2 ^ (prefixWord ++ tailWord_3322456).sum := by decide
  have hdescent : baseEnd_3322456 < baseStart_3322456 := by decide
  rcases family_descends (prefixWord ++ tailWord_3322456) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3322479 : List Nat := [1, 1, 2, 1, 3, 2, 2, 3, 3, 1, 4]
def baseStart_3322479 : Nat := 118140960795 + 3322479 * 2 ^ 59
def prefixEnd_3322479 : Nat := 4983230072969 + 3 ^ 40 * 3322479 * 2
def baseEnd_3322479 : Nat := 1706028691469611519332703

theorem tailTrace_3322479 : CollatzResearch.WordTrace tailWord_3322479 prefixEnd_3322479 1706028691469611519332703 := by
  unfold tailWord_3322479
  simp only [CollatzResearch.WordTrace]
  refine ⟨121180764530233492082562491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80787176353488994721708327 121180764530233492082562491)
  ·
    refine ⟨181771146795350238123843737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121180764530233492082562491 181771146795350238123843737)
    ·
      refine ⟨136328360096512678592882803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 181771146795350238123843737 136328360096512678592882803)
      ·
        refine ⟨204492540144769017889324205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 136328360096512678592882803 204492540144769017889324205)
        ·
          refine ⟨76684702554288381708496577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 204492540144769017889324205 76684702554288381708496577)
          ·
            refine ⟨57513526915716286281372433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 76684702554288381708496577 57513526915716286281372433)
            ·
              refine ⟨43135145186787214711029325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 57513526915716286281372433 43135145186787214711029325)
              ·
                refine ⟨16175679445045205516635997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 43135145186787214711029325 16175679445045205516635997)
                ·
                  refine ⟨6065879791891952068738499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16175679445045205516635997 6065879791891952068738499)
                  ·
                    refine ⟨9098819687837928103107749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6065879791891952068738499 9098819687837928103107749)
                    ·
                      refine ⟨1706028691469611519332703, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9098819687837928103107749 1706028691469611519332703)
                      ·
                        rfl

theorem cell23_3322479_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 2, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 2, 3, 3, 1, 4].length) (baseStart_3322479 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3322479 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3322479 prefixEnd_3322479 := by exact prefixLift 3322479
  have htrace : WordTrace (prefixWord ++ tailWord_3322479) baseStart_3322479 baseEnd_3322479 := by
    simpa [prefixWord, tailWord_3322479, baseEnd_3322479] using wordTrace_append hprefix tailTrace_3322479
  have hstable : (prefixWord ++ tailWord_3322479).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3322479).length < 2 ^ (prefixWord ++ tailWord_3322479).sum := by decide
  have hdescent : baseEnd_3322479 < baseStart_3322479 := by decide
  rcases family_descends (prefixWord ++ tailWord_3322479) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3322496 : List Nat := [2, 1, 1, 2, 1, 5, 2, 3, 1, 1, 4]
def baseStart_3322496 : Nat := 118140960795 + 3322496 * 2 ^ 59
def prefixEnd_3322496 : Nat := 4983230072969 + 3 ^ 40 * 3322496 * 2
def baseEnd_3322496 : Nat := 1706037420640737952820125

theorem tailTrace_3322496 : CollatzResearch.WordTrace tailWord_3322496 prefixEnd_3322496 1706037420640737952820125 := by
  unfold tailWord_3322496
  simp only [CollatzResearch.WordTrace]
  refine ⟨60590692285585951992965671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80787589714114602657287561 60590692285585951992965671)
  ·
    refine ⟨90886038428378927989448507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60590692285585951992965671 90886038428378927989448507)
    ·
      refine ⟨136329057642568391984172761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90886038428378927989448507 136329057642568391984172761)
      ·
        refine ⟨102246793231926293988129571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 136329057642568391984172761 102246793231926293988129571)
        ·
          refine ⟨153370189847889440982194357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 102246793231926293988129571 153370189847889440982194357)
          ·
            refine ⟨14378455298239635092080721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 153370189847889440982194357 14378455298239635092080721)
            ·
              refine ⟨10783841473679726319060541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14378455298239635092080721 10783841473679726319060541)
              ·
                refine ⟨4043940552629897369647703, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10783841473679726319060541 4043940552629897369647703)
                ·
                  refine ⟨6065910828944846054471555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4043940552629897369647703 6065910828944846054471555)
                  ·
                    refine ⟨9098866243417269081707333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6065910828944846054471555 9098866243417269081707333)
                    ·
                      refine ⟨1706037420640737952820125, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9098866243417269081707333 1706037420640737952820125)
                      ·
                        rfl

theorem cell23_3322496_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 5, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 5, 2, 3, 1, 1, 4].length) (baseStart_3322496 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3322496 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3322496 prefixEnd_3322496 := by exact prefixLift 3322496
  have htrace : WordTrace (prefixWord ++ tailWord_3322496) baseStart_3322496 baseEnd_3322496 := by
    simpa [prefixWord, tailWord_3322496, baseEnd_3322496] using wordTrace_append hprefix tailTrace_3322496
  have hstable : (prefixWord ++ tailWord_3322496).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3322496).length < 2 ^ (prefixWord ++ tailWord_3322496).sum := by decide
  have hdescent : baseEnd_3322496 < baseStart_3322496 := by decide
  rcases family_descends (prefixWord ++ tailWord_3322496) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3322499 : List Nat := [1, 1, 1, 3, 3, 1, 3, 3, 1, 1, 5]
def baseStart_3322499 : Nat := 118140960795 + 3322499 * 2 ^ 59
def prefixEnd_3322499 : Nat := 4983230072969 + 3 ^ 40 * 3322499 * 2
def baseEnd_3322499 : Nat := 1706038961082701441082611

theorem tailTrace_3322499 : CollatzResearch.WordTrace tailWord_3322499 prefixEnd_3322499 1706038961082701441082611 := by
  unfold tailWord_3322499
  simp only [CollatzResearch.WordTrace]
  refine ⟨121181493990161035498290551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80787662660107356998860367 121181493990161035498290551)
  ·
    refine ⟨181772240985241553247435827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121181493990161035498290551 181772240985241553247435827)
    ·
      refine ⟨272658361477862329871153741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 181772240985241553247435827 272658361477862329871153741)
      ·
        refine ⟨102246885554198373701682653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 272658361477862329871153741 102246885554198373701682653)
        ·
          refine ⟨38342582082824390138130995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 102246885554198373701682653 38342582082824390138130995)
          ·
            refine ⟨57513873124236585207196493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38342582082824390138130995 57513873124236585207196493)
            ·
              refine ⟨21567702421588719452698685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 57513873124236585207196493 21567702421588719452698685)
              ·
                refine ⟨8087888408095769794762007, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21567702421588719452698685 8087888408095769794762007)
                ·
                  refine ⟨12131832612143654692143011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8087888408095769794762007 12131832612143654692143011)
                  ·
                    refine ⟨18197748918215482038214517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12131832612143654692143011 18197748918215482038214517)
                    ·
                      refine ⟨1706038961082701441082611, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 18197748918215482038214517 1706038961082701441082611)
                      ·
                        rfl

theorem cell23_3322499_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 3, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 3, 3, 1, 1, 5].length) (baseStart_3322499 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3322499 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3322499 prefixEnd_3322499 := by exact prefixLift 3322499
  have htrace : WordTrace (prefixWord ++ tailWord_3322499) baseStart_3322499 baseEnd_3322499 := by
    simpa [prefixWord, tailWord_3322499, baseEnd_3322499] using wordTrace_append hprefix tailTrace_3322499
  have hstable : (prefixWord ++ tailWord_3322499).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3322499).length < 2 ^ (prefixWord ++ tailWord_3322499).sum := by decide
  have hdescent : baseEnd_3322499 < baseStart_3322499 := by decide
  rcases family_descends (prefixWord ++ tailWord_3322499) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3322519 : List Nat := [1, 1, 3, 3, 2, 1, 4, 8]
def baseStart_3322519 : Nat := 118140960795 + 3322519 * 2 ^ 59
def prefixEnd_3322519 : Nat := 4983230072969 + 3 ^ 40 * 3322519 * 2
def baseEnd_3322519 : Nat := 63187008544288568993797

theorem tailTrace_3322519 : CollatzResearch.WordTrace tailWord_3322519 prefixEnd_3322519 63187008544288568993797 := by
  unfold tailWord_3322519
  simp only [CollatzResearch.WordTrace]
  refine ⟨121182223450088578914018611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80788148966725719276012407 121182223450088578914018611)
  ·
    refine ⟨181773335175132868371027917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121182223450088578914018611 181773335175132868371027917)
    ·
      refine ⟨68165000690674825639135469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 181773335175132868371027917 68165000690674825639135469)
      ·
        refine ⟨25561875259003059614675801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 68165000690674825639135469 25561875259003059614675801)
        ·
          refine ⟨19171406444252294711006851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25561875259003059614675801 19171406444252294711006851)
          ·
            refine ⟨28757109666378442066510277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19171406444252294711006851 28757109666378442066510277)
            ·
              refine ⟨5391958062445957887470677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 28757109666378442066510277 5391958062445957887470677)
              ·
                refine ⟨63187008544288568993797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 5391958062445957887470677 63187008544288568993797)
                ·
                  rfl

theorem cell23_3322519_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 4, 8].length) (baseStart_3322519 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3322519 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3322519 prefixEnd_3322519 := by exact prefixLift 3322519
  have htrace : WordTrace (prefixWord ++ tailWord_3322519) baseStart_3322519 baseEnd_3322519 := by
    simpa [prefixWord, tailWord_3322519, baseEnd_3322519] using wordTrace_append hprefix tailTrace_3322519
  have hstable : (prefixWord ++ tailWord_3322519).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3322519).length < 2 ^ (prefixWord ++ tailWord_3322519).sum := by decide
  have hdescent : baseEnd_3322519 < baseStart_3322519 := by decide
  rcases family_descends (prefixWord ++ tailWord_3322519) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3322526 : List Nat := [4, 3, 1, 1, 1, 1, 1, 3, 1, 1, 6]
def baseStart_3322526 : Nat := 118140960795 + 3322526 * 2 ^ 59
def prefixEnd_3322526 : Nat := 4983230072969 + 3 ^ 40 * 3322526 * 2
def baseEnd_3322526 : Nat := 1706052825060372835444987

theorem tailTrace_3322526 : CollatzResearch.WordTrace tailWord_3322526 prefixEnd_3322526 1706052825060372835444987 := by
  unfold tailWord_3322526
  simp only [CollatzResearch.WordTrace]
  refine ⟨15147809845132902388690429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 80788319174042146073015621 15147809845132902388690429)
  ·
    refine ⟨5680428691924838395758911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15147809845132902388690429 5680428691924838395758911)
    ·
      refine ⟨8520643037887257593638367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5680428691924838395758911 8520643037887257593638367)
      ·
        refine ⟨12780964556830886390457551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8520643037887257593638367 12780964556830886390457551)
        ·
          refine ⟨19171446835246329585686327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12780964556830886390457551 19171446835246329585686327)
          ·
            refine ⟨28757170252869494378529491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19171446835246329585686327 28757170252869494378529491)
            ·
              refine ⟨43135755379304241567794237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28757170252869494378529491 43135755379304241567794237)
              ·
                refine ⟨16175908267239090587922839, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 43135755379304241567794237 16175908267239090587922839)
                ·
                  refine ⟨24263862400858635881884259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16175908267239090587922839 24263862400858635881884259)
                  ·
                    refine ⟨36395793601287953822826389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 24263862400858635881884259 36395793601287953822826389)
                    ·
                      refine ⟨1706052825060372835444987, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 36395793601287953822826389 1706052825060372835444987)
                      ·
                        rfl

theorem cell23_3322526_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 1, 3, 1, 1, 6].length) (baseStart_3322526 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3322526 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3322526 prefixEnd_3322526 := by exact prefixLift 3322526
  have htrace : WordTrace (prefixWord ++ tailWord_3322526) baseStart_3322526 baseEnd_3322526 := by
    simpa [prefixWord, tailWord_3322526, baseEnd_3322526] using wordTrace_append hprefix tailTrace_3322526
  have hstable : (prefixWord ++ tailWord_3322526).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3322526).length < 2 ^ (prefixWord ++ tailWord_3322526).sum := by decide
  have hdescent : baseEnd_3322526 < baseStart_3322526 := by decide
  rcases family_descends (prefixWord ++ tailWord_3322526) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3322564 : List Nat := [2, 3, 3, 1, 1, 2, 4, 2, 1, 2, 2]
def baseStart_3322564 : Nat := 118140960795 + 3322564 * 2 ^ 59
def prefixEnd_3322564 : Nat := 4983230072969 + 3 ^ 40 * 3322564 * 2
def baseEnd_3322564 : Nat := 1706072337325243686769813

theorem tailTrace_3322564 : CollatzResearch.WordTrace tailWord_3322564 prefixEnd_3322564 1706072337325243686769813 := by
  unfold tailWord_3322564
  simp only [CollatzResearch.WordTrace]
  refine ⟨60591932367462775799703373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80789243156617034399604497 60591932367462775799703373)
  ·
    refine ⟨22721974637798540924888765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 60591932367462775799703373 22721974637798540924888765)
    ·
      refine ⟨8520740489174452846833287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22721974637798540924888765 8520740489174452846833287)
      ·
        refine ⟨12781110733761679270249931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8520740489174452846833287 12781110733761679270249931)
        ·
          refine ⟨19171666100642518905374897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12781110733761679270249931 19171666100642518905374897)
          ·
            refine ⟨14378749575481889179031173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19171666100642518905374897 14378749575481889179031173)
            ·
              refine ⟨2696015545402854221068345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 14378749575481889179031173 2696015545402854221068345)
              ·
                refine ⟨2022011659052140665801259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2696015545402854221068345 2022011659052140665801259)
                ·
                  refine ⟨3033017488578210998701889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2022011659052140665801259 3033017488578210998701889)
                  ·
                    refine ⟨2274763116433658249026417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3033017488578210998701889 2274763116433658249026417)
                    ·
                      refine ⟨1706072337325243686769813, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2274763116433658249026417 1706072337325243686769813)
                      ·
                        rfl

theorem cell23_3322564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 2, 4, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 2, 4, 2, 1, 2, 2].length) (baseStart_3322564 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3322564 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3322564 prefixEnd_3322564 := by exact prefixLift 3322564
  have htrace : WordTrace (prefixWord ++ tailWord_3322564) baseStart_3322564 baseEnd_3322564 := by
    simpa [prefixWord, tailWord_3322564, baseEnd_3322564] using wordTrace_append hprefix tailTrace_3322564
  have hstable : (prefixWord ++ tailWord_3322564).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3322564).length < 2 ^ (prefixWord ++ tailWord_3322564).sum := by decide
  have hdescent : baseEnd_3322564 < baseStart_3322564 := by decide
  rcases family_descends (prefixWord ++ tailWord_3322564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3322580 : List Nat := [2, 4, 1, 3, 2, 1, 2, 1, 1, 3, 3]
def baseStart_3322580 : Nat := 118140960795 + 3322580 * 2 ^ 59
def prefixEnd_3322580 : Nat := 4983230072969 + 3 ^ 40 * 3322580 * 2
def baseEnd_3322580 : Nat := 1706080553015715624169739

theorem tailTrace_3322580 : CollatzResearch.WordTrace tailWord_3322580 prefixEnd_3322580 1706080553015715624169739 := by
  unfold tailWord_3322580
  simp only [CollatzResearch.WordTrace]
  refine ⟨60592224151433793165994597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80789632201911724221326129 60592224151433793165994597)
  ·
    refine ⟨11361042028393836218623987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 60592224151433793165994597 11361042028393836218623987)
    ·
      refine ⟨17041563042590754327935981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11361042028393836218623987 17041563042590754327935981)
      ·
        refine ⟨6390586140971532872975993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17041563042590754327935981 6390586140971532872975993)
        ·
          refine ⟨4792939605728649654731995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6390586140971532872975993 4792939605728649654731995)
          ·
            refine ⟨7189409408592974482097993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4792939605728649654731995 7189409408592974482097993)
            ·
              refine ⟨5392057056444730861573495, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7189409408592974482097993 5392057056444730861573495)
              ·
                refine ⟨8088085584667096292360243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5392057056444730861573495 8088085584667096292360243)
                ·
                  refine ⟨12132128377000644438540365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8088085584667096292360243 12132128377000644438540365)
                  ·
                    refine ⟨4549548141375241664452637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12132128377000644438540365 4549548141375241664452637)
                    ·
                      refine ⟨1706080553015715624169739, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4549548141375241664452637 1706080553015715624169739)
                      ·
                        rfl

theorem cell23_3322580_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 2, 1, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 2, 1, 2, 1, 1, 3, 3].length) (baseStart_3322580 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3322580 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3322580 prefixEnd_3322580 := by exact prefixLift 3322580
  have htrace : WordTrace (prefixWord ++ tailWord_3322580) baseStart_3322580 baseEnd_3322580 := by
    simpa [prefixWord, tailWord_3322580, baseEnd_3322580] using wordTrace_append hprefix tailTrace_3322580
  have hstable : (prefixWord ++ tailWord_3322580).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3322580).length < 2 ^ (prefixWord ++ tailWord_3322580).sum := by decide
  have hdescent : baseEnd_3322580 < baseStart_3322580 := by decide
  rcases family_descends (prefixWord ++ tailWord_3322580) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3322603 : List Nat := [1, 1, 1, 1, 2, 4, 1, 4, 4, 2, 2]
def baseStart_3322603 : Nat := 118140960795 + 3322603 * 2 ^ 59
def prefixEnd_3322603 : Nat := 4983230072969 + 3 ^ 40 * 3322603 * 2
def baseEnd_3322603 : Nat := 1706092363070769034182133

theorem tailTrace_3322603 : CollatzResearch.WordTrace tailWord_3322603 prefixEnd_3322603 1706092363070769034182133 := by
  unfold tailWord_3322603
  simp only [CollatzResearch.WordTrace]
  refine ⟨121185287181784261260076463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80790191454522840840050975 121185287181784261260076463)
  ·
    refine ⟨181777930772676391890114695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121185287181784261260076463 181777930772676391890114695)
    ·
      refine ⟨272666896159014587835172043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 181777930772676391890114695 272666896159014587835172043)
      ·
        refine ⟨409000344238521881752758065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 272666896159014587835172043 409000344238521881752758065)
        ·
          refine ⟨306750258178891411314568549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 409000344238521881752758065 306750258178891411314568549)
          ·
            refine ⟨57515673408542139621481603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 306750258178891411314568549 57515673408542139621481603)
            ·
              refine ⟨86273510112813209432222405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 57515673408542139621481603 86273510112813209432222405)
              ·
                refine ⟨16176283146152476768541701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 86273510112813209432222405 16176283146152476768541701)
                ·
                  refine ⟨3033053089903589394101569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 16176283146152476768541701 3033053089903589394101569)
                  ·
                    refine ⟨2274789817427692045576177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3033053089903589394101569 2274789817427692045576177)
                    ·
                      refine ⟨1706092363070769034182133, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2274789817427692045576177 1706092363070769034182133)
                      ·
                        rfl

theorem cell23_3322603_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 1, 4, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 1, 4, 4, 2, 2].length) (baseStart_3322603 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3322603 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3322603 prefixEnd_3322603 := by exact prefixLift 3322603
  have htrace : WordTrace (prefixWord ++ tailWord_3322603) baseStart_3322603 baseEnd_3322603 := by
    simpa [prefixWord, tailWord_3322603, baseEnd_3322603] using wordTrace_append hprefix tailTrace_3322603
  have hstable : (prefixWord ++ tailWord_3322603).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3322603).length < 2 ^ (prefixWord ++ tailWord_3322603).sum := by decide
  have hdescent : baseEnd_3322603 < baseStart_3322603 := by decide
  rcases family_descends (prefixWord ++ tailWord_3322603) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3322607 : List Nat := [1, 1, 2, 1, 5, 4, 2, 1, 1, 3, 2]
def baseStart_3322607 : Nat := 118140960795 + 3322607 * 2 ^ 59
def prefixEnd_3322607 : Nat := 4983230072969 + 3 ^ 40 * 3322607 * 2
def baseEnd_3322607 : Nat := 1706094416993387018532115

theorem tailTrace_3322607 : CollatzResearch.WordTrace tailWord_3322607 prefixEnd_3322607 1706094416993387018532115 := by
  unfold tailWord_3322607
  simp only [CollatzResearch.WordTrace]
  refine ⟨121185433073769769943222075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80790288715846513295481383 121185433073769769943222075)
  ·
    refine ⟨181778149610654654914833113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121185433073769769943222075 181778149610654654914833113)
    ·
      refine ⟨136333612207990991186124835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 181778149610654654914833113 136333612207990991186124835)
      ·
        refine ⟨204500418311986486779187253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 136333612207990991186124835 204500418311986486779187253)
        ·
          refine ⟨19171914216748733135548805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 204500418311986486779187253 19171914216748733135548805)
          ·
            refine ⟨3594733915640387462915401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 19171914216748733135548805 3594733915640387462915401)
            ·
              refine ⟨2696050436730290597186551, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3594733915640387462915401 2696050436730290597186551)
              ·
                refine ⟨4044075655095435895779827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2696050436730290597186551 4044075655095435895779827)
                ·
                  refine ⟨6066113482643153843669741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4044075655095435895779827 6066113482643153843669741)
                  ·
                    refine ⟨2274792555991182691376153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6066113482643153843669741 2274792555991182691376153)
                    ·
                      refine ⟨1706094416993387018532115, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2274792555991182691376153 1706094416993387018532115)
                      ·
                        rfl

theorem cell23_3322607_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 4, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 4, 2, 1, 1, 3, 2].length) (baseStart_3322607 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3322607 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3322607 prefixEnd_3322607 := by exact prefixLift 3322607
  have htrace : WordTrace (prefixWord ++ tailWord_3322607) baseStart_3322607 baseEnd_3322607 := by
    simpa [prefixWord, tailWord_3322607, baseEnd_3322607] using wordTrace_append hprefix tailTrace_3322607
  have hstable : (prefixWord ++ tailWord_3322607).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3322607).length < 2 ^ (prefixWord ++ tailWord_3322607).sum := by decide
  have hdescent : baseEnd_3322607 < baseStart_3322607 := by decide
  rcases family_descends (prefixWord ++ tailWord_3322607) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3322609 : List Nat := [1, 2, 2, 2, 2, 2, 1, 2, 9]
def baseStart_3322609 : Nat := 118140960795 + 3322609 * 2 ^ 59
def prefixEnd_3322609 : Nat := 4983230072969 + 3 ^ 40 * 3322609 * 2
def baseEnd_3322609 : Nat := 189566160439410667856345

theorem tailTrace_3322609 : CollatzResearch.WordTrace tailWord_3322609 prefixEnd_3322609 189566160439410667856345 := by
  unfold tailWord_3322609
  simp only [CollatzResearch.WordTrace]
  refine ⟨121185506019762524284794881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80790337346508349523196587 121185506019762524284794881)
  ·
    refine ⟨90889129514821893213596161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 121185506019762524284794881 90889129514821893213596161)
    ·
      refine ⟨68166847136116419910197121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 90889129514821893213596161 68166847136116419910197121)
      ·
        refine ⟨51125135352087314932647841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 68166847136116419910197121 51125135352087314932647841)
        ·
          refine ⟨38343851514065486199485881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51125135352087314932647841 38343851514065486199485881)
          ·
            refine ⟨28757888635549114649614411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38343851514065486199485881 28757888635549114649614411)
            ·
              refine ⟨43136832953323671974421617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28757888635549114649614411 43136832953323671974421617)
              ·
                refine ⟨32352624714992753980816213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 43136832953323671974421617 32352624714992753980816213)
                ·
                  refine ⟨189566160439410667856345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 32352624714992753980816213 189566160439410667856345)
                  ·
                    rfl

theorem cell23_3322609_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 1, 2, 9].length) (baseStart_3322609 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3322609 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3322609 prefixEnd_3322609 := by exact prefixLift 3322609
  have htrace : WordTrace (prefixWord ++ tailWord_3322609) baseStart_3322609 baseEnd_3322609 := by
    simpa [prefixWord, tailWord_3322609, baseEnd_3322609] using wordTrace_append hprefix tailTrace_3322609
  have hstable : (prefixWord ++ tailWord_3322609).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3322609).length < 2 ^ (prefixWord ++ tailWord_3322609).sum := by decide
  have hdescent : baseEnd_3322609 < baseStart_3322609 := by decide
  rcases family_descends (prefixWord ++ tailWord_3322609) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3322620 : List Nat := [2, 2, 2, 1, 3, 3, 1, 1, 4, 2, 2]
def baseStart_3322620 : Nat := 118140960795 + 3322620 * 2 ^ 59
def prefixEnd_3322620 : Nat := 4983230072969 + 3 ^ 40 * 3322620 * 2
def baseEnd_3322620 : Nat := 1706101092241895467669555

theorem tailTrace_3322620 : CollatzResearch.WordTrace tailWord_3322620 prefixEnd_3322620 1706101092241895467669555 := by
  unfold tailWord_3322620
  simp only [CollatzResearch.WordTrace]
  refine ⟨60592953611361336581722657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80790604815148448775630209 60592953611361336581722657)
  ·
    refine ⟨45444715208521002436291993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60592953611361336581722657 45444715208521002436291993)
    ·
      refine ⟨34083536406390751827218995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45444715208521002436291993 34083536406390751827218995)
      ·
        refine ⟨51125304609586127740828493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34083536406390751827218995 51125304609586127740828493)
        ·
          refine ⟨19171989228594797902810685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 51125304609586127740828493 19171989228594797902810685)
          ·
            refine ⟨7189495960723049213554007, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19171989228594797902810685 7189495960723049213554007)
            ·
              refine ⟨10784243941084573820331011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7189495960723049213554007 10784243941084573820331011)
              ·
                refine ⟨16176365911626860730496517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10784243941084573820331011 16176365911626860730496517)
                ·
                  refine ⟨3033068608430036386968097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 16176365911626860730496517 3033068608430036386968097)
                  ·
                    refine ⟨2274801456322527290226073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3033068608430036386968097 2274801456322527290226073)
                    ·
                      refine ⟨1706101092241895467669555, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2274801456322527290226073 1706101092241895467669555)
                      ·
                        rfl

theorem cell23_3322620_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 3, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 3, 1, 1, 4, 2, 2].length) (baseStart_3322620 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3322620 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3322620 prefixEnd_3322620 := by exact prefixLift 3322620
  have htrace : WordTrace (prefixWord ++ tailWord_3322620) baseStart_3322620 baseEnd_3322620 := by
    simpa [prefixWord, tailWord_3322620, baseEnd_3322620] using wordTrace_append hprefix tailTrace_3322620
  have hstable : (prefixWord ++ tailWord_3322620).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3322620).length < 2 ^ (prefixWord ++ tailWord_3322620).sum := by decide
  have hdescent : baseEnd_3322620 < baseStart_3322620 := by decide
  rcases family_descends (prefixWord ++ tailWord_3322620) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3322639 : List Nat := [1, 1, 2, 1, 1, 1, 5, 1, 3, 7]
def baseStart_3322639 : Nat := 118140960795 + 3322639 * 2 ^ 59
def prefixEnd_3322639 : Nat := 4983230072969 + 3 ^ 40 * 3322639 * 2
def baseEnd_3322639 : Nat := 568703616124776964443989

theorem tailTrace_3322639 : CollatzResearch.WordTrace tailWord_3322639 prefixEnd_3322639 568703616124776964443989 := by
  unfold tailWord_3322639
  simp only [CollatzResearch.WordTrace]
  refine ⟨121186600209653839408386971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80791066806435892938924647 121186600209653839408386971)
  ·
    refine ⟨181779900314480759112580457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121186600209653839408386971 181779900314480759112580457)
    ·
      refine ⟨136334925235860569334435343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 181779900314480759112580457 136334925235860569334435343)
      ·
        refine ⟨204502387853790854001653015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 136334925235860569334435343 204502387853790854001653015)
        ·
          refine ⟨306753581780686281002479523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 204502387853790854001653015 306753581780686281002479523)
          ·
            refine ⟨460130372671029421503719285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 306753581780686281002479523 460130372671029421503719285)
            ·
              refine ⟨43137222437909008265973683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 460130372671029421503719285 43137222437909008265973683)
              ·
                refine ⟨64705833656863512398960525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43137222437909008265973683 64705833656863512398960525)
                ·
                  refine ⟨24264687621323817149610197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 64705833656863512398960525 24264687621323817149610197)
                  ·
                    refine ⟨568703616124776964443989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 24264687621323817149610197 568703616124776964443989)
                    ·
                      rfl

theorem cell23_3322639_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 5, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 5, 1, 3, 7].length) (baseStart_3322639 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3322639 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3322639 prefixEnd_3322639 := by exact prefixLift 3322639
  have htrace : WordTrace (prefixWord ++ tailWord_3322639) baseStart_3322639 baseEnd_3322639 := by
    simpa [prefixWord, tailWord_3322639, baseEnd_3322639] using wordTrace_append hprefix tailTrace_3322639
  have hstable : (prefixWord ++ tailWord_3322639).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3322639).length < 2 ^ (prefixWord ++ tailWord_3322639).sum := by decide
  have hdescent : baseEnd_3322639 < baseStart_3322639 := by decide
  rcases family_descends (prefixWord ++ tailWord_3322639) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3322649 : List Nat := [1, 2, 1, 2, 1, 1, 1, 3, 3, 1, 7]
def baseStart_3322649 : Nat := 118140960795 + 3322649 * 2 ^ 59
def prefixEnd_3322649 : Nat := 4983230072969 + 3 ^ 40 * 3322649 * 2
def baseEnd_3322649 : Nat := 1706115983180875854206921

theorem tailTrace_3322649 : CollatzResearch.WordTrace tailWord_3322649 prefixEnd_3322649 1706115983180875854206921 := by
  unfold tailWord_3322649
  simp only [CollatzResearch.WordTrace]
  refine ⟨121186964939617611116251001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80791309959745074077500667 121186964939617611116251001)
  ·
    refine ⟨90890223704713208337188251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 121186964939617611116251001 90890223704713208337188251)
    ·
      refine ⟨136335335557069812505782377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90890223704713208337188251 136335335557069812505782377)
      ·
        refine ⟨102251501667802359379336783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 136335335557069812505782377 102251501667802359379336783)
        ·
          refine ⟨153377252501703539069005175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 102251501667802359379336783 153377252501703539069005175)
          ·
            refine ⟨230065878752555308603507763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 153377252501703539069005175 230065878752555308603507763)
            ·
              refine ⟨345098818128832962905261645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 230065878752555308603507763 345098818128832962905261645)
              ·
                refine ⟨129412056798312361089473117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 345098818128832962905261645 129412056798312361089473117)
                ·
                  refine ⟨48529521299367135408552419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 129412056798312361089473117 48529521299367135408552419)
                  ·
                    refine ⟨72794281949050703112828629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 48529521299367135408552419 72794281949050703112828629)
                    ·
                      refine ⟨1706115983180875854206921, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 72794281949050703112828629 1706115983180875854206921)
                      ·
                        rfl

theorem cell23_3322649_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 3, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 3, 3, 1, 7].length) (baseStart_3322649 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3322649 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3322649 prefixEnd_3322649 := by exact prefixLift 3322649
  have htrace : WordTrace (prefixWord ++ tailWord_3322649) baseStart_3322649 baseEnd_3322649 := by
    simpa [prefixWord, tailWord_3322649, baseEnd_3322649] using wordTrace_append hprefix tailTrace_3322649
  have hstable : (prefixWord ++ tailWord_3322649).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3322649).length < 2 ^ (prefixWord ++ tailWord_3322649).sum := by decide
  have hdescent : baseEnd_3322649 < baseStart_3322649 := by decide
  rcases family_descends (prefixWord ++ tailWord_3322649) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3322656 : List Nat := [2, 1, 1, 5, 1, 2, 2, 1, 1, 7]
def baseStart_3322656 : Nat := 118140960795 + 3322656 * 2 ^ 59
def prefixEnd_3322656 : Nat := 4983230072969 + 3 ^ 40 * 3322656 * 2
def baseEnd_3322656 : Nat := 568706525848485775606463

theorem tailTrace_3322656 : CollatzResearch.WordTrace tailWord_3322656 prefixEnd_3322656 568706525848485775606463 := by
  unfold tailWord_3322656
  simp only [CollatzResearch.WordTrace]
  refine ⟨60593610125296125655877911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80791480167061500874503881 60593610125296125655877911)
  ·
    refine ⟨90890415187944188483816867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60593610125296125655877911 90890415187944188483816867)
    ·
      refine ⟨136335622781916282725725301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90890415187944188483816867 136335622781916282725725301)
      ·
        refine ⟨12781464635804651505536747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 136335622781916282725725301 12781464635804651505536747)
        ·
          refine ⟨19172196953706977258305121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12781464635804651505536747 19172196953706977258305121)
          ·
            refine ⟨14379147715280232943728841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19172196953706977258305121 14379147715280232943728841)
            ·
              refine ⟨10784360786460174707796631, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14379147715280232943728841 10784360786460174707796631)
              ·
                refine ⟨16176541179690262061694947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10784360786460174707796631 16176541179690262061694947)
                ·
                  refine ⟨24264811769535393092542421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16176541179690262061694947 24264811769535393092542421)
                  ·
                    refine ⟨568706525848485775606463, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 24264811769535393092542421 568706525848485775606463)
                    ·
                      rfl

theorem cell23_3322656_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 2, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 2, 2, 1, 1, 7].length) (baseStart_3322656 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3322656 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3322656 prefixEnd_3322656 := by exact prefixLift 3322656
  have htrace : WordTrace (prefixWord ++ tailWord_3322656) baseStart_3322656 baseEnd_3322656 := by
    simpa [prefixWord, tailWord_3322656, baseEnd_3322656] using wordTrace_append hprefix tailTrace_3322656
  have hstable : (prefixWord ++ tailWord_3322656).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3322656).length < 2 ^ (prefixWord ++ tailWord_3322656).sum := by decide
  have hdescent : baseEnd_3322656 < baseStart_3322656 := by decide
  rcases family_descends (prefixWord ++ tailWord_3322656) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3322713 : List Nat := [1, 2, 1, 2, 2, 4, 1, 3, 2, 2, 3]
def baseStart_3322713 : Nat := 118140960795 + 3322713 * 2 ^ 59
def prefixEnd_3322713 : Nat := 4983230072969 + 3 ^ 40 * 3322713 * 2
def baseEnd_3322713 : Nat := 1706148845942763603806627

theorem tailTrace_3322713 : CollatzResearch.WordTrace tailWord_3322713 prefixEnd_3322713 1706148845942763603806627 := by
  unfold tailWord_3322713
  simp only [CollatzResearch.WordTrace]
  refine ⟨121189299211385750046580793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80792866140923833364387195 121189299211385750046580793)
  ·
    refine ⟨90891974408539312534935595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 121189299211385750046580793 90891974408539312534935595)
    ·
      refine ⟨136337961612808968802403393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90891974408539312534935595 136337961612808968802403393)
      ·
        refine ⟨102253471209606726601802545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 136337961612808968802403393 102253471209606726601802545)
        ·
          refine ⟨76690103407205044951351909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 102253471209606726601802545 76690103407205044951351909)
          ·
            refine ⟨14379394388850945928378483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 76690103407205044951351909 14379394388850945928378483)
            ·
              refine ⟨21569091583276418892567725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14379394388850945928378483 21569091583276418892567725)
              ·
                refine ⟨8088409343728657084712897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21569091583276418892567725 8088409343728657084712897)
                ·
                  refine ⟨6066307007796492813534673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8088409343728657084712897 6066307007796492813534673)
                  ·
                    refine ⟨4549730255847369610151005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6066307007796492813534673 4549730255847369610151005)
                    ·
                      refine ⟨1706148845942763603806627, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4549730255847369610151005 1706148845942763603806627)
                      ·
                        rfl

theorem cell23_3322713_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 4, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 4, 1, 3, 2, 2, 3].length) (baseStart_3322713 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3322713 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3322713 prefixEnd_3322713 := by exact prefixLift 3322713
  have htrace : WordTrace (prefixWord ++ tailWord_3322713) baseStart_3322713 baseEnd_3322713 := by
    simpa [prefixWord, tailWord_3322713, baseEnd_3322713] using wordTrace_append hprefix tailTrace_3322713
  have hstable : (prefixWord ++ tailWord_3322713).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3322713).length < 2 ^ (prefixWord ++ tailWord_3322713).sum := by decide
  have hdescent : baseEnd_3322713 < baseStart_3322713 := by decide
  rcases family_descends (prefixWord ++ tailWord_3322713) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3322720 : List Nat := [2, 1, 1, 3, 3, 1, 2, 5, 1, 4]
def baseStart_3322720 : Nat := 118140960795 + 3322720 * 2 ^ 59
def prefixEnd_3322720 : Nat := 4983230072969 + 3 ^ 40 * 3322720 * 2
def baseEnd_3322720 : Nat := 568717480102448358806365

theorem tailTrace_3322720 : CollatzResearch.WordTrace tailWord_3322720 prefixEnd_3322720 568717480102448358806365 := by
  unfold tailWord_3322720
  simp only [CollatzResearch.WordTrace]
  refine ⟨60594777261180195121042807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80793036348240260161390409 60594777261180195121042807)
  ·
    refine ⟨90892165891770292681564211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60594777261180195121042807 90892165891770292681564211)
    ·
      refine ⟨136338248837655439022346317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90892165891770292681564211 136338248837655439022346317)
      ·
        refine ⟨51126843314120789633379869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 136338248837655439022346317 51126843314120789633379869)
        ·
          refine ⟨19172566242795296112517451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 51126843314120789633379869 19172566242795296112517451)
          ·
            refine ⟨28758849364192944168776177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19172566242795296112517451 28758849364192944168776177)
            ·
              refine ⟨21569137023144708126582133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28758849364192944168776177 21569137023144708126582133)
              ·
                refine ⟨2022106595919816386867075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 21569137023144708126582133 2022106595919816386867075)
                ·
                  refine ⟨3033159893879724580300613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2022106595919816386867075 3033159893879724580300613)
                  ·
                    refine ⟨568717480102448358806365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3033159893879724580300613 568717480102448358806365)
                    ·
                      rfl

theorem cell23_3322720_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 2, 5, 1, 4].length) (baseStart_3322720 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3322720 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3322720 prefixEnd_3322720 := by exact prefixLift 3322720
  have htrace : WordTrace (prefixWord ++ tailWord_3322720) baseStart_3322720 baseEnd_3322720 := by
    simpa [prefixWord, tailWord_3322720, baseEnd_3322720] using wordTrace_append hprefix tailTrace_3322720
  have hstable : (prefixWord ++ tailWord_3322720).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3322720).length < 2 ^ (prefixWord ++ tailWord_3322720).sum := by decide
  have hdescent : baseEnd_3322720 < baseStart_3322720 := by decide
  rcases family_descends (prefixWord ++ tailWord_3322720) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3322737 : List Nat := [1, 2, 2, 2, 1, 4, 4, 2, 1, 4]
def baseStart_3322737 : Nat := 118140960795 + 3322737 * 2 ^ 59
def prefixEnd_3322737 : Nat := 4983230072969 + 3 ^ 40 * 3322737 * 2
def baseEnd_3322737 : Nat := 568720389826157169968839

theorem tailTrace_3322737 : CollatzResearch.WordTrace tailWord_3322737 prefixEnd_3322737 568720389826157169968839 := by
  unfold tailWord_3322737
  simp only [CollatzResearch.WordTrace]
  refine ⟨121190174563298802145454465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80793449708865868096969643 121190174563298802145454465)
  ·
    refine ⟨90892630922474101609090849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 121190174563298802145454465 90892630922474101609090849)
    ·
      refine ⟨68169473191855576206818137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 90892630922474101609090849 68169473191855576206818137)
      ·
        refine ⟨51127104893891682155113603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 68169473191855576206818137 51127104893891682155113603)
        ·
          refine ⟨76690657340837523232670405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51127104893891682155113603 76690657340837523232670405)
          ·
            refine ⟨14379498251407035606125701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 76690657340837523232670405 14379498251407035606125701)
            ·
              refine ⟨2696155922138819176148569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 14379498251407035606125701 2696155922138819176148569)
              ·
                refine ⟨2022116941604114382111427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2696155922138819176148569 2022116941604114382111427)
                ·
                  refine ⟨3033175412406171573167141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2022116941604114382111427 3033175412406171573167141)
                  ·
                    refine ⟨568720389826157169968839, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3033175412406171573167141 568720389826157169968839)
                    ·
                      rfl

theorem cell23_3322737_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 4, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 4, 4, 2, 1, 4].length) (baseStart_3322737 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3322737 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3322737 prefixEnd_3322737 := by exact prefixLift 3322737
  have htrace : WordTrace (prefixWord ++ tailWord_3322737) baseStart_3322737 baseEnd_3322737 := by
    simpa [prefixWord, tailWord_3322737, baseEnd_3322737] using wordTrace_append hprefix tailTrace_3322737
  have hstable : (prefixWord ++ tailWord_3322737).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3322737).length < 2 ^ (prefixWord ++ tailWord_3322737).sum := by decide
  have hdescent : baseEnd_3322737 < baseStart_3322737 := by decide
  rcases family_descends (prefixWord ++ tailWord_3322737) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3322743 : List Nat := [1, 1, 3, 1, 1, 2, 1, 2, 7, 1, 3]
def baseStart_3322743 : Nat := 118140960795 + 3322743 * 2 ^ 59
def prefixEnd_3322743 : Nat := 4983230072969 + 3 ^ 40 * 3322743 * 2
def baseEnd_3322743 : Nat := 1706164250362398486431489

theorem tailTrace_3322743 : CollatzResearch.WordTrace tailWord_3322743 prefixEnd_3322743 1706164250362398486431489 := by
  unfold tailWord_3322743
  simp only [CollatzResearch.WordTrace]
  refine ⟨121190393401277065170172883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80793595600851376780115255 121190393401277065170172883)
  ·
    refine ⟨181785590101915597755259325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121190393401277065170172883 181785590101915597755259325)
    ·
      refine ⟨68169596288218349158222247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 181785590101915597755259325 68169596288218349158222247)
      ·
        refine ⟨102254394432327523737333371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68169596288218349158222247 102254394432327523737333371)
        ·
          refine ⟨153381591648491285606000057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 102254394432327523737333371 153381591648491285606000057)
          ·
            refine ⟨115036193736368464204500043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 153381591648491285606000057 115036193736368464204500043)
            ·
              refine ⟨172554290604552696306750065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 115036193736368464204500043 172554290604552696306750065)
              ·
                refine ⟨129415717953414522230062549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 172554290604552696306750065 129415717953414522230062549)
                ·
                  refine ⟨3033180889533152864767091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 129415717953414522230062549 3033180889533152864767091)
                  ·
                    refine ⟨4549771334299729297150637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3033180889533152864767091 4549771334299729297150637)
                    ·
                      refine ⟨1706164250362398486431489, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4549771334299729297150637 1706164250362398486431489)
                      ·
                        rfl

theorem cell23_3322743_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 1, 2, 7, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 1, 2, 7, 1, 3].length) (baseStart_3322743 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3322743 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3322743 prefixEnd_3322743 := by exact prefixLift 3322743
  have htrace : WordTrace (prefixWord ++ tailWord_3322743) baseStart_3322743 baseEnd_3322743 := by
    simpa [prefixWord, tailWord_3322743, baseEnd_3322743] using wordTrace_append hprefix tailTrace_3322743
  have hstable : (prefixWord ++ tailWord_3322743).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3322743).length < 2 ^ (prefixWord ++ tailWord_3322743).sum := by decide
  have hdescent : baseEnd_3322743 < baseStart_3322743 := by decide
  rcases family_descends (prefixWord ++ tailWord_3322743) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3322754 : List Nat := [3, 4, 2, 2, 1, 1, 1, 2, 3, 4]
def baseStart_3322754 : Nat := 118140960795 + 3322754 * 2 ^ 59
def prefixEnd_3322754 : Nat := 4983230072969 + 3 ^ 40 * 3322754 * 2
def baseEnd_3322754 : Nat := 568723299549865981131313

theorem tailTrace_3322754 : CollatzResearch.WordTrace tailWord_3322754 prefixEnd_3322754 568723299549865981131313 := by
  unfold tailWord_3322754
  simp only [CollatzResearch.WordTrace]
  refine ⟨30297698651059303512205829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 80793863069491476032548877 30297698651059303512205829)
  ·
    refine ⟨5680818497073619408538593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 30297698651059303512205829 5680818497073619408538593)
    ·
      refine ⟨4260613872805214556403945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5680818497073619408538593 4260613872805214556403945)
      ·
        refine ⟨3195460404603910917302959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4260613872805214556403945 3195460404603910917302959)
        ·
          refine ⟨4793190606905866375954439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3195460404603910917302959 4793190606905866375954439)
          ·
            refine ⟨7189785910358799563931659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4793190606905866375954439 7189785910358799563931659)
            ·
              refine ⟨10784678865538199345897489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7189785910358799563931659 10784678865538199345897489)
              ·
                refine ⟨8088509149153649509423117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10784678865538199345897489 8088509149153649509423117)
                ·
                  refine ⟨3033190930932618566033669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8088509149153649509423117 3033190930932618566033669)
                  ·
                    refine ⟨568723299549865981131313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3033190930932618566033669 568723299549865981131313)
                    ·
                      rfl

theorem cell23_3322754_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 2, 1, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 2, 1, 1, 1, 2, 3, 4].length) (baseStart_3322754 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3322754 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3322754 prefixEnd_3322754 := by exact prefixLift 3322754
  have htrace : WordTrace (prefixWord ++ tailWord_3322754) baseStart_3322754 baseEnd_3322754 := by
    simpa [prefixWord, tailWord_3322754, baseEnd_3322754] using wordTrace_append hprefix tailTrace_3322754
  have hstable : (prefixWord ++ tailWord_3322754).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3322754).length < 2 ^ (prefixWord ++ tailWord_3322754).sum := by decide
  have hdescent : baseEnd_3322754 < baseStart_3322754 := by decide
  rcases family_descends (prefixWord ++ tailWord_3322754) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3322756 : List Nat := [2, 3, 2, 1, 1, 1, 1, 1, 1, 3, 7]
def baseStart_3322756 : Nat := 118140960795 + 3322756 * 2 ^ 59
def prefixEnd_3322756 : Nat := 4983230072969 + 3 ^ 40 * 3322756 * 2
def baseEnd_3322756 : Nat := 1706170925610906935568929

theorem tailTrace_3322756 : CollatzResearch.WordTrace tailWord_3322756 prefixEnd_3322756 1706170925610906935568929 := by
  unfold tailWord_3322756
  simp only [CollatzResearch.WordTrace]
  refine ⟨60595433775114984195198061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80793911700153312260264081 60595433775114984195198061)
  ·
    refine ⟨22723287665668119073199273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 60595433775114984195198061 22723287665668119073199273)
    ·
      refine ⟨17042465749251089304899455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22723287665668119073199273 17042465749251089304899455)
      ·
        refine ⟨25563698623876633957349183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17042465749251089304899455 25563698623876633957349183)
        ·
          refine ⟨38345547935814950936023775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25563698623876633957349183 38345547935814950936023775)
          ·
            refine ⟨57518321903722426404035663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38345547935814950936023775 57518321903722426404035663)
            ·
              refine ⟨86277482855583639606053495, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 57518321903722426404035663 86277482855583639606053495)
              ·
                refine ⟨129416224283375459409080243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 86277482855583639606053495 129416224283375459409080243)
                ·
                  refine ⟨194124336425063189113620365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 129416224283375459409080243 194124336425063189113620365)
                  ·
                    refine ⟨72796626159398695917607637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 194124336425063189113620365 72796626159398695917607637)
                    ·
                      refine ⟨1706170925610906935568929, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 72796626159398695917607637 1706170925610906935568929)
                      ·
                        rfl

theorem cell23_3322756_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 1, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 1, 1, 1, 3, 7].length) (baseStart_3322756 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3322756 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3322756 prefixEnd_3322756 := by exact prefixLift 3322756
  have htrace : WordTrace (prefixWord ++ tailWord_3322756) baseStart_3322756 baseEnd_3322756 := by
    simpa [prefixWord, tailWord_3322756, baseEnd_3322756] using wordTrace_append hprefix tailTrace_3322756
  have hstable : (prefixWord ++ tailWord_3322756).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3322756).length < 2 ^ (prefixWord ++ tailWord_3322756).sum := by decide
  have hdescent : baseEnd_3322756 < baseStart_3322756 := by decide
  rcases family_descends (prefixWord ++ tailWord_3322756) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3322760 : List Nat := [2, 1, 3, 3, 2, 1, 1, 1, 5, 1, 3]
def baseStart_3322760 : Nat := 118140960795 + 3322760 * 2 ^ 59
def prefixEnd_3322760 : Nat := 4983230072969 + 3 ^ 40 * 3322760 * 2
def baseEnd_3322760 : Nat := 1706172979533524919918911

theorem tailTrace_3322760 : CollatzResearch.WordTrace tailWord_3322760 prefixEnd_3322760 1706172979533524919918911 := by
  unfold tailWord_3322760
  simp only [CollatzResearch.WordTrace]
  refine ⟨60595506721107738536770867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80794008961476984715694489 60595506721107738536770867)
  ·
    refine ⟨90893260081661607805156301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60595506721107738536770867 90893260081661607805156301)
    ·
      refine ⟨34084972530623102926933613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 90893260081661607805156301 34084972530623102926933613)
      ·
        refine ⟨12781864698983663597600105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 34084972530623102926933613 12781864698983663597600105)
        ·
          refine ⟨9586398524237747698200079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12781864698983663597600105 9586398524237747698200079)
          ·
            refine ⟨14379597786356621547300119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9586398524237747698200079 14379597786356621547300119)
            ·
              refine ⟨21569396679534932320950179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14379597786356621547300119 21569396679534932320950179)
              ·
                refine ⟨32354095019302398481425269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21569396679534932320950179 32354095019302398481425269)
                ·
                  refine ⟨3033196408059599857633619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 32354095019302398481425269 3033196408059599857633619)
                  ·
                    refine ⟨4549794612089399786450429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3033196408059599857633619 4549794612089399786450429)
                    ·
                      refine ⟨1706172979533524919918911, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4549794612089399786450429 1706172979533524919918911)
                      ·
                        rfl

theorem cell23_3322760_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 1, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 1, 1, 1, 5, 1, 3].length) (baseStart_3322760 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3322760 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3322760 prefixEnd_3322760 := by exact prefixLift 3322760
  have htrace : WordTrace (prefixWord ++ tailWord_3322760) baseStart_3322760 baseEnd_3322760 := by
    simpa [prefixWord, tailWord_3322760, baseEnd_3322760] using wordTrace_append hprefix tailTrace_3322760
  have hstable : (prefixWord ++ tailWord_3322760).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3322760).length < 2 ^ (prefixWord ++ tailWord_3322760).sum := by decide
  have hdescent : baseEnd_3322760 < baseStart_3322760 := by decide
  rcases family_descends (prefixWord ++ tailWord_3322760) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3322793 : List Nat := [1, 2, 1, 1, 1, 1, 7, 1, 4, 4]
def baseStart_3322793 : Nat := 118140960795 + 3322793 * 2 ^ 59
def prefixEnd_3322793 : Nat := 4983230072969 + 3 ^ 40 * 3322793 * 2
def baseEnd_3322793 : Nat := 568729974798374430268753

theorem tailTrace_3322793 : CollatzResearch.WordTrace tailWord_3322793 prefixEnd_3322793 568729974798374430268753 := by
  unfold tailWord_3322793
  simp only [CollatzResearch.WordTrace]
  refine ⟨121192217051095923709493033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80794811367397282472995355 121192217051095923709493033)
  ·
    refine ⟨90894162788321942782119775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 121192217051095923709493033 90894162788321942782119775)
    ·
      refine ⟨136341244182482914173179663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90894162788321942782119775 136341244182482914173179663)
      ·
        refine ⟨204511866273724371259769495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 136341244182482914173179663 204511866273724371259769495)
        ·
          refine ⟨306767799410586556889654243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 204511866273724371259769495 306767799410586556889654243)
          ·
            refine ⟨460151699115879835334481365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 306767799410586556889654243 460151699115879835334481365)
            ·
              refine ⟨10784805448028433640651907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 460151699115879835334481365 10784805448028433640651907)
              ·
                refine ⟨16177208172042650460977861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10784805448028433640651907 16177208172042650460977861)
                ·
                  refine ⟨3033226532257996961433349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 16177208172042650460977861 3033226532257996961433349)
                  ·
                    refine ⟨568729974798374430268753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3033226532257996961433349 568729974798374430268753)
                    ·
                      rfl

theorem cell23_3322793_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 7, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 7, 1, 4, 4].length) (baseStart_3322793 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3322793 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3322793 prefixEnd_3322793 := by exact prefixLift 3322793
  have htrace : WordTrace (prefixWord ++ tailWord_3322793) baseStart_3322793 baseEnd_3322793 := by
    simpa [prefixWord, tailWord_3322793, baseEnd_3322793] using wordTrace_append hprefix tailTrace_3322793
  have hstable : (prefixWord ++ tailWord_3322793).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3322793).length < 2 ^ (prefixWord ++ tailWord_3322793).sum := by decide
  have hdescent : baseEnd_3322793 < baseStart_3322793 := by decide
  rcases family_descends (prefixWord ++ tailWord_3322793) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3322796 : List Nat := [2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 6]
def baseStart_3322796 : Nat := 118140960795 + 3322796 * 2 ^ 59
def prefixEnd_3322796 : Nat := 4983230072969 + 3 ^ 40 * 3322796 * 2
def baseEnd_3322796 : Nat := 1706191464837086779068745

theorem tailTrace_3322796 : CollatzResearch.WordTrace tailWord_3322796 prefixEnd_3322796 1706191464837086779068745 := by
  unfold tailWord_3322796
  simp only [CollatzResearch.WordTrace]
  refine ⟨60596163235042527610926121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80794884313390036814568161 60596163235042527610926121)
  ·
    refine ⟨45447122426281895708194591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60596163235042527610926121 45447122426281895708194591)
    ·
      refine ⟨68170683639422843562291887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45447122426281895708194591 68170683639422843562291887)
      ·
        refine ⟨102256025459134265343437831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68170683639422843562291887 102256025459134265343437831)
        ·
          refine ⟨153384038188701398015156747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 102256025459134265343437831 153384038188701398015156747)
          ·
            refine ⟨230076057283052097022735121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 153384038188701398015156747 230076057283052097022735121)
            ·
              refine ⟨172557042962289072767051341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 230076057283052097022735121 172557042962289072767051341)
              ·
                refine ⟨64708891110858402287644253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 172557042962289072767051341 64708891110858402287644253)
                ·
                  refine ⟨24265834166571900857866595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 64708891110858402287644253 24265834166571900857866595)
                  ·
                    refine ⟨36398751249857851286799893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 24265834166571900857866595 36398751249857851286799893)
                    ·
                      refine ⟨1706191464837086779068745, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 36398751249857851286799893 1706191464837086779068745)
                      ·
                        rfl

theorem cell23_3322796_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 6].length) (baseStart_3322796 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3322796 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3322796 prefixEnd_3322796 := by exact prefixLift 3322796
  have htrace : WordTrace (prefixWord ++ tailWord_3322796) baseStart_3322796 baseEnd_3322796 := by
    simpa [prefixWord, tailWord_3322796, baseEnd_3322796] using wordTrace_append hprefix tailTrace_3322796
  have hstable : (prefixWord ++ tailWord_3322796).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3322796).length < 2 ^ (prefixWord ++ tailWord_3322796).sum := by decide
  have hdescent : baseEnd_3322796 < baseStart_3322796 := by decide
  rcases family_descends (prefixWord ++ tailWord_3322796) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3322803 : List Nat := [1, 1, 1, 2, 3, 1, 2, 4, 3, 2, 3]
def baseStart_3322803 : Nat := 118140960795 + 3322803 * 2 ^ 59
def prefixEnd_3322803 : Nat := 4983230072969 + 3 ^ 40 * 3322803 * 2
def baseEnd_3322803 : Nat := 1706195059201668251681213

theorem tailTrace_3322803 : CollatzResearch.WordTrace tailWord_3322803 prefixEnd_3322803 1706195059201668251681213 := by
  unfold tailWord_3322803
  simp only [CollatzResearch.WordTrace]
  refine ⟨121192581781059695417357063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80795054520706463611571375 121192581781059695417357063)
  ·
    refine ⟨181788872671589543126035595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121192581781059695417357063 181788872671589543126035595)
    ·
      refine ⟨272683309007384314689053393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 181788872671589543126035595 272683309007384314689053393)
      ·
        refine ⟨204512481755538236016790045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 272683309007384314689053393 204512481755538236016790045)
        ·
          refine ⟨76692180658326838506296267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 204512481755538236016790045 76692180658326838506296267)
          ·
            refine ⟨115038270987490257759444401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 76692180658326838506296267 115038270987490257759444401)
            ·
              refine ⟨86278703240617693319583301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 115038270987490257759444401 86278703240617693319583301)
              ·
                refine ⟨16177256857615817497421869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 86278703240617693319583301 16177256857615817497421869)
                ·
                  refine ⟨6066471321605931561533201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16177256857615817497421869 6066471321605931561533201)
                  ·
                    refine ⟨4549853491204448671149901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6066471321605931561533201 4549853491204448671149901)
                    ·
                      refine ⟨1706195059201668251681213, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4549853491204448671149901 1706195059201668251681213)
                      ·
                        rfl

theorem cell23_3322803_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 2, 4, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 2, 4, 3, 2, 3].length) (baseStart_3322803 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3322803 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3322803 prefixEnd_3322803 := by exact prefixLift 3322803
  have htrace : WordTrace (prefixWord ++ tailWord_3322803) baseStart_3322803 baseEnd_3322803 := by
    simpa [prefixWord, tailWord_3322803, baseEnd_3322803] using wordTrace_append hprefix tailTrace_3322803
  have hstable : (prefixWord ++ tailWord_3322803).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3322803).length < 2 ^ (prefixWord ++ tailWord_3322803).sum := by decide
  have hdescent : baseEnd_3322803 < baseStart_3322803 := by decide
  rcases family_descends (prefixWord ++ tailWord_3322803) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3322822 : List Nat := [6, 1, 3, 1, 2, 1, 1, 3, 1, 4]
def baseStart_3322822 : Nat := 118140960795 + 3322822 * 2 ^ 59
def prefixEnd_3322822 : Nat := 4983230072969 + 3 ^ 40 * 3322822 * 2
def baseEnd_3322822 : Nat := 568734938444701225781209

theorem tailTrace_3322822 : CollatzResearch.WordTrace tailWord_3322822 prefixEnd_3322822 568734938444701225781209 := by
  unfold tailWord_3322822
  simp only [CollatzResearch.WordTrace]
  refine ⟨3787289836499714426946835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 80795516511993907774865813 3787289836499714426946835)
  ·
    refine ⟨5680934754749571640420253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3787289836499714426946835 5680934754749571640420253)
    ·
      refine ⟨2130350533031089365157595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5680934754749571640420253 2130350533031089365157595)
      ·
        refine ⟨3195525799546634047736393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2130350533031089365157595 3195525799546634047736393)
        ·
          refine ⟨2396644349659975535802295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3195525799546634047736393 2396644349659975535802295)
          ·
            refine ⟨3594966524489963303703443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2396644349659975535802295 3594966524489963303703443)
            ·
              refine ⟨5392449786734944955555165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3594966524489963303703443 5392449786734944955555165)
              ·
                refine ⟨2022168670025604358333187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5392449786734944955555165 2022168670025604358333187)
                ·
                  refine ⟨3033253005038406537499781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2022168670025604358333187 3033253005038406537499781)
                  ·
                    refine ⟨568734938444701225781209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3033253005038406537499781 568734938444701225781209)
                    ·
                      rfl

theorem cell23_3322822_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 3, 1, 2, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 3, 1, 2, 1, 1, 3, 1, 4].length) (baseStart_3322822 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3322822 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3322822 prefixEnd_3322822 := by exact prefixLift 3322822
  have htrace : WordTrace (prefixWord ++ tailWord_3322822) baseStart_3322822 baseEnd_3322822 := by
    simpa [prefixWord, tailWord_3322822, baseEnd_3322822] using wordTrace_append hprefix tailTrace_3322822
  have hstable : (prefixWord ++ tailWord_3322822).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3322822).length < 2 ^ (prefixWord ++ tailWord_3322822).sum := by decide
  have hdescent : baseEnd_3322822 < baseStart_3322822 := by decide
  rcases family_descends (prefixWord ++ tailWord_3322822) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3322823 : List Nat := [1, 1, 4, 1, 1, 2, 6, 7]
def baseStart_3322823 : Nat := 118140960795 + 3322823 * 2 ^ 59
def prefixEnd_3322823 : Nat := 4983230072969 + 3 ^ 40 * 3322823 * 2
def baseEnd_3322823 : Nat := 63192789956102154571523

theorem tailTrace_3322823 : CollatzResearch.WordTrace tailWord_3322823 prefixEnd_3322823 63192789956102154571523 := by
  unfold tailWord_3322823
  simp only [CollatzResearch.WordTrace]
  refine ⟨121193311240987238833085123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80795540827324825888723415 121193311240987238833085123)
  ·
    refine ⟨181789966861480858249627685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121193311240987238833085123 181789966861480858249627685)
    ·
      refine ⟨34085618786527660921805191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 181789966861480858249627685 34085618786527660921805191)
      ·
        refine ⟨51128428179791491382707787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34085618786527660921805191 51128428179791491382707787)
        ·
          refine ⟨76692642269687237074061681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51128428179791491382707787 76692642269687237074061681)
          ·
            refine ⟨57519481702265427805546261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 76692642269687237074061681 57519481702265427805546261)
            ·
              refine ⟨2696225704793691928384981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 57519481702265427805546261 2696225704793691928384981)
              ·
                refine ⟨63192789956102154571523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2696225704793691928384981 63192789956102154571523)
                ·
                  rfl

theorem cell23_3322823_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 6, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 6, 7].length) (baseStart_3322823 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3322823 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3322823 prefixEnd_3322823 := by exact prefixLift 3322823
  have htrace : WordTrace (prefixWord ++ tailWord_3322823) baseStart_3322823 baseEnd_3322823 := by
    simpa [prefixWord, tailWord_3322823, baseEnd_3322823] using wordTrace_append hprefix tailTrace_3322823
  have hstable : (prefixWord ++ tailWord_3322823).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3322823).length < 2 ^ (prefixWord ++ tailWord_3322823).sum := by decide
  have hdescent : baseEnd_3322823 < baseStart_3322823 := by decide
  rcases family_descends (prefixWord ++ tailWord_3322823) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3322833 : List Nat := [1, 2, 2, 1, 2, 1, 4, 1, 3, 3, 3]
def baseStart_3322833 : Nat := 118140960795 + 3322833 * 2 ^ 59
def prefixEnd_3322833 : Nat := 4983230072969 + 3 ^ 40 * 3322833 * 2
def baseEnd_3322833 : Nat := 1706210463621303134306075

theorem tailTrace_3322833 : CollatzResearch.WordTrace tailWord_3322833 prefixEnd_3322833 1706210463621303134306075 := by
  unfold tailWord_3322833
  simp only [CollatzResearch.WordTrace]
  refine ⟨121193675970951010540949153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80795783980634007027299435 121193675970951010540949153)
  ·
    refine ⟨90895256978213257905711865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 121193675970951010540949153 90895256978213257905711865)
    ·
      refine ⟨68171442733659943429283899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 90895256978213257905711865 68171442733659943429283899)
      ·
        refine ⟨102257164100489915143925849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68171442733659943429283899 102257164100489915143925849)
        ·
          refine ⟨76692873075367436357944387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 102257164100489915143925849 76692873075367436357944387)
          ·
            refine ⟨115039309613051154536916581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 76692873075367436357944387 115039309613051154536916581)
            ·
              refine ⟨21569870552447091475671859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 115039309613051154536916581 21569870552447091475671859)
              ·
                refine ⟨32354805828670637213507789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21569870552447091475671859 32354805828670637213507789)
                ·
                  refine ⟨12133052185751488955065421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 32354805828670637213507789 12133052185751488955065421)
                  ·
                    refine ⟨4549894569656808358149533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12133052185751488955065421 4549894569656808358149533)
                    ·
                      refine ⟨1706210463621303134306075, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4549894569656808358149533 1706210463621303134306075)
                      ·
                        rfl

theorem cell23_3322833_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 4, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 4, 1, 3, 3, 3].length) (baseStart_3322833 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3322833 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3322833 prefixEnd_3322833 := by exact prefixLift 3322833
  have htrace : WordTrace (prefixWord ++ tailWord_3322833) baseStart_3322833 baseEnd_3322833 := by
    simpa [prefixWord, tailWord_3322833, baseEnd_3322833] using wordTrace_append hprefix tailTrace_3322833
  have hstable : (prefixWord ++ tailWord_3322833).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3322833).length < 2 ^ (prefixWord ++ tailWord_3322833).sum := by decide
  have hdescent : baseEnd_3322833 < baseStart_3322833 := by decide
  rcases family_descends (prefixWord ++ tailWord_3322833) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3322851 : List Nat := [1, 1, 1, 6, 1, 1, 5, 2, 1, 2, 2]
def baseStart_3322851 : Nat := 118140960795 + 3322851 * 2 ^ 59
def prefixEnd_3322851 : Nat := 4983230072969 + 3 ^ 40 * 3322851 * 2
def baseEnd_3322851 : Nat := 1706219706273084063880993

theorem tailTrace_3322851 : CollatzResearch.WordTrace tailWord_3322851 prefixEnd_3322851 1706219706273084063880993 := by
  unfold tailWord_3322851
  simp only [CollatzResearch.WordTrace]
  refine ⟨121194332484885799615104407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80796221656590533076736271 121194332484885799615104407)
  ·
    refine ⟨181791498727328699422656611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121194332484885799615104407 181791498727328699422656611)
    ·
      refine ⟨272687248090993049133984917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 181791498727328699422656611 272687248090993049133984917)
      ·
        refine ⟨12782214754265299178155543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 272687248090993049133984917 12782214754265299178155543)
        ·
          refine ⟨19173322131397948767233315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12782214754265299178155543 19173322131397948767233315)
          ·
            refine ⟨28759983197096923150849973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19173322131397948767233315 28759983197096923150849973)
            ·
              refine ⟨2696248424727836545392185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 28759983197096923150849973 2696248424727836545392185)
              ·
                refine ⟨2022186318545877409044139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2696248424727836545392185 2022186318545877409044139)
                ·
                  refine ⟨3033279477818816113566209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2022186318545877409044139 3033279477818816113566209)
                  ·
                    refine ⟨2274959608364112085174657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3033279477818816113566209 2274959608364112085174657)
                    ·
                      refine ⟨1706219706273084063880993, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2274959608364112085174657 1706219706273084063880993)
                      ·
                        rfl

theorem cell23_3322851_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 5, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 5, 2, 1, 2, 2].length) (baseStart_3322851 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3322851 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3322851 prefixEnd_3322851 := by exact prefixLift 3322851
  have htrace : WordTrace (prefixWord ++ tailWord_3322851) baseStart_3322851 baseEnd_3322851 := by
    simpa [prefixWord, tailWord_3322851, baseEnd_3322851] using wordTrace_append hprefix tailTrace_3322851
  have hstable : (prefixWord ++ tailWord_3322851).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3322851).length < 2 ^ (prefixWord ++ tailWord_3322851).sum := by decide
  have hdescent : baseEnd_3322851 < baseStart_3322851 := by decide
  rcases family_descends (prefixWord ++ tailWord_3322851) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3322953 : List Nat := [1, 2, 1, 1, 2, 2, 2, 4, 1, 2, 5]
def baseStart_3322953 : Nat := 118140960795 + 3322953 * 2 ^ 59
def prefixEnd_3322953 : Nat := 4983230072969 + 3 ^ 40 * 3322953 * 2
def baseEnd_3322953 : Nat := 1706272081299842664805523

theorem tailTrace_3322953 : CollatzResearch.WordTrace tailWord_3322953 prefixEnd_3322953 1706272081299842664805523 := by
  unfold tailWord_3322953
  simp only [CollatzResearch.WordTrace]
  refine ⟨121198052730516271035317513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80798701820344180690211675 121198052730516271035317513)
  ·
    refine ⟨90898539547887203276488135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 121198052730516271035317513 90898539547887203276488135)
    ·
      refine ⟨136347809321830804914732203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90898539547887203276488135 136347809321830804914732203)
      ·
        refine ⟨204521713982746207372098305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 136347809321830804914732203 204521713982746207372098305)
        ·
          refine ⟨153391285487059655529073729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 204521713982746207372098305 153391285487059655529073729)
          ·
            refine ⟨115043464115294741646805297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 153391285487059655529073729 115043464115294741646805297)
            ·
              refine ⟨86282598086471056235103973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 115043464115294741646805297 86282598086471056235103973)
              ·
                refine ⟨16177987141213323044081995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 86282598086471056235103973 16177987141213323044081995)
                ·
                  refine ⟨24266980711819984566122993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16177987141213323044081995 24266980711819984566122993)
                  ·
                    refine ⟨18200235533864988424592245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 24266980711819984566122993 18200235533864988424592245)
                    ·
                      refine ⟨1706272081299842664805523, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 18200235533864988424592245 1706272081299842664805523)
                      ·
                        rfl

theorem cell23_3322953_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 2, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 2, 4, 1, 2, 5].length) (baseStart_3322953 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3322953 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3322953 prefixEnd_3322953 := by exact prefixLift 3322953
  have htrace : WordTrace (prefixWord ++ tailWord_3322953) baseStart_3322953 baseEnd_3322953 := by
    simpa [prefixWord, tailWord_3322953, baseEnd_3322953] using wordTrace_append hprefix tailTrace_3322953
  have hstable : (prefixWord ++ tailWord_3322953).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3322953).length < 2 ^ (prefixWord ++ tailWord_3322953).sum := by decide
  have hdescent : baseEnd_3322953 < baseStart_3322953 := by decide
  rcases family_descends (prefixWord ++ tailWord_3322953) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3322957 : List Nat := [1, 6, 1, 1, 1, 2, 1, 2, 2, 3, 3]
def baseStart_3322957 : Nat := 118140960795 + 3322957 * 2 ^ 59
def prefixEnd_3322957 : Nat := 4983230072969 + 3 ^ 40 * 3322957 * 2
def baseEnd_3322957 : Nat := 1706274135222460649155505

theorem tailTrace_3322957 : CollatzResearch.WordTrace tailWord_3322957 prefixEnd_3322957 1706274135222460649155505 := by
  unfold tailWord_3322957
  simp only [CollatzResearch.WordTrace]
  refine ⟨121198198622501779718463125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80798799081667853145642083 121198198622501779718463125)
  ·
    refine ⟨5681165560429770924302959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 121198198622501779718463125 5681165560429770924302959)
    ·
      refine ⟨8521748340644656386454439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5681165560429770924302959 8521748340644656386454439)
      ·
        refine ⟨12782622510966984579681659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8521748340644656386454439 12782622510966984579681659)
        ·
          refine ⟨19173933766450476869522489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12782622510966984579681659 19173933766450476869522489)
          ·
            refine ⟨14380450324837857652141867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19173933766450476869522489 14380450324837857652141867)
            ·
              refine ⟨21570675487256786478212801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14380450324837857652141867 21570675487256786478212801)
              ·
                refine ⟨16178006615442589858659601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21570675487256786478212801 16178006615442589858659601)
                ·
                  refine ⟨12133504961581942393994701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16178006615442589858659601 12133504961581942393994701)
                  ·
                    refine ⟨4550064360593228397748013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12133504961581942393994701 4550064360593228397748013)
                    ·
                      refine ⟨1706274135222460649155505, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4550064360593228397748013 1706274135222460649155505)
                      ·
                        rfl

theorem cell23_3322957_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 2, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 2, 1, 2, 2, 3, 3].length) (baseStart_3322957 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3322957 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3322957 prefixEnd_3322957 := by exact prefixLift 3322957
  have htrace : WordTrace (prefixWord ++ tailWord_3322957) baseStart_3322957 baseEnd_3322957 := by
    simpa [prefixWord, tailWord_3322957, baseEnd_3322957] using wordTrace_append hprefix tailTrace_3322957
  have hstable : (prefixWord ++ tailWord_3322957).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3322957).length < 2 ^ (prefixWord ++ tailWord_3322957).sum := by decide
  have hdescent : baseEnd_3322957 < baseStart_3322957 := by decide
  rcases family_descends (prefixWord ++ tailWord_3322957) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3322963 : List Nat := [1, 1, 1, 2, 1, 1, 2, 4, 3, 3, 4]
def baseStart_3322963 : Nat := 118140960795 + 3322963 * 2 ^ 59
def prefixEnd_3322963 : Nat := 4983230072969 + 3 ^ 40 * 3322963 * 2
def baseEnd_3322963 : Nat := 1706277216106387625680477

theorem tailTrace_3322963 : CollatzResearch.WordTrace tailWord_3322963 prefixEnd_3322963 1706277216106387625680477 := by
  unfold tailWord_3322963
  simp only [CollatzResearch.WordTrace]
  refine ⟨121198417460480042743181543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80798944973653361828787695 121198417460480042743181543)
  ·
    refine ⟨181797626190720064114772315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121198417460480042743181543 181797626190720064114772315)
    ·
      refine ⟨272696439286080096172158473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 181797626190720064114772315 272696439286080096172158473)
      ·
        refine ⟨204522329464560072129118855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 272696439286080096172158473 204522329464560072129118855)
        ·
          refine ⟨306783494196840108193678283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 204522329464560072129118855 306783494196840108193678283)
          ·
            refine ⟨460175241295260162290517425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 306783494196840108193678283 460175241295260162290517425)
            ·
              refine ⟨345131430971445121717888069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 460175241295260162290517425 345131430971445121717888069)
              ·
                refine ⟨64712143307145960322104013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 345131430971445121717888069 64712143307145960322104013)
                ·
                  refine ⟨24267053740179735120789005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 64712143307145960322104013 24267053740179735120789005)
                  ·
                    refine ⟨9100145152567400670295877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 24267053740179735120789005 9100145152567400670295877)
                    ·
                      refine ⟨1706277216106387625680477, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9100145152567400670295877 1706277216106387625680477)
                      ·
                        rfl

theorem cell23_3322963_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 4, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 4, 3, 3, 4].length) (baseStart_3322963 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3322963 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3322963 prefixEnd_3322963 := by exact prefixLift 3322963
  have htrace : WordTrace (prefixWord ++ tailWord_3322963) baseStart_3322963 baseEnd_3322963 := by
    simpa [prefixWord, tailWord_3322963, baseEnd_3322963] using wordTrace_append hprefix tailTrace_3322963
  have hstable : (prefixWord ++ tailWord_3322963).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3322963).length < 2 ^ (prefixWord ++ tailWord_3322963).sum := by decide
  have hdescent : baseEnd_3322963 < baseStart_3322963 := by decide
  rcases family_descends (prefixWord ++ tailWord_3322963) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3322993 : List Nat := [1, 2, 2, 2, 1, 1, 2, 2, 1, 3, 6]
def baseStart_3322993 : Nat := 118140960795 + 3322993 * 2 ^ 59
def prefixEnd_3322993 : Nat := 4983230072969 + 3 ^ 40 * 3322993 * 2
def baseEnd_3322993 : Nat := 1706292620526022508305339

theorem tailTrace_3322993 : CollatzResearch.WordTrace tailWord_3322993 prefixEnd_3322993 1706292620526022508305339 := by
  unfold tailWord_3322993
  simp only [CollatzResearch.WordTrace]
  refine ⟨121199511650371357866773633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80799674433580905244515755 121199511650371357866773633)
  ·
    refine ⟨90899633737778518400080225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 121199511650371357866773633 90899633737778518400080225)
    ·
      refine ⟨68174725303333888800060169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 90899633737778518400080225 68174725303333888800060169)
      ·
        refine ⟨51131043977500416600045127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 68174725303333888800060169 51131043977500416600045127)
        ·
          refine ⟨76696565966250624900067691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51131043977500416600045127 76696565966250624900067691)
          ·
            refine ⟨115044848949375937350101537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 76696565966250624900067691 115044848949375937350101537)
            ·
              refine ⟨86283636712031953012576153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 115044848949375937350101537 86283636712031953012576153)
              ·
                refine ⟨64712727534023964759432115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 86283636712031953012576153 64712727534023964759432115)
                ·
                  refine ⟨97069091301035947139148173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 64712727534023964759432115 97069091301035947139148173)
                  ·
                    refine ⟨36400909237888480177180565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 97069091301035947139148173 36400909237888480177180565)
                    ·
                      refine ⟨1706292620526022508305339, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 36400909237888480177180565 1706292620526022508305339)
                      ·
                        rfl

theorem cell23_3322993_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 2, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 2, 2, 1, 3, 6].length) (baseStart_3322993 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3322993 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3322993 prefixEnd_3322993 := by exact prefixLift 3322993
  have htrace : WordTrace (prefixWord ++ tailWord_3322993) baseStart_3322993 baseEnd_3322993 := by
    simpa [prefixWord, tailWord_3322993, baseEnd_3322993] using wordTrace_append hprefix tailTrace_3322993
  have hstable : (prefixWord ++ tailWord_3322993).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3322993).length < 2 ^ (prefixWord ++ tailWord_3322993).sum := by decide
  have hdescent : baseEnd_3322993 < baseStart_3322993 := by decide
  rcases family_descends (prefixWord ++ tailWord_3322993) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3323000 : List Nat := [2, 1, 2, 1, 1, 1, 6, 1, 1, 4, 3]
def baseStart_3323000 : Nat := 118140960795 + 3323000 * 2 ^ 59
def prefixEnd_3323000 : Nat := 4983230072969 + 3 ^ 40 * 3323000 * 2
def baseEnd_3323000 : Nat := 1706296214890603980917807

theorem tailTrace_3323000 : CollatzResearch.WordTrace tailWord_3323000 prefixEnd_3323000 1706296214890603980917807 := by
  unfold tailWord_3323000
  simp only [CollatzResearch.WordTrace]
  refine ⟨60599883480672999031139227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80799844640897332041518969 60599883480672999031139227)
  ·
    refine ⟨90899825221009498546708841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60599883480672999031139227 90899825221009498546708841)
    ·
      refine ⟨68174868915757123910031631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 90899825221009498546708841 68174868915757123910031631)
      ·
        refine ⟨102262303373635685865047447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68174868915757123910031631 102262303373635685865047447)
        ·
          refine ⟨153393455060453528797571171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 102262303373635685865047447 153393455060453528797571171)
          ·
            refine ⟨230090182590680293196356757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 153393455060453528797571171 230090182590680293196356757)
            ·
              refine ⟨10785477308938138743579223, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 230090182590680293196356757 10785477308938138743579223)
              ·
                refine ⟨16178215963407208115368835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10785477308938138743579223 16178215963407208115368835)
                ·
                  refine ⟨24267323945110812173053253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16178215963407208115368835 24267323945110812173053253)
                  ·
                    refine ⟨4550123239708277282447485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 24267323945110812173053253 4550123239708277282447485)
                    ·
                      refine ⟨1706296214890603980917807, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4550123239708277282447485 1706296214890603980917807)
                      ·
                        rfl

theorem cell23_3323000_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 6, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 6, 1, 1, 4, 3].length) (baseStart_3323000 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3323000 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3323000 prefixEnd_3323000 := by exact prefixLift 3323000
  have htrace : WordTrace (prefixWord ++ tailWord_3323000) baseStart_3323000 baseEnd_3323000 := by
    simpa [prefixWord, tailWord_3323000, baseEnd_3323000] using wordTrace_append hprefix tailTrace_3323000
  have hstable : (prefixWord ++ tailWord_3323000).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3323000).length < 2 ^ (prefixWord ++ tailWord_3323000).sum := by decide
  have hdescent : baseEnd_3323000 < baseStart_3323000 := by decide
  rcases family_descends (prefixWord ++ tailWord_3323000) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3323017 : List Nat := [1, 2, 1, 1, 4, 4, 1, 2, 2, 2, 3]
def baseStart_3323017 : Nat := 118140960795 + 3323017 * 2 ^ 59
def prefixEnd_3323017 : Nat := 4983230072969 + 3 ^ 40 * 3323017 * 2
def baseEnd_3323017 : Nat := 1706304944061730414405229

theorem tailTrace_3323017 : CollatzResearch.WordTrace tailWord_3323017 prefixEnd_3323017 1706304944061730414405229 := by
  unfold tailWord_3323017
  simp only [CollatzResearch.WordTrace]
  refine ⟨121200387002284409965647305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80800258001522939977098203 121200387002284409965647305)
  ·
    refine ⟨90900290251713307474235479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 121200387002284409965647305 90900290251713307474235479)
    ·
      refine ⟨136350435377569961211353219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90900290251713307474235479 136350435377569961211353219)
      ·
        refine ⟨204525653066354941817029829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 136350435377569961211353219 204525653066354941817029829)
        ·
          refine ⟨38348559949941551590693093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 204525653066354941817029829 38348559949941551590693093)
          ·
            refine ⟨7190354990614040923254955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 38348559949941551590693093 7190354990614040923254955)
            ·
              refine ⟨10785532485921061384882433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7190354990614040923254955 10785532485921061384882433)
              ·
                refine ⟨8089149364440796038661825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10785532485921061384882433 8089149364440796038661825)
                ·
                  refine ⟨6066862023330597028996369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8089149364440796038661825 6066862023330597028996369)
                  ·
                    refine ⟨4550146517497947771747277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6066862023330597028996369 4550146517497947771747277)
                    ·
                      refine ⟨1706304944061730414405229, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4550146517497947771747277 1706304944061730414405229)
                      ·
                        rfl

theorem cell23_3323017_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 4, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 4, 1, 2, 2, 2, 3].length) (baseStart_3323017 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3323017 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3323017 prefixEnd_3323017 := by exact prefixLift 3323017
  have htrace : WordTrace (prefixWord ++ tailWord_3323017) baseStart_3323017 baseEnd_3323017 := by
    simpa [prefixWord, tailWord_3323017, baseEnd_3323017] using wordTrace_append hprefix tailTrace_3323017
  have hstable : (prefixWord ++ tailWord_3323017).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3323017).length < 2 ^ (prefixWord ++ tailWord_3323017).sum := by decide
  have hdescent : baseEnd_3323017 < baseStart_3323017 := by decide
  rcases family_descends (prefixWord ++ tailWord_3323017) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3323023 : List Nat := [1, 1, 2, 1, 1, 1, 1, 2, 5, 2, 6]
def baseStart_3323023 : Nat := 118140960795 + 3323023 * 2 ^ 59
def prefixEnd_3323023 : Nat := 4983230072969 + 3 ^ 40 * 3323023 * 2
def baseEnd_3323023 : Nat := 1706308024945657390930201

theorem tailTrace_3323023 : CollatzResearch.WordTrace tailWord_3323023 prefixEnd_3323023 1706308024945657390930201 := by
  unfold tailWord_3323023
  simp only [CollatzResearch.WordTrace]
  refine ⟨121200605840262672990365723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80800403893508448660243815 121200605840262672990365723)
  ·
    refine ⟨181800908760394009485548585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121200605840262672990365723 181800908760394009485548585)
    ·
      refine ⟨136350681570295507114161439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 181800908760394009485548585 136350681570295507114161439)
      ·
        refine ⟨204526022355443260671242159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 136350681570295507114161439 204526022355443260671242159)
        ·
          refine ⟨306789033533164891006863239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 204526022355443260671242159 306789033533164891006863239)
          ·
            refine ⟨460183550299747336510294859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 306789033533164891006863239 460183550299747336510294859)
            ·
              refine ⟨690275325449621004765442289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 460183550299747336510294859 690275325449621004765442289)
              ·
                refine ⟨517706494087215753574081717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 690275325449621004765442289 517706494087215753574081717)
                ·
                  refine ⟨48534983820676476897570161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 517706494087215753574081717 48534983820676476897570161)
                  ·
                    refine ⟨36401237865507357673177621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 48534983820676476897570161 36401237865507357673177621)
                    ·
                      refine ⟨1706308024945657390930201, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 36401237865507357673177621 1706308024945657390930201)
                      ·
                        rfl

theorem cell23_3323023_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 2, 5, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 2, 5, 2, 6].length) (baseStart_3323023 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3323023 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3323023 prefixEnd_3323023 := by exact prefixLift 3323023
  have htrace : WordTrace (prefixWord ++ tailWord_3323023) baseStart_3323023 baseEnd_3323023 := by
    simpa [prefixWord, tailWord_3323023, baseEnd_3323023] using wordTrace_append hprefix tailTrace_3323023
  have hstable : (prefixWord ++ tailWord_3323023).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3323023).length < 2 ^ (prefixWord ++ tailWord_3323023).sum := by decide
  have hdescent : baseEnd_3323023 < baseStart_3323023 := by decide
  rcases family_descends (prefixWord ++ tailWord_3323023) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3323033 : List Nat := [1, 2, 1, 2, 1, 2, 1, 1, 1, 11]
def baseStart_3323033 : Nat := 118140960795 + 3323033 * 2 ^ 59
def prefixEnd_3323033 : Nat := 4983230072969 + 3 ^ 40 * 3323033 * 2
def baseEnd_3323033 : Nat := 568771053250734117268385

theorem tailTrace_3323033 : CollatzResearch.WordTrace tailWord_3323033 prefixEnd_3323033 568771053250734117268385 := by
  unfold tailWord_3323033
  simp only [CollatzResearch.WordTrace]
  refine ⟨121200970570226444698229753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80800647046817629798819835 121200970570226444698229753)
  ·
    refine ⟨90900727927669833523672315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 121200970570226444698229753 90900727927669833523672315)
    ·
      refine ⟨136351091891504750285508473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90900727927669833523672315 136351091891504750285508473)
      ·
        refine ⟨102263318918628562714131355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 136351091891504750285508473 102263318918628562714131355)
        ·
          refine ⟨153394978377942844071197033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 102263318918628562714131355 153394978377942844071197033)
          ·
            refine ⟨115046233783457133053397775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 153394978377942844071197033 115046233783457133053397775)
            ·
              refine ⟨172569350675185699580096663, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 115046233783457133053397775 172569350675185699580096663)
              ·
                refine ⟨258854026012778549370144995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 172569350675185699580096663 258854026012778549370144995)
                ·
                  refine ⟨388281039019167824055217493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 258854026012778549370144995 388281039019167824055217493)
                  ·
                    refine ⟨568771053250734117268385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 11 388281039019167824055217493 568771053250734117268385)
                    ·
                      rfl

theorem cell23_3323033_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 1, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 1, 1, 1, 11].length) (baseStart_3323033 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3323033 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3323033 prefixEnd_3323033 := by exact prefixLift 3323033
  have htrace : WordTrace (prefixWord ++ tailWord_3323033) baseStart_3323033 baseEnd_3323033 := by
    simpa [prefixWord, tailWord_3323033, baseEnd_3323033] using wordTrace_append hprefix tailTrace_3323033
  have hstable : (prefixWord ++ tailWord_3323033).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3323033).length < 2 ^ (prefixWord ++ tailWord_3323033).sum := by decide
  have hdescent : baseEnd_3323033 < baseStart_3323033 := by decide
  rcases family_descends (prefixWord ++ tailWord_3323033) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3323104 : List Nat := [2, 1, 1, 3, 1, 4, 1, 1, 5, 2, 2]
def baseStart_3323104 : Nat := 118140960795 + 3323104 * 2 ^ 59
def prefixEnd_3323104 : Nat := 4983230072969 + 3 ^ 40 * 3323104 * 2
def baseEnd_3323104 : Nat := 1706349616878671574017329

theorem tailTrace_3323104 : CollatzResearch.WordTrace tailWord_3323104 prefixEnd_3323104 1706349616878671574017329 := by
  unfold tailWord_3323104
  simp only [CollatzResearch.WordTrace]
  refine ⟨60601780076484611912032183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80802373435312815882709577 60601780076484611912032183)
  ·
    refine ⟨90902670114726917868048275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60601780076484611912032183 90902670114726917868048275)
    ·
      refine ⟨136354005172090376802072413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90902670114726917868048275 136354005172090376802072413)
      ·
        refine ⟨51132751939533891300777155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 136354005172090376802072413 51132751939533891300777155)
        ·
          refine ⟨76699127909300836951165733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51132751939533891300777155 76699127909300836951165733)
          ·
            refine ⟨14381086482993906928343575, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 76699127909300836951165733 14381086482993906928343575)
            ·
              refine ⟨21571629724490860392515363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14381086482993906928343575 21571629724490860392515363)
              ·
                refine ⟨32357444586736290588773045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21571629724490860392515363 32357444586736290588773045)
                ·
                  refine ⟨3033510430006527242697473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 32357444586736290588773045 3033510430006527242697473)
                  ·
                    refine ⟨2275132822504895432023105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3033510430006527242697473 2275132822504895432023105)
                    ·
                      refine ⟨1706349616878671574017329, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2275132822504895432023105 1706349616878671574017329)
                      ·
                        rfl

theorem cell23_3323104_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 4, 1, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 4, 1, 1, 5, 2, 2].length) (baseStart_3323104 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3323104 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3323104 prefixEnd_3323104 := by exact prefixLift 3323104
  have htrace : WordTrace (prefixWord ++ tailWord_3323104) baseStart_3323104 baseEnd_3323104 := by
    simpa [prefixWord, tailWord_3323104, baseEnd_3323104] using wordTrace_append hprefix tailTrace_3323104
  have hstable : (prefixWord ++ tailWord_3323104).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3323104).length < 2 ^ (prefixWord ++ tailWord_3323104).sum := by decide
  have hdescent : baseEnd_3323104 < baseStart_3323104 := by decide
  rcases family_descends (prefixWord ++ tailWord_3323104) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3323164 : List Nat := [2, 2, 3, 1, 1, 1, 2, 3, 3, 3, 2]
def baseStart_3323164 : Nat := 118140960795 + 3323164 * 2 ^ 59
def prefixEnd_3323164 : Nat := 4983230072969 + 3 ^ 40 * 3323164 * 2
def baseEnd_3323164 : Nat := 1706380425717941339267053

theorem tailTrace_3323164 : CollatzResearch.WordTrace tailWord_3323164 prefixEnd_3323164 1706380425717941339267053 := by
  unfold tailWord_3323164
  simp only [CollatzResearch.WordTrace]
  refine ⟨60602874266375927035624273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80803832355167902714165697 60602874266375927035624273)
  ·
    refine ⟨45452155699781945276718205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60602874266375927035624273 45452155699781945276718205)
    ·
      refine ⟨17044558387418229478769327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 45452155699781945276718205 17044558387418229478769327)
      ·
        refine ⟨25566837581127344218153991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17044558387418229478769327 25566837581127344218153991)
        ·
          refine ⟨38350256371691016327230987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25566837581127344218153991 38350256371691016327230987)
          ·
            refine ⟨57525384557536524490846481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38350256371691016327230987 57525384557536524490846481)
            ·
              refine ⟨43144038418152393368134861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 57525384557536524490846481 43144038418152393368134861)
              ·
                refine ⟨16179014406807147513050573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 43144038418152393368134861 16179014406807147513050573)
                ·
                  refine ⟨6067130402552680317393965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16179014406807147513050573 6067130402552680317393965)
                  ·
                    refine ⟨2275173900957255119022737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6067130402552680317393965 2275173900957255119022737)
                    ·
                      refine ⟨1706380425717941339267053, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2275173900957255119022737 1706380425717941339267053)
                      ·
                        rfl

theorem cell23_3323164_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 2, 3, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 2, 3, 3, 3, 2].length) (baseStart_3323164 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3323164 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3323164 prefixEnd_3323164 := by exact prefixLift 3323164
  have htrace : WordTrace (prefixWord ++ tailWord_3323164) baseStart_3323164 baseEnd_3323164 := by
    simpa [prefixWord, tailWord_3323164, baseEnd_3323164] using wordTrace_append hprefix tailTrace_3323164
  have hstable : (prefixWord ++ tailWord_3323164).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3323164).length < 2 ^ (prefixWord ++ tailWord_3323164).sum := by decide
  have hdescent : baseEnd_3323164 < baseStart_3323164 := by decide
  rcases family_descends (prefixWord ++ tailWord_3323164) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3323247 : List Nat := [1, 1, 2, 1, 3, 1, 3, 4, 2, 5]
def baseStart_3323247 : Nat := 118140960795 + 3323247 * 2 ^ 59
def prefixEnd_3323247 : Nat := 4983230072969 + 3 ^ 40 * 3323247 * 2
def baseEnd_3323247 : Nat := 568807681537421504843057

theorem tailTrace_3323247 : CollatzResearch.WordTrace tailWord_3323247 prefixEnd_3323247 568807681537421504843057 := by
  unfold tailWord_3323247
  simp only [CollatzResearch.WordTrace]
  refine ⟨121208775791451159246519995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80805850527634106164346663 121208775791451159246519995)
  ·
    refine ⟨181813163687176738869779993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121208775791451159246519995 181813163687176738869779993)
    ·
      refine ⟨136359872765382554152334995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 181813163687176738869779993 136359872765382554152334995)
      ·
        refine ⟨204539809148073831228502493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 136359872765382554152334995 204539809148073831228502493)
        ·
          refine ⟨76702428430527686710688435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 204539809148073831228502493 76702428430527686710688435)
          ·
            refine ⟨115053642645791530066032653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 76702428430527686710688435 115053642645791530066032653)
            ·
              refine ⟨43145115992171823774762245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 115053642645791530066032653 43145115992171823774762245)
              ·
                refine ⟨8089709248532216957767921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 43145115992171823774762245 8089709248532216957767921)
                ·
                  refine ⟨6067281936399162718325941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8089709248532216957767921 6067281936399162718325941)
                  ·
                    refine ⟨568807681537421504843057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6067281936399162718325941 568807681537421504843057)
                    ·
                      rfl

theorem cell23_3323247_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 3, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 3, 4, 2, 5].length) (baseStart_3323247 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3323247 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3323247 prefixEnd_3323247 := by exact prefixLift 3323247
  have htrace : WordTrace (prefixWord ++ tailWord_3323247) baseStart_3323247 baseEnd_3323247 := by
    simpa [prefixWord, tailWord_3323247, baseEnd_3323247] using wordTrace_append hprefix tailTrace_3323247
  have hstable : (prefixWord ++ tailWord_3323247).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3323247).length < 2 ^ (prefixWord ++ tailWord_3323247).sum := by decide
  have hdescent : baseEnd_3323247 < baseStart_3323247 := by decide
  rcases family_descends (prefixWord ++ tailWord_3323247) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3323257 : List Nat := [1, 2, 1, 3, 2, 1, 4, 1, 1, 2, 5]
def baseStart_3323257 : Nat := 118140960795 + 3323257 * 2 ^ 59
def prefixEnd_3323257 : Nat := 4983230072969 + 3 ^ 40 * 3323257 * 2
def baseEnd_3323257 : Nat := 1706428179418809475404125

theorem tailTrace_3323257 : CollatzResearch.WordTrace tailWord_3323257 prefixEnd_3323257 1706428179418809475404125 := by
  unfold tailWord_3323257
  simp only [CollatzResearch.WordTrace]
  refine ⟨121209140521414930954384025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80806093680943287302922683 121209140521414930954384025)
  ·
    refine ⟨90906855391061198215788019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 121209140521414930954384025 90906855391061198215788019)
    ·
      refine ⟨136360283086591797323682029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90906855391061198215788019 136360283086591797323682029)
      ·
        refine ⟨51135106157471923996380761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 136360283086591797323682029 51135106157471923996380761)
        ·
          refine ⟨38351329618103942997285571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51135106157471923996380761 38351329618103942997285571)
          ·
            refine ⟨57526994427155914495928357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38351329618103942997285571 57526994427155914495928357)
            ·
              refine ⟨10786311455091733967986567, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 57526994427155914495928357 10786311455091733967986567)
              ·
                refine ⟨16179467182637600951979851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10786311455091733967986567 16179467182637600951979851)
                ·
                  refine ⟨24269200773956401427969777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16179467182637600951979851 24269200773956401427969777)
                  ·
                    refine ⟨18201900580467301070977333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 24269200773956401427969777 18201900580467301070977333)
                    ·
                      refine ⟨1706428179418809475404125, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 18201900580467301070977333 1706428179418809475404125)
                      ·
                        rfl

theorem cell23_3323257_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 4, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 4, 1, 1, 2, 5].length) (baseStart_3323257 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3323257 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3323257 prefixEnd_3323257 := by exact prefixLift 3323257
  have htrace : WordTrace (prefixWord ++ tailWord_3323257) baseStart_3323257 baseEnd_3323257 := by
    simpa [prefixWord, tailWord_3323257, baseEnd_3323257] using wordTrace_append hprefix tailTrace_3323257
  have hstable : (prefixWord ++ tailWord_3323257).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3323257).length < 2 ^ (prefixWord ++ tailWord_3323257).sum := by decide
  have hdescent : baseEnd_3323257 < baseStart_3323257 := by decide
  rcases family_descends (prefixWord ++ tailWord_3323257) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3323361 : List Nat := [1, 2, 3, 1, 2, 3, 1, 1, 4, 3, 2]
def baseStart_3323361 : Nat := 118140960795 + 3323361 * 2 ^ 59
def prefixEnd_3323361 : Nat := 4983230072969 + 3 ^ 40 * 3323361 * 2
def baseEnd_3323361 : Nat := 1706481581406877068503647

theorem tailTrace_3323361 : CollatzResearch.WordTrace tailWord_3323361 prefixEnd_3323361 1706481581406877068503647 := by
  unfold tailWord_3323361
  simp only [CollatzResearch.WordTrace]
  refine ⟨121212933713038156716169937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80808622475358771144113291 121212933713038156716169937)
  ·
    refine ⟨90909700284778617537127453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 121212933713038156716169937 90909700284778617537127453)
    ·
      refine ⟨34091137606791981576422795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 90909700284778617537127453 34091137606791981576422795)
      ·
        refine ⟨51136706410187972364634193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34091137606791981576422795 51136706410187972364634193)
        ·
          refine ⟨38352529807640979273475645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51136706410187972364634193 38352529807640979273475645)
          ·
            refine ⟨14382198677865367227553367, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 38352529807640979273475645 14382198677865367227553367)
            ·
              refine ⟨21573298016798050841330051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14382198677865367227553367 21573298016798050841330051)
              ·
                refine ⟨32359947025197076261995077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21573298016798050841330051 32359947025197076261995077)
                ·
                  refine ⟨6067490067224451799124077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 32359947025197076261995077 6067490067224451799124077)
                  ·
                    refine ⟨2275308775209169424671529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6067490067224451799124077 2275308775209169424671529)
                    ·
                      refine ⟨1706481581406877068503647, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2275308775209169424671529 1706481581406877068503647)
                      ·
                        rfl

theorem cell23_3323361_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 3, 1, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 3, 1, 1, 4, 3, 2].length) (baseStart_3323361 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3323361 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3323361 prefixEnd_3323361 := by exact prefixLift 3323361
  have htrace : WordTrace (prefixWord ++ tailWord_3323361) baseStart_3323361 baseEnd_3323361 := by
    simpa [prefixWord, tailWord_3323361, baseEnd_3323361] using wordTrace_append hprefix tailTrace_3323361
  have hstable : (prefixWord ++ tailWord_3323361).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3323361).length < 2 ^ (prefixWord ++ tailWord_3323361).sum := by decide
  have hdescent : baseEnd_3323361 < baseStart_3323361 := by decide
  rcases family_descends (prefixWord ++ tailWord_3323361) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3323407 : List Nat := [1, 1, 2, 1, 1, 1, 2, 2, 1, 4, 7]
def baseStart_3323407 : Nat := 118140960795 + 3323407 * 2 ^ 59
def prefixEnd_3323407 : Nat := 4983230072969 + 3 ^ 40 * 3323407 * 2
def baseEnd_3323407 : Nat := 1706505201516983888528435

theorem tailTrace_3323407 : CollatzResearch.WordTrace tailWord_3323407 prefixEnd_3323407 1706505201516983888528435 := by
  unfold tailWord_3323407
  simp only [CollatzResearch.WordTrace]
  refine ⟨121214611470871506572344475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80809740980581004381562983 121214611470871506572344475)
  ·
    refine ⟨181821917206307259858516713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121214611470871506572344475 181821917206307259858516713)
    ·
      refine ⟨136366437904730444893887535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 181821917206307259858516713 136366437904730444893887535)
      ·
        refine ⟨204549656857095667340831303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 136366437904730444893887535 204549656857095667340831303)
        ·
          refine ⟨306824485285643501011246955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 204549656857095667340831303 306824485285643501011246955)
          ·
            refine ⟨460236727928465251516870433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 306824485285643501011246955 460236727928465251516870433)
            ·
              refine ⟨345177545946348938637652825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 460236727928465251516870433 345177545946348938637652825)
              ·
                refine ⟨258883159459761703978239619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 345177545946348938637652825 258883159459761703978239619)
                ·
                  refine ⟨388324739189642555967359429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 258883159459761703978239619 388324739189642555967359429)
                  ·
                    refine ⟨72810888598057979243879893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 388324739189642555967359429 72810888598057979243879893)
                    ·
                      refine ⟨1706505201516983888528435, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 72810888598057979243879893 1706505201516983888528435)
                      ·
                        rfl

theorem cell23_3323407_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 2, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 2, 1, 4, 7].length) (baseStart_3323407 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3323407 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3323407 prefixEnd_3323407 := by exact prefixLift 3323407
  have htrace : WordTrace (prefixWord ++ tailWord_3323407) baseStart_3323407 baseEnd_3323407 := by
    simpa [prefixWord, tailWord_3323407, baseEnd_3323407] using wordTrace_append hprefix tailTrace_3323407
  have hstable : (prefixWord ++ tailWord_3323407).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3323407).length < 2 ^ (prefixWord ++ tailWord_3323407).sum := by decide
  have hdescent : baseEnd_3323407 < baseStart_3323407 := by decide
  rcases family_descends (prefixWord ++ tailWord_3323407) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3323411 : List Nat := [1, 1, 1, 2, 1, 8, 1, 1, 1, 1, 5]
def baseStart_3323411 : Nat := 118140960795 + 3323411 * 2 ^ 59
def prefixEnd_3323411 : Nat := 4983230072969 + 3 ^ 40 * 3323411 * 2
def baseEnd_3323411 : Nat := 1706507255439601872878417

theorem tailTrace_3323411 : CollatzResearch.WordTrace tailWord_3323411 prefixEnd_3323411 1706507255439601872878417 := by
  unfold tailWord_3323411
  simp only [CollatzResearch.WordTrace]
  refine ⟨121214757362857015255490087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80809838241904676836993391 121214757362857015255490087)
  ·
    refine ⟨181822136044285522883235131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121214757362857015255490087 181822136044285522883235131)
    ·
      refine ⟨272733204066428284324852697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 181822136044285522883235131 272733204066428284324852697)
      ·
        refine ⟨204549903049821213243639523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 272733204066428284324852697 204549903049821213243639523)
        ·
          refine ⟨306824854574731819865459285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 204549903049821213243639523 306824854574731819865459285)
          ·
            refine ⟨3595603764547638514048351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 306824854574731819865459285 3595603764547638514048351)
            ·
              refine ⟨5393405646821457771072527, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3595603764547638514048351 5393405646821457771072527)
              ·
                refine ⟨8090108470232186656608791, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5393405646821457771072527 8090108470232186656608791)
                ·
                  refine ⟨12135162705348279984913187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8090108470232186656608791 12135162705348279984913187)
                  ·
                    refine ⟨18202744058022419977369781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12135162705348279984913187 18202744058022419977369781)
                    ·
                      refine ⟨1706507255439601872878417, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 18202744058022419977369781 1706507255439601872878417)
                      ·
                        rfl

theorem cell23_3323411_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 8, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 8, 1, 1, 1, 1, 5].length) (baseStart_3323411 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3323411 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3323411 prefixEnd_3323411 := by exact prefixLift 3323411
  have htrace : WordTrace (prefixWord ++ tailWord_3323411) baseStart_3323411 baseEnd_3323411 := by
    simpa [prefixWord, tailWord_3323411, baseEnd_3323411] using wordTrace_append hprefix tailTrace_3323411
  have hstable : (prefixWord ++ tailWord_3323411).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3323411).length < 2 ^ (prefixWord ++ tailWord_3323411).sum := by decide
  have hdescent : baseEnd_3323411 < baseStart_3323411 := by decide
  rcases family_descends (prefixWord ++ tailWord_3323411) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3323438 : List Nat := [4, 1, 3, 1, 2, 2, 2, 1, 1, 2, 4]
def baseStart_3323438 : Nat := 118140960795 + 3323438 * 2 ^ 59
def prefixEnd_3323438 : Nat := 4983230072969 + 3 ^ 40 * 3323438 * 2
def baseEnd_3323438 : Nat := 1706521119417273267240793

theorem tailTrace_3323438 : CollatzResearch.WordTrace tailWord_3323438 prefixEnd_3323438 1706521119417273267240793 := by
  unfold tailWord_3323438
  simp only [CollatzResearch.WordTrace]
  refine ⟨15151967766719899858340371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 80810494755839465911148645 15151967766719899858340371)
  ·
    refine ⟨22727951650079849787510557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15151967766719899858340371 22727951650079849787510557)
    ·
      refine ⟨8522981868779943670316459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22727951650079849787510557 8522981868779943670316459)
      ·
        refine ⟨12784472803169915505474689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8522981868779943670316459 12784472803169915505474689)
        ·
          refine ⟨9588354602377436629106017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12784472803169915505474689 9588354602377436629106017)
          ·
            refine ⟨7191265951783077471829513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9588354602377436629106017 7191265951783077471829513)
            ·
              refine ⟨5393449463837308103872135, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7191265951783077471829513 5393449463837308103872135)
              ·
                refine ⟨8090174195755962155808203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5393449463837308103872135 8090174195755962155808203)
                ·
                  refine ⟨12135261293633943233712305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8090174195755962155808203 12135261293633943233712305)
                  ·
                    refine ⟨9101445970225457425284229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12135261293633943233712305 9101445970225457425284229)
                    ·
                      refine ⟨1706521119417273267240793, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9101445970225457425284229 1706521119417273267240793)
                      ·
                        rfl

theorem cell23_3323438_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 2, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 2, 2, 1, 1, 2, 4].length) (baseStart_3323438 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3323438 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3323438 prefixEnd_3323438 := by exact prefixLift 3323438
  have htrace : WordTrace (prefixWord ++ tailWord_3323438) baseStart_3323438 baseEnd_3323438 := by
    simpa [prefixWord, tailWord_3323438, baseEnd_3323438] using wordTrace_append hprefix tailTrace_3323438
  have hstable : (prefixWord ++ tailWord_3323438).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3323438).length < 2 ^ (prefixWord ++ tailWord_3323438).sum := by decide
  have hdescent : baseEnd_3323438 < baseStart_3323438 := by decide
  rcases family_descends (prefixWord ++ tailWord_3323438) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3323441 : List Nat := [1, 2, 2, 3, 1, 1, 1, 2, 6, 1, 3]
def baseStart_3323441 : Nat := 118140960795 + 3323441 * 2 ^ 59
def prefixEnd_3323441 : Nat := 4983230072969 + 3 ^ 40 * 3323441 * 2
def baseEnd_3323441 : Nat := 1706522659859236755503279

theorem tailTrace_3323441 : CollatzResearch.WordTrace tailWord_3323441 prefixEnd_3323441 1706522659859236755503279 := by
  unfold tailWord_3323441
  simp only [CollatzResearch.WordTrace]
  refine ⟨121215851552748330379082177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80810567701832220252721451 121215851552748330379082177)
  ·
    refine ⟨90911888664561247784311633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 121215851552748330379082177 90911888664561247784311633)
    ·
      refine ⟨68183916498420935838233725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 90911888664561247784311633 68183916498420935838233725)
      ·
        refine ⟨25568968686907850939337647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 68183916498420935838233725 25568968686907850939337647)
        ·
          refine ⟨38353453030361776409006471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25568968686907850939337647 38353453030361776409006471)
          ·
            refine ⟨57530179545542664613509707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38353453030361776409006471 57530179545542664613509707)
            ·
              refine ⟨86295269318313996920264561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 57530179545542664613509707 86295269318313996920264561)
              ·
                refine ⟨64721451988735497690198421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 86295269318313996920264561 64721451988735497690198421)
                ·
                  refine ⟨3033818061971976454228051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 64721451988735497690198421 3033818061971976454228051)
                  ·
                    refine ⟨4550727092957964681342077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3033818061971976454228051 4550727092957964681342077)
                    ·
                      refine ⟨1706522659859236755503279, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4550727092957964681342077 1706522659859236755503279)
                      ·
                        rfl

theorem cell23_3323441_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 1, 2, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 1, 2, 6, 1, 3].length) (baseStart_3323441 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3323441 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3323441 prefixEnd_3323441 := by exact prefixLift 3323441
  have htrace : WordTrace (prefixWord ++ tailWord_3323441) baseStart_3323441 baseEnd_3323441 := by
    simpa [prefixWord, tailWord_3323441, baseEnd_3323441] using wordTrace_append hprefix tailTrace_3323441
  have hstable : (prefixWord ++ tailWord_3323441).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3323441).length < 2 ^ (prefixWord ++ tailWord_3323441).sum := by decide
  have hdescent : baseEnd_3323441 < baseStart_3323441 := by decide
  rcases family_descends (prefixWord ++ tailWord_3323441) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3323462 : List Nat := [6, 1, 1, 1, 3, 1, 1, 3, 1, 2, 3]
def baseStart_3323462 : Nat := 118140960795 + 3323462 * 2 ^ 59
def prefixEnd_3323462 : Nat := 4983230072969 + 3 ^ 40 * 3323462 * 2
def baseEnd_3323462 : Nat := 1706533442952981173340683

theorem tailTrace_3323462 : CollatzResearch.WordTrace tailWord_3323462 prefixEnd_3323462 1706533442952981173340683 := by
  unfold tailWord_3323462
  simp only [CollatzResearch.WordTrace]
  refine ⟨3788019296427257842674895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 80811078323781500643731093 3788019296427257842674895)
  ·
    refine ⟨5682028944640886764012343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3788019296427257842674895 5682028944640886764012343)
    ·
      refine ⟨8523043416961330146018515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5682028944640886764012343 8523043416961330146018515)
      ·
        refine ⟨12784565125441995219027773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8523043416961330146018515 12784565125441995219027773)
        ·
          refine ⟨4794211922040748207135415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12784565125441995219027773 4794211922040748207135415)
          ·
            refine ⟨7191317883061122310703123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4794211922040748207135415 7191317883061122310703123)
            ·
              refine ⟨10786976824591683466054685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7191317883061122310703123 10786976824591683466054685)
              ·
                refine ⟨4045116309221881299770507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10786976824591683466054685 4045116309221881299770507)
                ·
                  refine ⟨6067674463832821949655761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4045116309221881299770507 6067674463832821949655761)
                  ·
                    refine ⟨4550755847874616462241821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6067674463832821949655761 4550755847874616462241821)
                    ·
                      refine ⟨1706533442952981173340683, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4550755847874616462241821 1706533442952981173340683)
                      ·
                        rfl

theorem cell23_3323462_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 3, 1, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 3, 1, 1, 3, 1, 2, 3].length) (baseStart_3323462 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3323462 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3323462 prefixEnd_3323462 := by exact prefixLift 3323462
  have htrace : WordTrace (prefixWord ++ tailWord_3323462) baseStart_3323462 baseEnd_3323462 := by
    simpa [prefixWord, tailWord_3323462, baseEnd_3323462] using wordTrace_append hprefix tailTrace_3323462
  have hstable : (prefixWord ++ tailWord_3323462).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3323462).length < 2 ^ (prefixWord ++ tailWord_3323462).sum := by decide
  have hdescent : baseEnd_3323462 < baseStart_3323462 := by decide
  rcases family_descends (prefixWord ++ tailWord_3323462) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3323481 : List Nat := [1, 2, 1, 2, 2, 1, 1, 4, 3, 4, 2]
def baseStart_3323481 : Nat := 118140960795 + 3323481 * 2 ^ 59
def prefixEnd_3323481 : Nat := 4983230072969 + 3 ^ 40 * 3323481 * 2
def baseEnd_3323481 : Nat := 1706543199085416599003095

theorem tailTrace_3323481 : CollatzResearch.WordTrace tailWord_3323481 prefixEnd_3323481 1706543199085416599003095 := by
  unfold tailWord_3323481
  simp only [CollatzResearch.WordTrace]
  refine ⟨121217310472603417210538297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80811540315068944807025531 121217310472603417210538297)
  ·
    refine ⟨90912982854452562907903723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 121217310472603417210538297 90912982854452562907903723)
    ·
      refine ⟨136369474281678844361855585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90912982854452562907903723 136369474281678844361855585)
      ·
        refine ⟨102277105711259133271391689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 136369474281678844361855585 102277105711259133271391689)
        ·
          refine ⟨76707829283444349953543767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 102277105711259133271391689 76707829283444349953543767)
          ·
            refine ⟨115061743925166524930315651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 76707829283444349953543767 115061743925166524930315651)
            ·
              refine ⟨172592615887749787395473477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 115061743925166524930315651 172592615887749787395473477)
              ·
                refine ⟨32361115478953085136651277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 172592615887749787395473477 32361115478953085136651277)
                ·
                  refine ⟨12135418304607406926244229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 32361115478953085136651277 12135418304607406926244229)
                  ·
                    refine ⟨2275390932113888798670793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 12135418304607406926244229 2275390932113888798670793)
                    ·
                      refine ⟨1706543199085416599003095, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2275390932113888798670793 1706543199085416599003095)
                      ·
                        rfl

theorem cell23_3323481_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 1, 4, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 1, 4, 3, 4, 2].length) (baseStart_3323481 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3323481 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3323481 prefixEnd_3323481 := by exact prefixLift 3323481
  have htrace : WordTrace (prefixWord ++ tailWord_3323481) baseStart_3323481 baseEnd_3323481 := by
    simpa [prefixWord, tailWord_3323481, baseEnd_3323481] using wordTrace_append hprefix tailTrace_3323481
  have hstable : (prefixWord ++ tailWord_3323481).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3323481).length < 2 ^ (prefixWord ++ tailWord_3323481).sum := by decide
  have hdescent : baseEnd_3323481 < baseStart_3323481 := by decide
  rcases family_descends (prefixWord ++ tailWord_3323481) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3323502 : List Nat := [4, 1, 2, 2, 3, 1, 2, 2, 1, 3, 2]
def baseStart_3323502 : Nat := 118140960795 + 3323502 * 2 ^ 59
def prefixEnd_3323502 : Nat := 4983230072969 + 3 ^ 40 * 3323502 * 2
def baseEnd_3323502 : Nat := 1706553982179161016840499

theorem tailTrace_3323502 : CollatzResearch.WordTrace tailWord_3323502 prefixEnd_3323502 1706553982179161016840499 := by
  unfold tailWord_3323502
  simp only [CollatzResearch.WordTrace]
  refine ⟨15152259550690917224631595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 80812050937018225198035173 15152259550690917224631595)
  ·
    refine ⟨22728389326036375836947393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15152259550690917224631595 22728389326036375836947393)
    ·
      refine ⟨17046291994527281877710545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22728389326036375836947393 17046291994527281877710545)
      ·
        refine ⟨12784718995895461408282909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17046291994527281877710545 12784718995895461408282909)
        ·
          refine ⟨4794269623460798028106091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12784718995895461408282909 4794269623460798028106091)
          ·
            refine ⟨7191404435191197042159137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4794269623460798028106091 7191404435191197042159137)
            ·
              refine ⟨5393553326393397781619353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7191404435191197042159137 5393553326393397781619353)
              ·
                refine ⟨4045164994795048336214515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5393553326393397781619353 4045164994795048336214515)
                ·
                  refine ⟨6067747492192572504321773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4045164994795048336214515 6067747492192572504321773)
                  ·
                    refine ⟨2275405309572214689120665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6067747492192572504321773 2275405309572214689120665)
                    ·
                      refine ⟨1706553982179161016840499, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2275405309572214689120665 1706553982179161016840499)
                      ·
                        rfl

theorem cell23_3323502_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 3, 1, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 3, 1, 2, 2, 1, 3, 2].length) (baseStart_3323502 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3323502 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3323502 prefixEnd_3323502 := by exact prefixLift 3323502
  have htrace : WordTrace (prefixWord ++ tailWord_3323502) baseStart_3323502 baseEnd_3323502 := by
    simpa [prefixWord, tailWord_3323502, baseEnd_3323502] using wordTrace_append hprefix tailTrace_3323502
  have hstable : (prefixWord ++ tailWord_3323502).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3323502).length < 2 ^ (prefixWord ++ tailWord_3323502).sum := by decide
  have hdescent : baseEnd_3323502 < baseStart_3323502 := by decide
  rcases family_descends (prefixWord ++ tailWord_3323502) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3323588 : List Nat := [2, 3, 3, 1, 1, 1, 1, 4, 2, 1, 4]
def baseStart_3323588 : Nat := 118140960795 + 3323588 * 2 ^ 59
def prefixEnd_3323588 : Nat := 4983230072969 + 3 ^ 40 * 3323588 * 2
def baseEnd_3323588 : Nat := 1706598141515447680365103

theorem tailTrace_3323588 : CollatzResearch.WordTrace tailWord_3323588 prefixEnd_3323588 1706598141515447680365103 := by
  unfold tailWord_3323588
  simp only [CollatzResearch.WordTrace]
  refine ⟨60610606541607887242341709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80814142055477182989788945 60610606541607887242341709)
  ·
    refine ⟨22728977453102957715878141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 60610606541607887242341709 22728977453102957715878141)
    ·
      refine ⟨8523366544913609143454303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22728977453102957715878141 8523366544913609143454303)
      ·
        refine ⟨12785049817370413715181455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8523366544913609143454303 12785049817370413715181455)
        ·
          refine ⟨19177574726055620572772183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12785049817370413715181455 19177574726055620572772183)
          ·
            refine ⟨28766362089083430859158275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19177574726055620572772183 28766362089083430859158275)
            ·
              refine ⟨43149543133625146288737413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28766362089083430859158275 43149543133625146288737413)
              ·
                refine ⟨8090539337554714929138265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 43149543133625146288737413 8090539337554714929138265)
                ·
                  refine ⟨6067904503166036196853699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8090539337554714929138265 6067904503166036196853699)
                  ·
                    refine ⟨9101856754749054295280549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6067904503166036196853699 9101856754749054295280549)
                    ·
                      refine ⟨1706598141515447680365103, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9101856754749054295280549 1706598141515447680365103)
                      ·
                        rfl

theorem cell23_3323588_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 1, 4, 2, 1, 4].length) (baseStart_3323588 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3323588 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3323588 prefixEnd_3323588 := by exact prefixLift 3323588
  have htrace : WordTrace (prefixWord ++ tailWord_3323588) baseStart_3323588 baseEnd_3323588 := by
    simpa [prefixWord, tailWord_3323588, baseEnd_3323588] using wordTrace_append hprefix tailTrace_3323588
  have hstable : (prefixWord ++ tailWord_3323588).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3323588).length < 2 ^ (prefixWord ++ tailWord_3323588).sum := by decide
  have hdescent : baseEnd_3323588 < baseStart_3323588 := by decide
  rcases family_descends (prefixWord ++ tailWord_3323588) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3323598 : List Nat := [4, 1, 1, 1, 3, 1, 2, 3, 3, 4]
def baseStart_3323598 : Nat := 118140960795 + 3323598 * 2 ^ 59
def prefixEnd_3323598 : Nat := 4983230072969 + 3 ^ 40 * 3323598 * 2
def baseEnd_3323598 : Nat := 568867758773997547080019

theorem tailTrace_3323598 : CollatzResearch.WordTrace tailWord_3323598 prefixEnd_3323598 568867758773997547080019 := by
  unfold tailWord_3323598
  simp only [CollatzResearch.WordTrace]
  refine ⟨15152697226647443274068431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 80814385208786364128364965 15152697226647443274068431)
  ·
    refine ⟨22729045839971164911102647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15152697226647443274068431 22729045839971164911102647)
    ·
      refine ⟨34093568759956747366653971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22729045839971164911102647 34093568759956747366653971)
      ·
        refine ⟨51140353139935121049980957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34093568759956747366653971 51140353139935121049980957)
        ·
          refine ⟨19177632427475670393742859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 51140353139935121049980957 19177632427475670393742859)
          ·
            refine ⟨28766448641213505590614289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19177632427475670393742859 28766448641213505590614289)
            ·
              refine ⟨21574836480910129192960717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28766448641213505590614289 21574836480910129192960717)
              ·
                refine ⟨8090563680341298447360269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21574836480910129192960717 8090563680341298447360269)
                ·
                  refine ⟨3033961380127986917760101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8090563680341298447360269 3033961380127986917760101)
                  ·
                    refine ⟨568867758773997547080019, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3033961380127986917760101 568867758773997547080019)
                    ·
                      rfl

theorem cell23_3323598_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 2, 3, 3, 4].length) (baseStart_3323598 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3323598 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3323598 prefixEnd_3323598 := by exact prefixLift 3323598
  have htrace : WordTrace (prefixWord ++ tailWord_3323598) baseStart_3323598 baseEnd_3323598 := by
    simpa [prefixWord, tailWord_3323598, baseEnd_3323598] using wordTrace_append hprefix tailTrace_3323598
  have hstable : (prefixWord ++ tailWord_3323598).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3323598).length < 2 ^ (prefixWord ++ tailWord_3323598).sum := by decide
  have hdescent : baseEnd_3323598 < baseStart_3323598 := by decide
  rcases family_descends (prefixWord ++ tailWord_3323598) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3323698 : List Nat := [3, 2, 1, 1, 3, 2, 1, 3, 1, 1, 5]
def baseStart_3323698 : Nat := 118140960795 + 3323698 * 2 ^ 59
def prefixEnd_3323698 : Nat := 4983230072969 + 3 ^ 40 * 3323698 * 2
def baseEnd_3323698 : Nat := 1706654624387442249989597

theorem tailTrace_3323698 : CollatzResearch.WordTrace tailWord_3323698 prefixEnd_3323698 1706654624387442249989597 := by
  unfold tailWord_3323698
  simp only [CollatzResearch.WordTrace]
  refine ⟨30306306278204315817796937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 80816816741878175514125165 30306306278204315817796937)
  ·
    refine ⟨22729729708653236863347703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30306306278204315817796937 22729729708653236863347703)
    ·
      refine ⟨34094594562979855295021555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22729729708653236863347703 34094594562979855295021555)
      ·
        refine ⟨51141891844469782942532333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34094594562979855295021555 51141891844469782942532333)
        ·
          refine ⟨19178209441676168603449625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 51141891844469782942532333 19178209441676168603449625)
          ·
            refine ⟨14383657081257126452587219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19178209441676168603449625 14383657081257126452587219)
            ·
              refine ⟨21575485621885689678880829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14383657081257126452587219 21575485621885689678880829)
              ·
                refine ⟨8090807108207133629580311, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21575485621885689678880829 8090807108207133629580311)
                ·
                  refine ⟨12136210662310700444370467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8090807108207133629580311 12136210662310700444370467)
                  ·
                    refine ⟨18204315993466050666555701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12136210662310700444370467 18204315993466050666555701)
                    ·
                      refine ⟨1706654624387442249989597, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 18204315993466050666555701 1706654624387442249989597)
                      ·
                        rfl

theorem cell23_3323698_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 2, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 2, 1, 3, 1, 1, 5].length) (baseStart_3323698 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3323698 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3323698 prefixEnd_3323698 := by exact prefixLift 3323698
  have htrace : WordTrace (prefixWord ++ tailWord_3323698) baseStart_3323698 baseEnd_3323698 := by
    simpa [prefixWord, tailWord_3323698, baseEnd_3323698] using wordTrace_append hprefix tailTrace_3323698
  have hstable : (prefixWord ++ tailWord_3323698).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3323698).length < 2 ^ (prefixWord ++ tailWord_3323698).sum := by decide
  have hdescent : baseEnd_3323698 < baseStart_3323698 := by decide
  rcases family_descends (prefixWord ++ tailWord_3323698) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3323721 : List Nat := [1, 2, 1, 1, 2, 4, 1, 1, 2, 2, 6]
def baseStart_3323721 : Nat := 118140960795 + 3323721 * 2 ^ 59
def prefixEnd_3323721 : Nat := 4983230072969 + 3 ^ 40 * 3323721 * 2
def baseEnd_3323721 : Nat := 1706666434442495660001991

theorem tailTrace_3323721 : CollatzResearch.WordTrace tailWord_3323721 prefixEnd_3323721 1706666434442495660001991 := by
  unfold tailWord_3323721
  simp only [CollatzResearch.WordTrace]
  refine ⟨121226063991733938199275017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80817375994489292132850011 121226063991733938199275017)
  ·
    refine ⟨90919547993800453649456263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 121226063991733938199275017 90919547993800453649456263)
    ·
      refine ⟨136379321990700680474184395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90919547993800453649456263 136379321990700680474184395)
      ·
        refine ⟨204568982986051020711276593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 136379321990700680474184395 204568982986051020711276593)
        ·
          refine ⟨153426737239538265533457445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 204568982986051020711276593 153426737239538265533457445)
          ·
            refine ⟨28767513232413424787523271, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 153426737239538265533457445 28767513232413424787523271)
            ·
              refine ⟨43151269848620137181284907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28767513232413424787523271 43151269848620137181284907)
              ·
                refine ⟨64726904772930205771927361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43151269848620137181284907 64726904772930205771927361)
                ·
                  refine ⟨48545178579697654328945521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 64726904772930205771927361 48545178579697654328945521)
                  ·
                    refine ⟨36408883934773240746709141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 48545178579697654328945521 36408883934773240746709141)
                    ·
                      refine ⟨1706666434442495660001991, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 36408883934773240746709141 1706666434442495660001991)
                      ·
                        rfl

theorem cell23_3323721_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 1, 1, 2, 2, 6].length) (baseStart_3323721 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3323721 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3323721 prefixEnd_3323721 := by exact prefixLift 3323721
  have htrace : WordTrace (prefixWord ++ tailWord_3323721) baseStart_3323721 baseEnd_3323721 := by
    simpa [prefixWord, tailWord_3323721, baseEnd_3323721] using wordTrace_append hprefix tailTrace_3323721
  have hstable : (prefixWord ++ tailWord_3323721).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3323721).length < 2 ^ (prefixWord ++ tailWord_3323721).sum := by decide
  have hdescent : baseEnd_3323721 < baseStart_3323721 := by decide
  rcases family_descends (prefixWord ++ tailWord_3323721) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3323725 : List Nat := [1, 6, 1, 2, 1, 1, 2, 1, 1, 1, 6]
def baseStart_3323725 : Nat := 118140960795 + 3323725 * 2 ^ 59
def prefixEnd_3323725 : Nat := 4983230072969 + 3 ^ 40 * 3323725 * 2
def baseEnd_3323725 : Nat := 1706668488365113644351973

theorem tailTrace_3323725 : CollatzResearch.WordTrace tailWord_3323725 prefixEnd_3323725 1706668488365113644351973 := by
  unfold tailWord_3323725
  simp only [CollatzResearch.WordTrace]
  refine ⟨121226209883719446882420629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80817473255812964588280419 121226209883719446882420629)
  ·
    refine ⟨5682478588299349072613467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 121226209883719446882420629 5682478588299349072613467)
    ·
      refine ⟨8523717882449023608920201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5682478588299349072613467 8523717882449023608920201)
      ·
        refine ⟨6392788411836767706690151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8523717882449023608920201 6392788411836767706690151)
        ·
          refine ⟨9589182617755151560035227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6392788411836767706690151 9589182617755151560035227)
          ·
            refine ⟨14383773926632727340052841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9589182617755151560035227 14383773926632727340052841)
            ·
              refine ⟨10787830444974545505039631, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14383773926632727340052841 10787830444974545505039631)
              ·
                refine ⟨16181745667461818257559447, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10787830444974545505039631 16181745667461818257559447)
                ·
                  refine ⟨24272618501192727386339171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16181745667461818257559447 24272618501192727386339171)
                  ·
                    refine ⟨36408927751789091079508757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 24272618501192727386339171 36408927751789091079508757)
                    ·
                      refine ⟨1706668488365113644351973, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 36408927751789091079508757 1706668488365113644351973)
                      ·
                        rfl

theorem cell23_3323725_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 1, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 1, 2, 1, 1, 1, 6].length) (baseStart_3323725 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3323725 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3323725 prefixEnd_3323725 := by exact prefixLift 3323725
  have htrace : WordTrace (prefixWord ++ tailWord_3323725) baseStart_3323725 baseEnd_3323725 := by
    simpa [prefixWord, tailWord_3323725, baseEnd_3323725] using wordTrace_append hprefix tailTrace_3323725
  have hstable : (prefixWord ++ tailWord_3323725).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3323725).length < 2 ^ (prefixWord ++ tailWord_3323725).sum := by decide
  have hdescent : baseEnd_3323725 < baseStart_3323725 := by decide
  rcases family_descends (prefixWord ++ tailWord_3323725) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3323728 : List Nat := [2, 1, 1, 1, 1, 4, 1, 5, 1, 3, 3]
def baseStart_3323728 : Nat := 118140960795 + 3323728 * 2 ^ 59
def prefixEnd_3323728 : Nat := 4983230072969 + 3 ^ 40 * 3323728 * 2
def baseEnd_3323728 : Nat := 1706670028807077132614459

theorem tailTrace_3323728 : CollatzResearch.WordTrace tailWord_3323728 prefixEnd_3323728 1706670028807077132614459 := by
  unfold tailWord_3323728
  simp only [CollatzResearch.WordTrace]
  refine ⟨60613159651354289197389919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80817546201805718929853225 60613159651354289197389919)
  ·
    refine ⟨90919739477031433796084879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60613159651354289197389919 90919739477031433796084879)
    ·
      refine ⟨136379609215547150694127319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90919739477031433796084879 136379609215547150694127319)
      ·
        refine ⟨204569413823320726041190979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 136379609215547150694127319 204569413823320726041190979)
        ·
          refine ⟨306854120734981089061786469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 204569413823320726041190979 306854120734981089061786469)
          ·
            refine ⟨57535147637808954199084963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 306854120734981089061786469 57535147637808954199084963)
            ·
              refine ⟨86302721456713431298627445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 57535147637808954199084963 86302721456713431298627445)
              ·
                refine ⟨8090880136566884184246323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 86302721456713431298627445 8090880136566884184246323)
                ·
                  refine ⟨12136320204850326276369485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8090880136566884184246323 12136320204850326276369485)
                  ·
                    refine ⟨4551120076818872353638557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12136320204850326276369485 4551120076818872353638557)
                    ·
                      refine ⟨1706670028807077132614459, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4551120076818872353638557 1706670028807077132614459)
                      ·
                        rfl

theorem cell23_3323728_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 1, 5, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 1, 5, 1, 3, 3].length) (baseStart_3323728 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3323728 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3323728 prefixEnd_3323728 := by exact prefixLift 3323728
  have htrace : WordTrace (prefixWord ++ tailWord_3323728) baseStart_3323728 baseEnd_3323728 := by
    simpa [prefixWord, tailWord_3323728, baseEnd_3323728] using wordTrace_append hprefix tailTrace_3323728
  have hstable : (prefixWord ++ tailWord_3323728).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3323728).length < 2 ^ (prefixWord ++ tailWord_3323728).sum := by decide
  have hdescent : baseEnd_3323728 < baseStart_3323728 := by decide
  rcases family_descends (prefixWord ++ tailWord_3323728) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3323732 : List Nat := [2, 4, 1, 1, 3, 1, 3, 2, 1, 2, 3]
def baseStart_3323732 : Nat := 118140960795 + 3323732 * 2 ^ 59
def prefixEnd_3323732 : Nat := 4983230072969 + 3 ^ 40 * 3323732 * 2
def baseEnd_3323732 : Nat := 1706672082729695116964441

theorem tailTrace_3323732 : CollatzResearch.WordTrace tailWord_3323732 prefixEnd_3323732 1706672082729695116964441 := by
  unfold tailWord_3323732
  simp only [CollatzResearch.WordTrace]
  refine ⟨60613232597347043538962725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80817643463129391385283633 60613232597347043538962725)
  ·
    refine ⟨11364981112002570663555511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 60613232597347043538962725 11364981112002570663555511)
    ·
      refine ⟨17047471668003855995333267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11364981112002570663555511 17047471668003855995333267)
      ·
        refine ⟨25571207502005783992999901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17047471668003855995333267 25571207502005783992999901)
        ·
          refine ⟨9589202813252168997374963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25571207502005783992999901 9589202813252168997374963)
          ·
            refine ⟨14383804219878253496062445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9589202813252168997374963 14383804219878253496062445)
            ·
              refine ⟨5393926582454345061023417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14383804219878253496062445 5393926582454345061023417)
              ·
                refine ⟨4045444936840758795767563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5393926582454345061023417 4045444936840758795767563)
                ·
                  refine ⟨6068167405261138193651345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4045444936840758795767563 6068167405261138193651345)
                  ·
                    refine ⟨4551125553945853645238509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6068167405261138193651345 4551125553945853645238509)
                    ·
                      refine ⟨1706672082729695116964441, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4551125553945853645238509 1706672082729695116964441)
                      ·
                        rfl

theorem cell23_3323732_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 1, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 1, 3, 2, 1, 2, 3].length) (baseStart_3323732 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3323732 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3323732 prefixEnd_3323732 := by exact prefixLift 3323732
  have htrace : WordTrace (prefixWord ++ tailWord_3323732) baseStart_3323732 baseEnd_3323732 := by
    simpa [prefixWord, tailWord_3323732, baseEnd_3323732] using wordTrace_append hprefix tailTrace_3323732
  have hstable : (prefixWord ++ tailWord_3323732).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3323732).length < 2 ^ (prefixWord ++ tailWord_3323732).sum := by decide
  have hdescent : baseEnd_3323732 < baseStart_3323732 := by decide
  rcases family_descends (prefixWord ++ tailWord_3323732) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3323788 : List Nat := [2, 2, 1, 2, 1, 2, 1, 1, 4, 4, 3]
def baseStart_3323788 : Nat := 118140960795 + 3323788 * 2 ^ 59
def prefixEnd_3323788 : Nat := 4983230072969 + 3 ^ 40 * 3323788 * 2
def baseEnd_3323788 : Nat := 1706700837646346897864183

theorem tailTrace_3323788 : CollatzResearch.WordTrace tailWord_3323788 prefixEnd_3323788 1706700837646346897864183 := by
  unfold tailWord_3323788
  simp only [CollatzResearch.WordTrace]
  refine ⟨60614253841245604320982009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80819005121660805761309345 60614253841245604320982009)
  ·
    refine ⟨45460690380934203240736507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60614253841245604320982009 45460690380934203240736507)
    ·
      refine ⟨68191035571401304861104761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45460690380934203240736507 68191035571401304861104761)
      ·
        refine ⟨51143276678550978645828571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 68191035571401304861104761 51143276678550978645828571)
        ·
          refine ⟨76714915017826467968742857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51143276678550978645828571 76714915017826467968742857)
          ·
            refine ⟨57536186263369850976557143, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 76714915017826467968742857 57536186263369850976557143)
            ·
              refine ⟨86304279395054776464835715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 57536186263369850976557143 86304279395054776464835715)
              ·
                refine ⟨129456419092582164697253573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 86304279395054776464835715 129456419092582164697253573)
                ·
                  refine ⟨24273078579859155880735045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 129456419092582164697253573 24273078579859155880735045)
                  ·
                    refine ⟨4551202233723591727637821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 24273078579859155880735045 4551202233723591727637821)
                    ·
                      refine ⟨1706700837646346897864183, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4551202233723591727637821 1706700837646346897864183)
                      ·
                        rfl

theorem cell23_3323788_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 1, 1, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 1, 1, 4, 4, 3].length) (baseStart_3323788 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3323788 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3323788 prefixEnd_3323788 := by exact prefixLift 3323788
  have htrace : WordTrace (prefixWord ++ tailWord_3323788) baseStart_3323788 baseEnd_3323788 := by
    simpa [prefixWord, tailWord_3323788, baseEnd_3323788] using wordTrace_append hprefix tailTrace_3323788
  have hstable : (prefixWord ++ tailWord_3323788).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3323788).length < 2 ^ (prefixWord ++ tailWord_3323788).sum := by decide
  have hdescent : baseEnd_3323788 < baseStart_3323788 := by decide
  rcases family_descends (prefixWord ++ tailWord_3323788) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3323802 : List Nat := [3, 1, 1, 4, 2, 1, 2, 2, 1, 4, 2]
def baseStart_3323802 : Nat := 118140960795 + 3323802 * 2 ^ 59
def prefixEnd_3323802 : Nat := 4983230072969 + 3 ^ 40 * 3323802 * 2
def baseEnd_3323802 : Nat := 1706708026375509843089119

theorem tailTrace_3323802 : CollatzResearch.WordTrace tailWord_3323802 prefixEnd_3323802 1706708026375509843089119 := by
  unfold tailWord_3323802
  simp only [CollatzResearch.WordTrace]
  refine ⟨30307254576110122258243415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 80819345536293659355315773 30307254576110122258243415)
  ·
    refine ⟨45460881864165183387365123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30307254576110122258243415 45460881864165183387365123)
    ·
      refine ⟨68191322796247775081047685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45460881864165183387365123 68191322796247775081047685)
      ·
        refine ⟨12785873024296457827696441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 68191322796247775081047685 12785873024296457827696441)
        ·
          refine ⟨9589404768222343370772331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12785873024296457827696441 9589404768222343370772331)
          ·
            refine ⟨14384107152333515056158497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9589404768222343370772331 14384107152333515056158497)
            ·
              refine ⟨10788080364250136292118873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14384107152333515056158497 10788080364250136292118873)
              ·
                refine ⟨8091060273187602219089155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10788080364250136292118873 8091060273187602219089155)
                ·
                  refine ⟨12136590409781403328633733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8091060273187602219089155 12136590409781403328633733)
                  ·
                    refine ⟨2275610701834013124118825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 12136590409781403328633733 2275610701834013124118825)
                    ·
                      refine ⟨1706708026375509843089119, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2275610701834013124118825 1706708026375509843089119)
                      ·
                        rfl

theorem cell23_3323802_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 1, 2, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 1, 2, 2, 1, 4, 2].length) (baseStart_3323802 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3323802 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3323802 prefixEnd_3323802 := by exact prefixLift 3323802
  have htrace : WordTrace (prefixWord ++ tailWord_3323802) baseStart_3323802 baseEnd_3323802 := by
    simpa [prefixWord, tailWord_3323802, baseEnd_3323802] using wordTrace_append hprefix tailTrace_3323802
  have hstable : (prefixWord ++ tailWord_3323802).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3323802).length < 2 ^ (prefixWord ++ tailWord_3323802).sum := by decide
  have hdescent : baseEnd_3323802 < baseStart_3323802 := by decide
  rcases family_descends (prefixWord ++ tailWord_3323802) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3323815 : List Nat := [1, 1, 6, 1, 2, 1, 1, 2, 2, 2, 4]
def baseStart_3323815 : Nat := 118140960795 + 3323815 * 2 ^ 59
def prefixEnd_3323815 : Nat := 4983230072969 + 3 ^ 40 * 3323815 * 2
def baseEnd_3323815 : Nat := 1706714701624018292226559

theorem tailTrace_3323815 : CollatzResearch.WordTrace tailWord_3323815 prefixEnd_3323815 1706714701624018292226559 := by
  unfold tailWord_3323815
  simp only [CollatzResearch.WordTrace]
  refine ⟨121229492453393392253196899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80819661635595594835464599 121229492453393392253196899)
  ·
    refine ⟨181844238680090088379795349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121229492453393392253196899 181844238680090088379795349)
    ·
      refine ⟨8523948688129222892802907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 181844238680090088379795349 8523948688129222892802907)
      ·
        refine ⟨12785923032193834339204361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8523948688129222892802907 12785923032193834339204361)
        ·
          refine ⟨9589442274145375754403271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12785923032193834339204361 9589442274145375754403271)
          ·
            refine ⟨14384163411218063631604907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9589442274145375754403271 14384163411218063631604907)
            ·
              refine ⟨21576245116827095447407361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14384163411218063631604907 21576245116827095447407361)
              ·
                refine ⟨16182183837620321585555521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21576245116827095447407361 16182183837620321585555521)
                ·
                  refine ⟨12136637878215241189166641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16182183837620321585555521 12136637878215241189166641)
                  ·
                    refine ⟨9102478408661430891874981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12136637878215241189166641 9102478408661430891874981)
                    ·
                      refine ⟨1706714701624018292226559, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9102478408661430891874981 1706714701624018292226559)
                      ·
                        rfl

theorem cell23_3323815_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 1, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 1, 1, 2, 2, 2, 4].length) (baseStart_3323815 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3323815 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3323815 prefixEnd_3323815 := by exact prefixLift 3323815
  have htrace : WordTrace (prefixWord ++ tailWord_3323815) baseStart_3323815 baseEnd_3323815 := by
    simpa [prefixWord, tailWord_3323815, baseEnd_3323815] using wordTrace_append hprefix tailTrace_3323815
  have hstable : (prefixWord ++ tailWord_3323815).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3323815).length < 2 ^ (prefixWord ++ tailWord_3323815).sum := by decide
  have hdescent : baseEnd_3323815 < baseStart_3323815 := by decide
  rcases family_descends (prefixWord ++ tailWord_3323815) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3323825 : List Nat := [1, 2, 2, 4, 2, 2, 2, 1, 7]
def baseStart_3323825 : Nat := 118140960795 + 3323825 * 2 ^ 59
def prefixEnd_3323825 : Nat := 4983230072969 + 3 ^ 40 * 3323825 * 2
def baseEnd_3323825 : Nat := 189635537381173694789057

theorem tailTrace_3323825 : CollatzResearch.WordTrace tailWord_3323825 prefixEnd_3323825 189635537381173694789057 := by
  unfold tailWord_3323825
  simp only [CollatzResearch.WordTrace]
  refine ⟨121229857183357163961060929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80819904788904775974040619 121229857183357163961060929)
  ·
    refine ⟨90922392887517872970795697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 121229857183357163961060929 90922392887517872970795697)
    ·
      refine ⟨68191794665638404728096773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 90922392887517872970795697 68191794665638404728096773)
      ·
        refine ⟨12785961499807200886518145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 68191794665638404728096773 12785961499807200886518145)
        ·
          refine ⟨9589471124855400664888609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12785961499807200886518145 9589471124855400664888609)
          ·
            refine ⟨7192103343641550498666457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9589471124855400664888609 7192103343641550498666457)
            ·
              refine ⟨5394077507731162873999843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7192103343641550498666457 5394077507731162873999843)
              ·
                refine ⟨8091116261596744310999765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5394077507731162873999843 8091116261596744310999765)
                ·
                  refine ⟨189635537381173694789057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 8091116261596744310999765 189635537381173694789057)
                  ·
                    rfl

theorem cell23_3323825_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 2, 2, 1, 7].length) (baseStart_3323825 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3323825 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3323825 prefixEnd_3323825 := by exact prefixLift 3323825
  have htrace : WordTrace (prefixWord ++ tailWord_3323825) baseStart_3323825 baseEnd_3323825 := by
    simpa [prefixWord, tailWord_3323825, baseEnd_3323825] using wordTrace_append hprefix tailTrace_3323825
  have hstable : (prefixWord ++ tailWord_3323825).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3323825).length < 2 ^ (prefixWord ++ tailWord_3323825).sum := by decide
  have hdescent : baseEnd_3323825 < baseStart_3323825 := by decide
  rcases family_descends (prefixWord ++ tailWord_3323825) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3323836 : List Nat := [2, 2, 2, 5, 1, 2, 1, 1, 1, 4, 2]
def baseStart_3323836 : Nat := 118140960795 + 3323836 * 2 ^ 59
def prefixEnd_3323836 : Nat := 4983230072969 + 3 ^ 40 * 3323836 * 2
def baseEnd_3323836 : Nat := 1706725484717762710063963

theorem tailTrace_3323836 : CollatzResearch.WordTrace tailWord_3323836 prefixEnd_3323836 1706725484717762710063963 := by
  unfold tailWord_3323836
  simp only [CollatzResearch.WordTrace]
  refine ⟨60615129193158656419855681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80820172257544875226474241 60615129193158656419855681)
  ·
    refine ⟨45461346894868992314891761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60615129193158656419855681 45461346894868992314891761)
    ·
      refine ⟨34096010171151744236168821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45461346894868992314891761 34096010171151744236168821)
      ·
        refine ⟨3196500953545476022140827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 34096010171151744236168821 3196500953545476022140827)
        ·
          refine ⟨4794751430318214033211241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3196500953545476022140827 4794751430318214033211241)
          ·
            refine ⟨3596063572738660524908431, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4794751430318214033211241 3596063572738660524908431)
            ·
              refine ⟨5394095359107990787362647, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3596063572738660524908431 5394095359107990787362647)
              ·
                refine ⟨8091143038661986181043971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5394095359107990787362647 8091143038661986181043971)
                ·
                  refine ⟨12136714557992979271565957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8091143038661986181043971 12136714557992979271565957)
                  ·
                    refine ⟨2275633979623683613418617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 12136714557992979271565957 2275633979623683613418617)
                    ·
                      refine ⟨1706725484717762710063963, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2275633979623683613418617 1706725484717762710063963)
                      ·
                        rfl

theorem cell23_3323836_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 5, 1, 2, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 5, 1, 2, 1, 1, 1, 4, 2].length) (baseStart_3323836 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3323836 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3323836 prefixEnd_3323836 := by exact prefixLift 3323836
  have htrace : WordTrace (prefixWord ++ tailWord_3323836) baseStart_3323836 baseEnd_3323836 := by
    simpa [prefixWord, tailWord_3323836, baseEnd_3323836] using wordTrace_append hprefix tailTrace_3323836
  have hstable : (prefixWord ++ tailWord_3323836).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3323836).length < 2 ^ (prefixWord ++ tailWord_3323836).sum := by decide
  have hdescent : baseEnd_3323836 < baseStart_3323836 := by decide
  rcases family_descends (prefixWord ++ tailWord_3323836) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3323875 : List Nat := [1, 1, 1, 6, 1, 2, 1, 1, 4, 1, 4]
def baseStart_3323875 : Nat := 118140960795 + 3323875 * 2 ^ 59
def prefixEnd_3323875 : Nat := 4983230072969 + 3 ^ 40 * 3323875 * 2
def baseEnd_3323875 : Nat := 1706745510463288057476283

theorem tailTrace_3323875 : CollatzResearch.WordTrace tailWord_3323875 prefixEnd_3323875 1706745510463288057476283 := by
  unfold tailWord_3323875
  simp only [CollatzResearch.WordTrace]
  refine ⟨121231680833176022500381079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80821120555450681666920719 121231680833176022500381079)
  ·
    refine ⟨181847521249764033750571619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121231680833176022500381079 181847521249764033750571619)
    ·
      refine ⟨272771281874646050625857429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 181847521249764033750571619 272771281874646050625857429)
      ·
        refine ⟨12786153837874033623087067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 272771281874646050625857429 12786153837874033623087067)
        ·
          refine ⟨19179230756811050434630601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12786153837874033623087067 19179230756811050434630601)
          ·
            refine ⟨14384423067608287825972951, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19179230756811050434630601 14384423067608287825972951)
            ·
              refine ⟨21576634601412431738959427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14384423067608287825972951 21576634601412431738959427)
              ·
                refine ⟨32364951902118647608439141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21576634601412431738959427 32364951902118647608439141)
                ·
                  refine ⟨6068428481647246426582339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 32364951902118647608439141 6068428481647246426582339)
                  ·
                    refine ⟨9102642722470869639873509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6068428481647246426582339 9102642722470869639873509)
                    ·
                      refine ⟨1706745510463288057476283, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9102642722470869639873509 1706745510463288057476283)
                      ·
                        rfl

theorem cell23_3323875_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 2, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 2, 1, 1, 4, 1, 4].length) (baseStart_3323875 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3323875 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3323875 prefixEnd_3323875 := by exact prefixLift 3323875
  have htrace : WordTrace (prefixWord ++ tailWord_3323875) baseStart_3323875 baseEnd_3323875 := by
    simpa [prefixWord, tailWord_3323875, baseEnd_3323875] using wordTrace_append hprefix tailTrace_3323875
  have hstable : (prefixWord ++ tailWord_3323875).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3323875).length < 2 ^ (prefixWord ++ tailWord_3323875).sum := by decide
  have hdescent : baseEnd_3323875 < baseStart_3323875 := by decide
  rcases family_descends (prefixWord ++ tailWord_3323875) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3323888 : List Nat := [2, 1, 1, 1, 3, 2, 2, 2, 2, 1, 6]
def baseStart_3323888 : Nat := 118140960795 + 3323888 * 2 ^ 59
def prefixEnd_3323888 : Nat := 4983230072969 + 3 ^ 40 * 3323888 * 2
def baseEnd_3323888 : Nat := 1706752185711796506613723

theorem tailTrace_3323888 : CollatzResearch.WordTrace tailWord_3323888 prefixEnd_3323888 1706752185711796506613723 := by
  unfold tailWord_3323888
  simp only [CollatzResearch.WordTrace]
  refine ⟨60616077491064462860302159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80821436654752617147069545 60616077491064462860302159)
  ·
    refine ⟨90924116236596694290453239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60616077491064462860302159 90924116236596694290453239)
    ·
      refine ⟨136386174354895041435679859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90924116236596694290453239 136386174354895041435679859)
      ·
        refine ⟨204579261532342562153519789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 136386174354895041435679859 204579261532342562153519789)
        ·
          refine ⟨76717223074628460807569921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 204579261532342562153519789 76717223074628460807569921)
          ·
            refine ⟨57537917305971345605677441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 76717223074628460807569921 57537917305971345605677441)
            ·
              refine ⟨43153437979478509204258081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 57537917305971345605677441 43153437979478509204258081)
              ·
                refine ⟨32365078484608881903193561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 43153437979478509204258081 32365078484608881903193561)
                ·
                  refine ⟨24273808863456661427395171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32365078484608881903193561 24273808863456661427395171)
                  ·
                    refine ⟨36410713295184992141092757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 24273808863456661427395171 36410713295184992141092757)
                    ·
                      refine ⟨1706752185711796506613723, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 36410713295184992141092757 1706752185711796506613723)
                      ·
                        rfl

theorem cell23_3323888_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 2, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 2, 2, 2, 1, 6].length) (baseStart_3323888 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3323888 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3323888 prefixEnd_3323888 := by exact prefixLift 3323888
  have htrace : WordTrace (prefixWord ++ tailWord_3323888) baseStart_3323888 baseEnd_3323888 := by
    simpa [prefixWord, tailWord_3323888, baseEnd_3323888] using wordTrace_append hprefix tailTrace_3323888
  have hstable : (prefixWord ++ tailWord_3323888).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3323888).length < 2 ^ (prefixWord ++ tailWord_3323888).sum := by decide
  have hdescent : baseEnd_3323888 < baseStart_3323888 := by decide
  rcases family_descends (prefixWord ++ tailWord_3323888) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3323912 : List Nat := [2, 1, 3, 2, 1, 2, 4, 1, 2, 2, 3]
def baseStart_3323912 : Nat := 118140960795 + 3323912 * 2 ^ 59
def prefixEnd_3323912 : Nat := 4983230072969 + 3 ^ 40 * 3323912 * 2
def baseEnd_3323912 : Nat := 1706764509247504412713613

theorem tailTrace_3323912 : CollatzResearch.WordTrace tailWord_3323912 prefixEnd_3323912 1706764509247504412713613 := by
  unfold tailWord_3323912
  simp only [CollatzResearch.WordTrace]
  refine ⟨60616515167020988909738995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80822020222694651879651993 60616515167020988909738995)
  ·
    refine ⟨90924772750531483364608493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60616515167020988909738995 90924772750531483364608493)
    ·
      refine ⟨34096789781449306261728185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 90924772750531483364608493 34096789781449306261728185)
      ·
        refine ⟨25572592336086979696296139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34096789781449306261728185 25572592336086979696296139)
        ·
          refine ⟨38358888504130469544444209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25572592336086979696296139 38358888504130469544444209)
          ·
            refine ⟨28769166378097852158333157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38358888504130469544444209 28769166378097852158333157)
            ·
              refine ⟨5394218695893347279687467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 28769166378097852158333157 5394218695893347279687467)
              ·
                refine ⟨8091328043840020919531201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5394218695893347279687467 8091328043840020919531201)
                ·
                  refine ⟨6068496032880015689648401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8091328043840020919531201 6068496032880015689648401)
                  ·
                    refine ⟨4551372024660011767236301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6068496032880015689648401 4551372024660011767236301)
                    ·
                      refine ⟨1706764509247504412713613, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4551372024660011767236301 1706764509247504412713613)
                      ·
                        rfl

theorem cell23_3323912_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 4, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 4, 1, 2, 2, 3].length) (baseStart_3323912 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3323912 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3323912 prefixEnd_3323912 := by exact prefixLift 3323912
  have htrace : WordTrace (prefixWord ++ tailWord_3323912) baseStart_3323912 baseEnd_3323912 := by
    simpa [prefixWord, tailWord_3323912, baseEnd_3323912] using wordTrace_append hprefix tailTrace_3323912
  have hstable : (prefixWord ++ tailWord_3323912).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3323912).length < 2 ^ (prefixWord ++ tailWord_3323912).sum := by decide
  have hdescent : baseEnd_3323912 < baseStart_3323912 := by decide
  rcases family_descends (prefixWord ++ tailWord_3323912) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3323932 : List Nat := [2, 2, 3, 1, 3, 2, 2, 2, 6]
def baseStart_3323932 : Nat := 118140960795 + 3323932 * 2 ^ 59
def prefixEnd_3323932 : Nat := 4983230072969 + 3 ^ 40 * 3323932 * 2
def baseEnd_3323932 : Nat := 189641642095621592718169

theorem tailTrace_3323932 : CollatzResearch.WordTrace tailWord_3323932 prefixEnd_3323932 189641642095621592718169 := by
  unfold tailWord_3323932
  simp only [CollatzResearch.WordTrace]
  refine ⟨60616879896984760617603025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80822506529313014156804033 60616879896984760617603025)
  ·
    refine ⟨45462659922738570463202269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60616879896984760617603025 45462659922738570463202269)
    ·
      refine ⟨17048497471026963923700851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 45462659922738570463202269 17048497471026963923700851)
      ·
        refine ⟨25572746206540445885551277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17048497471026963923700851 25572746206540445885551277)
        ·
          refine ⟨9589779827452667207081729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25572746206540445885551277 9589779827452667207081729)
          ·
            refine ⟨7192334870589500405311297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9589779827452667207081729 7192334870589500405311297)
            ·
              refine ⟨5394251152942125303983473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7192334870589500405311297 5394251152942125303983473)
              ·
                refine ⟨4045688364706593977987605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5394251152942125303983473 4045688364706593977987605)
                ·
                  refine ⟨189641642095621592718169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4045688364706593977987605 189641642095621592718169)
                  ·
                    rfl

theorem cell23_3323932_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 2, 2, 2, 6].length) (baseStart_3323932 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3323932 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3323932 prefixEnd_3323932 := by exact prefixLift 3323932
  have htrace : WordTrace (prefixWord ++ tailWord_3323932) baseStart_3323932 baseEnd_3323932 := by
    simpa [prefixWord, tailWord_3323932, baseEnd_3323932] using wordTrace_append hprefix tailTrace_3323932
  have hstable : (prefixWord ++ tailWord_3323932).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3323932).length < 2 ^ (prefixWord ++ tailWord_3323932).sum := by decide
  have hdescent : baseEnd_3323932 < baseStart_3323932 := by decide
  rcases family_descends (prefixWord ++ tailWord_3323932) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3323969 : List Nat := [1, 2, 5, 1, 2, 2, 1, 1, 1, 5, 2]
def baseStart_3323969 : Nat := 118140960795 + 3323969 * 2 ^ 59
def prefixEnd_3323969 : Nat := 4983230072969 + 3 ^ 40 * 3323969 * 2
def baseEnd_3323969 : Nat := 1706793777644810689700851

theorem tailTrace_3323969 : CollatzResearch.WordTrace tailWord_3323969 prefixEnd_3323969 1706793777644810689700851 := by
  unfold tailWord_3323969
  simp only [CollatzResearch.WordTrace]
  refine ⟨121235109294835476554302961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80823406196556984369535307 121235109294835476554302961)
  ·
    refine ⟨90926331971126607415727221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 121235109294835476554302961 90926331971126607415727221)
    ·
      refine ⟨8524343622293119445224427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 90926331971126607415727221 8524343622293119445224427)
      ·
        refine ⟨12786515433439679167836641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8524343622293119445224427 12786515433439679167836641)
        ·
          refine ⟨9589886575079759375877481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12786515433439679167836641 9589886575079759375877481)
          ·
            refine ⟨7192414931309819531908111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9589886575079759375877481 7192414931309819531908111)
            ·
              refine ⟨10788622396964729297862167, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7192414931309819531908111 10788622396964729297862167)
              ·
                refine ⟨16182933595447093946793251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10788622396964729297862167 16182933595447093946793251)
                ·
                  refine ⟨24274400393170640920189877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16182933595447093946793251 24274400393170640920189877)
                  ·
                    refine ⟨2275725036859747586267801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 24274400393170640920189877 2275725036859747586267801)
                    ·
                      refine ⟨1706793777644810689700851, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2275725036859747586267801 1706793777644810689700851)
                      ·
                        rfl

theorem cell23_3323969_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 2, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 2, 1, 1, 1, 5, 2].length) (baseStart_3323969 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3323969 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3323969 prefixEnd_3323969 := by exact prefixLift 3323969
  have htrace : WordTrace (prefixWord ++ tailWord_3323969) baseStart_3323969 baseEnd_3323969 := by
    simpa [prefixWord, tailWord_3323969, baseEnd_3323969] using wordTrace_append hprefix tailTrace_3323969
  have hstable : (prefixWord ++ tailWord_3323969).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3323969).length < 2 ^ (prefixWord ++ tailWord_3323969).sum := by decide
  have hdescent : baseEnd_3323969 < baseStart_3323969 := by decide
  rcases family_descends (prefixWord ++ tailWord_3323969) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3323975 : List Nat := [1, 1, 4, 1, 3, 1, 1, 4, 1, 6]
def baseStart_3323975 : Nat := 118140960795 + 3323975 * 2 ^ 59
def prefixEnd_3323975 : Nat := 4983230072969 + 3 ^ 40 * 3323975 * 2
def baseEnd_3323975 : Nat := 568932286176245888741941

theorem tailTrace_3323975 : CollatzResearch.WordTrace tailWord_3323975 prefixEnd_3323975 568932286176245888741941 := by
  unfold tailWord_3323975
  simp only [CollatzResearch.WordTrace]
  refine ⟨121235328132813739579021379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80823552088542493052680919 121235328132813739579021379)
  ·
    refine ⟨181852992199220609368532069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121235328132813739579021379 181852992199220609368532069)
    ·
      refine ⟨34097436037353864256599763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 181852992199220609368532069 34097436037353864256599763)
      ·
        refine ⟨51146154056030796384899645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34097436037353864256599763 51146154056030796384899645)
        ·
          refine ⟨19179807771011548644337367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 51146154056030796384899645 19179807771011548644337367)
          ·
            refine ⟨28769711656517322966506051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19179807771011548644337367 28769711656517322966506051)
            ·
              refine ⟨43154567484775984449759077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28769711656517322966506051 43154567484775984449759077)
              ·
                refine ⟨8091481403395497084329827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 43154567484775984449759077 8091481403395497084329827)
                ·
                  refine ⟨12137222105093245626494741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8091481403395497084329827 12137222105093245626494741)
                  ·
                    refine ⟨568932286176245888741941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 12137222105093245626494741 568932286176245888741941)
                    ·
                      rfl

theorem cell23_3323975_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 1, 4, 1, 6].length) (baseStart_3323975 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3323975 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3323975 prefixEnd_3323975 := by exact prefixLift 3323975
  have htrace : WordTrace (prefixWord ++ tailWord_3323975) baseStart_3323975 baseEnd_3323975 := by
    simpa [prefixWord, tailWord_3323975, baseEnd_3323975] using wordTrace_append hprefix tailTrace_3323975
  have hstable : (prefixWord ++ tailWord_3323975).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3323975).length < 2 ^ (prefixWord ++ tailWord_3323975).sum := by decide
  have hdescent : baseEnd_3323975 < baseStart_3323975 := by decide
  rcases family_descends (prefixWord ++ tailWord_3323975) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3323985 : List Nat := [1, 2, 2, 1, 3, 1, 1, 5, 1, 1, 5]
def baseStart_3323985 : Nat := 118140960795 + 3323985 * 2 ^ 59
def prefixEnd_3323985 : Nat := 4983230072969 + 3 ^ 40 * 3323985 * 2
def baseEnd_3323985 : Nat := 1706801993335282627100777

theorem tailTrace_3323985 : CollatzResearch.WordTrace tailWord_3323985 prefixEnd_3323985 1706801993335282627100777 := by
  unfold tailWord_3323985
  simp only [CollatzResearch.WordTrace]
  refine ⟨121235692862777511286885409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80823795241851674191256939 121235692862777511286885409)
  ·
    refine ⟨90926769647083133465164057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 121235692862777511286885409 90926769647083133465164057)
    ·
      refine ⟨68195077235312350098873043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 90926769647083133465164057 68195077235312350098873043)
      ·
        refine ⟨102292615852968525148309565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68195077235312350098873043 102292615852968525148309565)
        ·
          refine ⟨38359730944863196930616087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 102292615852968525148309565 38359730944863196930616087)
          ·
            refine ⟨57539596417294795395924131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38359730944863196930616087 57539596417294795395924131)
            ·
              refine ⟨86309394625942193093886197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 57539596417294795395924131 86309394625942193093886197)
              ·
                refine ⟨8091505746182080602551831, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 86309394625942193093886197 8091505746182080602551831)
                ·
                  refine ⟨12137258619273120903827747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8091505746182080602551831 12137258619273120903827747)
                  ·
                    refine ⟨18205887928909681355741621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12137258619273120903827747 18205887928909681355741621)
                    ·
                      refine ⟨1706801993335282627100777, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 18205887928909681355741621 1706801993335282627100777)
                      ·
                        rfl

theorem cell23_3323985_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 1, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 1, 5, 1, 1, 5].length) (baseStart_3323985 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3323985 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3323985 prefixEnd_3323985 := by exact prefixLift 3323985
  have htrace : WordTrace (prefixWord ++ tailWord_3323985) baseStart_3323985 baseEnd_3323985 := by
    simpa [prefixWord, tailWord_3323985, baseEnd_3323985] using wordTrace_append hprefix tailTrace_3323985
  have hstable : (prefixWord ++ tailWord_3323985).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3323985).length < 2 ^ (prefixWord ++ tailWord_3323985).sum := by decide
  have hdescent : baseEnd_3323985 < baseStart_3323985 := by decide
  rcases family_descends (prefixWord ++ tailWord_3323985) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3323992 : List Nat := [2, 1, 2, 2, 1, 5, 1, 1, 4, 4]
def baseStart_3323992 : Nat := 118140960795 + 3323992 * 2 ^ 59
def prefixEnd_3323992 : Nat := 4983230072969 + 3 ^ 40 * 3323992 * 2
def baseEnd_3323992 : Nat := 568935195899954699904415

theorem tailTrace_3323992 : CollatzResearch.WordTrace tailWord_3323992 prefixEnd_3323992 568935195899954699904415 := by
  unfold tailWord_3323992
  simp only [CollatzResearch.WordTrace]
  refine ⟨60617974086876075741195115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80823965449168100988260153 60617974086876075741195115)
  ·
    refine ⟨90926961130314113611792673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60617974086876075741195115 90926961130314113611792673)
    ·
      refine ⟨68195220847735585208844505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 90926961130314113611792673 68195220847735585208844505)
      ·
        refine ⟨51146415635801688906633379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 68195220847735585208844505 51146415635801688906633379)
        ·
          refine ⟨76719623453702533359950069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51146415635801688906633379 76719623453702533359950069)
          ·
            refine ⟨7192464698784612502495319, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 76719623453702533359950069 7192464698784612502495319)
            ·
              refine ⟨10788697048176918753742979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7192464698784612502495319 10788697048176918753742979)
              ·
                refine ⟨16183045572265378130614469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10788697048176918753742979 16183045572265378130614469)
                ·
                  refine ⟨3034321044799758399490213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 16183045572265378130614469 3034321044799758399490213)
                  ·
                    refine ⟨568935195899954699904415, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3034321044799758399490213 568935195899954699904415)
                    ·
                      rfl

theorem cell23_3323992_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 5, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 5, 1, 1, 4, 4].length) (baseStart_3323992 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3323992 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3323992 prefixEnd_3323992 := by exact prefixLift 3323992
  have htrace : WordTrace (prefixWord ++ tailWord_3323992) baseStart_3323992 baseEnd_3323992 := by
    simpa [prefixWord, tailWord_3323992, baseEnd_3323992] using wordTrace_append hprefix tailTrace_3323992
  have hstable : (prefixWord ++ tailWord_3323992).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3323992).length < 2 ^ (prefixWord ++ tailWord_3323992).sum := by decide
  have hdescent : baseEnd_3323992 < baseStart_3323992 := by decide
  rcases family_descends (prefixWord ++ tailWord_3323992) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3324009 : List Nat := [1, 2, 1, 1, 1, 5, 5, 1, 2, 4]
def baseStart_3324009 : Nat := 118140960795 + 3324009 * 2 ^ 59
def prefixEnd_3324009 : Nat := 4983230072969 + 3 ^ 40 * 3324009 * 2
def baseEnd_3324009 : Nat := 568938105623663511066889

theorem tailTrace_3324009 : CollatzResearch.WordTrace tailWord_3324009 prefixEnd_3324009 568938105623663511066889 := by
  unfold tailWord_3324009
  simp only [CollatzResearch.WordTrace]
  refine ⟨121236568214690563385759081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80824378809793708923839387 121236568214690563385759081)
  ·
    refine ⟨90927426161017922539319311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 121236568214690563385759081 90927426161017922539319311)
    ·
      refine ⟨136391139241526883808978967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90927426161017922539319311 136391139241526883808978967)
      ·
        refine ⟨204586708862290325713468451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 136391139241526883808978967 204586708862290325713468451)
        ·
          refine ⟨306880063293435488570202677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 204586708862290325713468451 306880063293435488570202677)
          ·
            refine ⟨28770005933759577053456501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 306880063293435488570202677 28770005933759577053456501)
            ·
              refine ⟨2697188056289960348761547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 28770005933759577053456501 2697188056289960348761547)
              ·
                refine ⟨4045782084434940523142321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2697188056289960348761547 4045782084434940523142321)
                ·
                  refine ⟨3034336563326205392356741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4045782084434940523142321 3034336563326205392356741)
                  ·
                    refine ⟨568938105623663511066889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3034336563326205392356741 568938105623663511066889)
                    ·
                      rfl

theorem cell23_3324009_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 5, 1, 2, 4].length) (baseStart_3324009 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3324009 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3324009 prefixEnd_3324009 := by exact prefixLift 3324009
  have htrace : WordTrace (prefixWord ++ tailWord_3324009) baseStart_3324009 baseEnd_3324009 := by
    simpa [prefixWord, tailWord_3324009, baseEnd_3324009] using wordTrace_append hprefix tailTrace_3324009
  have hstable : (prefixWord ++ tailWord_3324009).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3324009).length < 2 ^ (prefixWord ++ tailWord_3324009).sum := by decide
  have hdescent : baseEnd_3324009 < baseStart_3324009 := by decide
  rcases family_descends (prefixWord ++ tailWord_3324009) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3324012 : List Nat := [2, 2, 1, 1, 3, 3, 3, 1, 1, 2, 4]
def baseStart_3324012 : Nat := 118140960795 + 3324012 * 2 ^ 59
def prefixEnd_3324012 : Nat := 4983230072969 + 3 ^ 40 * 3324012 * 2
def baseEnd_3324012 : Nat := 1706815857312954021463153

theorem tailTrace_3324012 : CollatzResearch.WordTrace tailWord_3324012 prefixEnd_3324012 1706815857312954021463153 := by
  unfold tailWord_3324012
  simp only [CollatzResearch.WordTrace]
  refine ⟨60618338816839847449059145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80824451755786463265412193 60618338816839847449059145)
  ·
    refine ⟨45463754112629885586794359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60618338816839847449059145 45463754112629885586794359)
    ·
      refine ⟨68195631168944828380191539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45463754112629885586794359 68195631168944828380191539)
      ·
        refine ⟨102293446753417242570287309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68195631168944828380191539 102293446753417242570287309)
        ·
          refine ⟨38360042532531465963857741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 102293446753417242570287309 38360042532531465963857741)
          ·
            refine ⟨14385015949699299736446653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 38360042532531465963857741 14385015949699299736446653)
            ·
              refine ⟨5394380981137237401167495, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14385015949699299736446653 5394380981137237401167495)
              ·
                refine ⟨8091571471705856101751243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5394380981137237401167495 8091571471705856101751243)
                ·
                  refine ⟨12137357207558784152626865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8091571471705856101751243 12137357207558784152626865)
                  ·
                    refine ⟨9103017905669088114470149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12137357207558784152626865 9103017905669088114470149)
                    ·
                      refine ⟨1706815857312954021463153, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9103017905669088114470149 1706815857312954021463153)
                      ·
                        rfl

theorem cell23_3324012_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 2, 4].length) (baseStart_3324012 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3324012 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3324012 prefixEnd_3324012 := by exact prefixLift 3324012
  have htrace : WordTrace (prefixWord ++ tailWord_3324012) baseStart_3324012 baseEnd_3324012 := by
    simpa [prefixWord, tailWord_3324012, baseEnd_3324012] using wordTrace_append hprefix tailTrace_3324012
  have hstable : (prefixWord ++ tailWord_3324012).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3324012).length < 2 ^ (prefixWord ++ tailWord_3324012).sum := by decide
  have hdescent : baseEnd_3324012 < baseStart_3324012 := by decide
  rcases family_descends (prefixWord ++ tailWord_3324012) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3324022 : List Nat := [5, 1, 1, 2, 1, 3, 1, 9]
def baseStart_3324022 : Nat := 118140960795 + 3324022 * 2 ^ 59
def prefixEnd_3324022 : Nat := 4983230072969 + 3 ^ 40 * 3324022 * 2
def baseEnd_3324022 : Nat := 63215592300722184531041

theorem tailTrace_3324022 : CollatzResearch.WordTrace tailWord_3324022 prefixEnd_3324022 63215592300722184531041 := by
  unfold tailWord_3324022
  simp only [CollatzResearch.WordTrace]
  refine ⟨7577315147727716662873895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 80824694909095644403988213 7577315147727716662873895)
  ·
    refine ⟨11365972721591574994310843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7577315147727716662873895 11365972721591574994310843)
    ·
      refine ⟨17048959082387362491466265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11365972721591574994310843 17048959082387362491466265)
      ·
        refine ⟨12786719311790521868599699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17048959082387362491466265 12786719311790521868599699)
        ·
          refine ⟨19180078967685782802899549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12786719311790521868599699 19180078967685782802899549)
          ·
            refine ⟨7192529612882168551087331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19180078967685782802899549 7192529612882168551087331)
            ·
              refine ⟨10788794419323252826630997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7192529612882168551087331 10788794419323252826630997)
              ·
                refine ⟨63215592300722184531041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 10788794419323252826630997 63215592300722184531041)
                ·
                  rfl

theorem cell23_3324022_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 3, 1, 9].length) (baseStart_3324022 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3324022 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3324022 prefixEnd_3324022 := by exact prefixLift 3324022
  have htrace : WordTrace (prefixWord ++ tailWord_3324022) baseStart_3324022 baseEnd_3324022 := by
    simpa [prefixWord, tailWord_3324022, baseEnd_3324022] using wordTrace_append hprefix tailTrace_3324022
  have hstable : (prefixWord ++ tailWord_3324022).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3324022).length < 2 ^ (prefixWord ++ tailWord_3324022).sum := by decide
  have hdescent : baseEnd_3324022 < baseStart_3324022 := by decide
  rcases family_descends (prefixWord ++ tailWord_3324022) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3324050 : List Nat := [3, 2, 3, 1, 1, 1, 5, 2, 1, 2, 2]
def baseStart_3324050 : Nat := 118140960795 + 3324050 * 2 ^ 59
def prefixEnd_3324050 : Nat := 4983230072969 + 3 ^ 40 * 3324050 * 2
def baseEnd_3324050 : Nat := 1706835369577824872787979

theorem tailTrace_3324050 : CollatzResearch.WordTrace tailWord_3324050 prefixEnd_3324050 1706835369577824872787979 := by
  unfold tailWord_3324050
  simp only [CollatzResearch.WordTrace]
  refine ⟨30309515901885506847000401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 80825375738361351592001069 30309515901885506847000401)
  ·
    refine ⟨22732136926414130135250301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30309515901885506847000401 22732136926414130135250301)
    ·
      refine ⟨8524551347405298800718863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22732136926414130135250301 8524551347405298800718863)
      ·
        refine ⟨12786827021107948201078295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8524551347405298800718863 12786827021107948201078295)
        ·
          refine ⟨19180240531661922301617443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12786827021107948201078295 19180240531661922301617443)
          ·
            refine ⟨28770360797492883452426165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19180240531661922301617443 28770360797492883452426165)
            ·
              refine ⟨2697221324764957823664953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 28770360797492883452426165 2697221324764957823664953)
              ·
                refine ⟨2022915993573718367748715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2697221324764957823664953 2022915993573718367748715)
                ·
                  refine ⟨3034373990360577551623073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2022915993573718367748715 3034373990360577551623073)
                  ·
                    refine ⟨2275780492770433163717305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3034373990360577551623073 2275780492770433163717305)
                    ·
                      refine ⟨1706835369577824872787979, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2275780492770433163717305 1706835369577824872787979)
                      ·
                        rfl

theorem cell23_3324050_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 5, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 5, 2, 1, 2, 2].length) (baseStart_3324050 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3324050 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3324050 prefixEnd_3324050 := by exact prefixLift 3324050
  have htrace : WordTrace (prefixWord ++ tailWord_3324050) baseStart_3324050 baseEnd_3324050 := by
    simpa [prefixWord, tailWord_3324050, baseEnd_3324050] using wordTrace_append hprefix tailTrace_3324050
  have hstable : (prefixWord ++ tailWord_3324050).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3324050).length < 2 ^ (prefixWord ++ tailWord_3324050).sum := by decide
  have hdescent : baseEnd_3324050 < baseStart_3324050 := by decide
  rcases family_descends (prefixWord ++ tailWord_3324050) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3324089 : List Nat := [1, 2, 1, 4, 1, 2, 3, 2, 1, 4, 2]
def baseStart_3324089 : Nat := 118140960795 + 3324089 * 2 ^ 59
def prefixEnd_3324089 : Nat := 4983230072969 + 3 ^ 40 * 3324089 * 2
def baseEnd_3324089 : Nat := 1706855395323350220200299

theorem tailTrace_3324089 : CollatzResearch.WordTrace tailWord_3324089 prefixEnd_3324089 1706855395323350220200299 := by
  unfold tailWord_3324089
  simp only [CollatzResearch.WordTrace]
  refine ⟨121239486054400737048671321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80826324036267158032447547 121239486054400737048671321)
  ·
    refine ⟨90929614540800552786503491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 121239486054400737048671321 90929614540800552786503491)
    ·
      refine ⟨136394421811200829179755237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90929614540800552786503491 136394421811200829179755237)
      ·
        refine ⟨25573954089600155471204107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 136394421811200829179755237 25573954089600155471204107)
        ·
          refine ⟨38360931134400233206806161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25573954089600155471204107 38360931134400233206806161)
          ·
            refine ⟨28770698350800174905104621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38360931134400233206806161 28770698350800174905104621)
            ·
              refine ⟨10789011881550065589414233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28770698350800174905104621 10789011881550065589414233)
              ·
                refine ⟨8091758911162549192060675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10789011881550065589414233 8091758911162549192060675)
                ·
                  refine ⟨12137638366743823788091013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8091758911162549192060675 12137638366743823788091013)
                  ·
                    refine ⟨2275807193764466960267065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 12137638366743823788091013 2275807193764466960267065)
                    ·
                      refine ⟨1706855395323350220200299, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2275807193764466960267065 1706855395323350220200299)
                      ·
                        rfl

theorem cell23_3324089_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 3, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 3, 2, 1, 4, 2].length) (baseStart_3324089 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3324089 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3324089 prefixEnd_3324089 := by exact prefixLift 3324089
  have htrace : WordTrace (prefixWord ++ tailWord_3324089) baseStart_3324089 baseEnd_3324089 := by
    simpa [prefixWord, tailWord_3324089, baseEnd_3324089] using wordTrace_append hprefix tailTrace_3324089
  have hstable : (prefixWord ++ tailWord_3324089).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3324089).length < 2 ^ (prefixWord ++ tailWord_3324089).sum := by decide
  have hdescent : baseEnd_3324089 < baseStart_3324089 := by decide
  rcases family_descends (prefixWord ++ tailWord_3324089) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3324122 : List Nat := [3, 1, 1, 2, 2, 1, 3, 1, 1, 5, 3]
def baseStart_3324122 : Nat := 118140960795 + 3324122 * 2 ^ 59
def prefixEnd_3324122 : Nat := 4983230072969 + 3 ^ 40 * 3324122 * 2
def baseEnd_3324122 : Nat := 1706872340184948591087647

theorem tailTrace_3324122 : CollatzResearch.WordTrace tailWord_3324122 prefixEnd_3324122 1706872340184948591087647 := by
  unfold tailWord_3324122
  simp only [CollatzResearch.WordTrace]
  refine ⟨30310172415820295921155655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 80827126442187455789748413 30310172415820295921155655)
  ·
    refine ⟨45465258623730443881733483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30310172415820295921155655 45465258623730443881733483)
    ·
      refine ⟨68197887935595665822600225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45465258623730443881733483 68197887935595665822600225)
      ·
        refine ⟨51148415951696749366950169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 68197887935595665822600225 51148415951696749366950169)
        ·
          refine ⟨38361311963772562025212627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51148415951696749366950169 38361311963772562025212627)
          ·
            refine ⟨57541967945658843037818941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38361311963772562025212627 57541967945658843037818941)
            ·
              refine ⟨21578237979622066139182103, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 57541967945658843037818941 21578237979622066139182103)
              ·
                refine ⟨32367356969433099208773155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21578237979622066139182103 32367356969433099208773155)
                ·
                  refine ⟨48551035454149648813159733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32367356969433099208773155 48551035454149648813159733)
                  ·
                    refine ⟨4551659573826529576233725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 48551035454149648813159733 4551659573826529576233725)
                    ·
                      refine ⟨1706872340184948591087647, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4551659573826529576233725 1706872340184948591087647)
                      ·
                        rfl

theorem cell23_3324122_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 3, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 3, 1, 1, 5, 3].length) (baseStart_3324122 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3324122 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3324122 prefixEnd_3324122 := by exact prefixLift 3324122
  have htrace : WordTrace (prefixWord ++ tailWord_3324122) baseStart_3324122 baseEnd_3324122 := by
    simpa [prefixWord, tailWord_3324122, baseEnd_3324122] using wordTrace_append hprefix tailTrace_3324122
  have hstable : (prefixWord ++ tailWord_3324122).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3324122).length < 2 ^ (prefixWord ++ tailWord_3324122).sum := by decide
  have hdescent : baseEnd_3324122 < baseStart_3324122 := by decide
  rcases family_descends (prefixWord ++ tailWord_3324122) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3324146 : List Nat := [3, 2, 1, 3, 2, 2, 2, 3, 5]
def baseStart_3324146 : Nat := 118140960795 + 3324146 * 2 ^ 59
def prefixEnd_3324146 : Nat := 4983230072969 + 3 ^ 40 * 3324146 * 2
def baseEnd_3324146 : Nat := 189653851524517388576393

theorem tailTrace_3324146 : CollatzResearch.WordTrace tailWord_3324146 prefixEnd_3324146 189653851524517388576393 := by
  unfold tailWord_3324146
  simp only [CollatzResearch.WordTrace]
  refine ⟨30310391253798558945874073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 80827710010129490522330861 30310391253798558945874073)
  ·
    refine ⟨22732793440348919209405555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30310391253798558945874073 22732793440348919209405555)
    ·
      refine ⟨34099190160523378814108333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22732793440348919209405555 34099190160523378814108333)
      ·
        refine ⟨12787196310196267055290625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 34099190160523378814108333 12787196310196267055290625)
        ·
          refine ⟨9590397232647200291467969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12787196310196267055290625 9590397232647200291467969)
          ·
            refine ⟨7192797924485400218600977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9590397232647200291467969 7192797924485400218600977)
            ·
              refine ⟨5394598443364050163950733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7192797924485400218600977 5394598443364050163950733)
              ·
                refine ⟨2022974416261518811481525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5394598443364050163950733 2022974416261518811481525)
                ·
                  refine ⟨189653851524517388576393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2022974416261518811481525 189653851524517388576393)
                  ·
                    rfl

theorem cell23_3324146_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 2, 2, 3, 5].length) (baseStart_3324146 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3324146 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3324146 prefixEnd_3324146 := by exact prefixLift 3324146
  have htrace : WordTrace (prefixWord ++ tailWord_3324146) baseStart_3324146 baseEnd_3324146 := by
    simpa [prefixWord, tailWord_3324146, baseEnd_3324146] using wordTrace_append hprefix tailTrace_3324146
  have hstable : (prefixWord ++ tailWord_3324146).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3324146).length < 2 ^ (prefixWord ++ tailWord_3324146).sum := by decide
  have hdescent : baseEnd_3324146 < baseStart_3324146 := by decide
  rcases family_descends (prefixWord ++ tailWord_3324146) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3324155 : List Nat := [1, 1, 1, 1, 1, 3, 1, 1, 3, 10]
def baseStart_3324155 : Nat := 118140960795 + 3324155 * 2 ^ 59
def prefixEnd_3324155 : Nat := 4983230072969 + 3 ^ 40 * 3324155 * 2
def baseEnd_3324155 : Nat := 568963095015515653991665

theorem tailTrace_3324155 : CollatzResearch.WordTrace tailWord_3324155 prefixEnd_3324155 568963095015515653991665 := by
  unfold tailWord_3324155
  simp only [CollatzResearch.WordTrace]
  refine ⟨121241893272161630320573919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80827928848107753547049279 121241893272161630320573919)
  ·
    refine ⟨181862839908242445480860879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121241893272161630320573919 181862839908242445480860879)
    ·
      refine ⟨272794259862363668221291319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 181862839908242445480860879 272794259862363668221291319)
      ·
        refine ⟨409191389793545502331936979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 272794259862363668221291319 409191389793545502331936979)
        ·
          refine ⟨613787084690318253497905469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 409191389793545502331936979 613787084690318253497905469)
          ·
            refine ⟨230170156758869345061714551, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 613787084690318253497905469 230170156758869345061714551)
            ·
              refine ⟨345255235138304017592571827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 230170156758869345061714551 345255235138304017592571827)
              ·
                refine ⟨517882852707456026388857741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 345255235138304017592571827 517882852707456026388857741)
                ·
                  refine ⟨194206069765296009895821653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 517882852707456026388857741 194206069765296009895821653)
                  ·
                    refine ⟨568963095015515653991665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 194206069765296009895821653 568963095015515653991665)
                    ·
                      rfl

theorem cell23_3324155_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 1, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 1, 3, 10].length) (baseStart_3324155 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3324155 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3324155 prefixEnd_3324155 := by exact prefixLift 3324155
  have htrace : WordTrace (prefixWord ++ tailWord_3324155) baseStart_3324155 baseEnd_3324155 := by
    simpa [prefixWord, tailWord_3324155, baseEnd_3324155] using wordTrace_append hprefix tailTrace_3324155
  have hstable : (prefixWord ++ tailWord_3324155).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3324155).length < 2 ^ (prefixWord ++ tailWord_3324155).sum := by decide
  have hdescent : baseEnd_3324155 < baseStart_3324155 := by decide
  rcases family_descends (prefixWord ++ tailWord_3324155) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3324223 : List Nat := [1, 1, 2, 2, 4, 1, 5, 2, 1, 4]
def baseStart_3324223 : Nat := 118140960795 + 3324223 * 2 ^ 59
def prefixEnd_3324223 : Nat := 4983230072969 + 3 ^ 40 * 3324223 * 2
def baseEnd_3324223 : Nat := 568974733910350898641561

theorem tailTrace_3324223 : CollatzResearch.WordTrace tailWord_3324223 prefixEnd_3324223 568974733910350898641561 := by
  unfold tailWord_3324223
  simp only [CollatzResearch.WordTrace]
  refine ⟨121244373435915277934049323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80829582290610185289366215 121244373435915277934049323)
  ·
    refine ⟨181866560153872916901073985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121244373435915277934049323 181866560153872916901073985)
    ·
      refine ⟨136399920115404687675805489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 181866560153872916901073985 136399920115404687675805489)
      ·
        refine ⟨102299940086553515756854117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 136399920115404687675805489 102299940086553515756854117)
        ·
          refine ⟨19181238766228784204410147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 102299940086553515756854117 19181238766228784204410147)
          ·
            refine ⟨28771858149343176306615221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19181238766228784204410147 28771858149343176306615221)
            ·
              refine ⟨2697361701500922778745177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 28771858149343176306615221 2697361701500922778745177)
              ·
                refine ⟨2023021276125692084058883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2697361701500922778745177 2023021276125692084058883)
                ·
                  refine ⟨3034531914188538126088325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2023021276125692084058883 3034531914188538126088325)
                  ·
                    refine ⟨568974733910350898641561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3034531914188538126088325 568974733910350898641561)
                    ·
                      rfl

theorem cell23_3324223_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 5, 2, 1, 4].length) (baseStart_3324223 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3324223 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3324223 prefixEnd_3324223 := by exact prefixLift 3324223
  have htrace : WordTrace (prefixWord ++ tailWord_3324223) baseStart_3324223 baseEnd_3324223 := by
    simpa [prefixWord, tailWord_3324223, baseEnd_3324223] using wordTrace_append hprefix tailTrace_3324223
  have hstable : (prefixWord ++ tailWord_3324223).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3324223).length < 2 ^ (prefixWord ++ tailWord_3324223).sum := by decide
  have hdescent : baseEnd_3324223 < baseStart_3324223 := by decide
  rcases family_descends (prefixWord ++ tailWord_3324223) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3324239 : List Nat := [1, 1, 2, 1, 1, 2, 1, 6, 1, 5, 2]
def baseStart_3324239 : Nat := 118140960795 + 3324239 * 2 ^ 59
def prefixEnd_3324239 : Nat := 4983230072969 + 3 ^ 40 * 3324239 * 2
def baseEnd_3324239 : Nat := 1706932417421524633324609

theorem tailTrace_3324239 : CollatzResearch.WordTrace tailWord_3324239 prefixEnd_3324239 1706932417421524633324609 := by
  unfold tailWord_3324239
  simp only [CollatzResearch.WordTrace]
  refine ⟨121244957003857312666631771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80829971335904875111087847 121244957003857312666631771)
  ·
    refine ⟨181867435505785968999947657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121244957003857312666631771 181867435505785968999947657)
    ·
      refine ⟨136400576629339476749960743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 181867435505785968999947657 136400576629339476749960743)
      ·
        refine ⟨204600864944009215124941115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 136400576629339476749960743 204600864944009215124941115)
        ·
          refine ⟨306901297416013822687411673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 204600864944009215124941115 306901297416013822687411673)
          ·
            refine ⟨230175973062010367015558755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 306901297416013822687411673 230175973062010367015558755)
            ·
              refine ⟨345263959593015550523338133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 230175973062010367015558755 345263959593015550523338133)
              ·
                refine ⟨16184248105922603930781475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 345263959593015550523338133 16184248105922603930781475)
                ·
                  refine ⟨24276372158883905896172213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16184248105922603930781475 24276372158883905896172213)
                  ·
                    refine ⟨2275909889895366177766145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 24276372158883905896172213 2275909889895366177766145)
                    ·
                      refine ⟨1706932417421524633324609, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2275909889895366177766145 1706932417421524633324609)
                      ·
                        rfl

theorem cell23_3324239_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 6, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 6, 1, 5, 2].length) (baseStart_3324239 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3324239 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3324239 prefixEnd_3324239 := by exact prefixLift 3324239
  have htrace : WordTrace (prefixWord ++ tailWord_3324239) baseStart_3324239 baseEnd_3324239 := by
    simpa [prefixWord, tailWord_3324239, baseEnd_3324239] using wordTrace_append hprefix tailTrace_3324239
  have hstable : (prefixWord ++ tailWord_3324239).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3324239).length < 2 ^ (prefixWord ++ tailWord_3324239).sum := by decide
  have hdescent : baseEnd_3324239 < baseStart_3324239 := by decide
  rcases family_descends (prefixWord ++ tailWord_3324239) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3324296 : List Nat := [2, 1, 3, 3, 1, 1, 1, 5, 2, 4]
def baseStart_3324296 : Nat := 118140960795 + 3324296 * 2 ^ 59
def prefixEnd_3324296 : Nat := 4983230072969 + 3 ^ 40 * 3324296 * 2
def baseEnd_3324296 : Nat := 568987228606276970103949

theorem tailTrace_3324296 : CollatzResearch.WordTrace tailWord_3324296 prefixEnd_3324296 568987228606276970103949 := by
  unfold tailWord_3324296
  simp only [CollatzResearch.WordTrace]
  refine ⟨60623517982325405700728371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80831357309767207600971161 60623517982325405700728371)
  ·
    refine ⟨90935276973488108551092557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60623517982325405700728371 90935276973488108551092557)
    ·
      refine ⟨34100728865058040706659709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 90935276973488108551092557 34100728865058040706659709)
      ·
        refine ⟨12787773324396765264997391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 34100728865058040706659709 12787773324396765264997391)
        ·
          refine ⟨19181659986595147897496087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12787773324396765264997391 19181659986595147897496087)
          ·
            refine ⟨28772489979892721846244131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19181659986595147897496087 28772489979892721846244131)
            ·
              refine ⟨43158734969839082769366197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28772489979892721846244131 43158734969839082769366197)
              ·
                refine ⟨4046131403422414009628081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 43158734969839082769366197 4046131403422414009628081)
                ·
                  refine ⟨3034598552566810507221061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4046131403422414009628081 3034598552566810507221061)
                  ·
                    refine ⟨568987228606276970103949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3034598552566810507221061 568987228606276970103949)
                    ·
                      rfl

theorem cell23_3324296_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 1, 5, 2, 4].length) (baseStart_3324296 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3324296 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3324296 prefixEnd_3324296 := by exact prefixLift 3324296
  have htrace : WordTrace (prefixWord ++ tailWord_3324296) baseStart_3324296 baseEnd_3324296 := by
    simpa [prefixWord, tailWord_3324296, baseEnd_3324296] using wordTrace_append hprefix tailTrace_3324296
  have hstable : (prefixWord ++ tailWord_3324296).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3324296).length < 2 ^ (prefixWord ++ tailWord_3324296).sum := by decide
  have hdescent : baseEnd_3324296 < baseStart_3324296 := by decide
  rcases family_descends (prefixWord ++ tailWord_3324296) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3324299 : List Nat := [1, 1, 1, 1, 4, 4, 1, 3, 1, 2, 4]
def baseStart_3324299 : Nat := 118140960795 + 3324299 * 2 ^ 59
def prefixEnd_3324299 : Nat := 4983230072969 + 3 ^ 40 * 3324299 * 2
def baseEnd_3324299 : Nat := 1706963226260794398574333

theorem tailTrace_3324299 : CollatzResearch.WordTrace tailWord_3324299 prefixEnd_3324299 1706963226260794398574333 := by
  unfold tailWord_3324299
  simp only [CollatzResearch.WordTrace]
  refine ⟨121247145383639942913815951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80831430255759961942543967 121247145383639942913815951)
  ·
    refine ⟨181870718075459914370723927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121247145383639942913815951 181870718075459914370723927)
    ·
      refine ⟨272806077113189871556085891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 181870718075459914370723927 272806077113189871556085891)
      ·
        refine ⟨409209115669784807334128837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 272806077113189871556085891 409209115669784807334128837)
        ·
          refine ⟨76726709188084651375149157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 409209115669784807334128837 76726709188084651375149157)
          ·
            refine ⟨14386257972765872132840467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 76726709188084651375149157 14386257972765872132840467)
            ·
              refine ⟨21579386959148808199260701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14386257972765872132840467 21579386959148808199260701)
              ·
                refine ⟨8092270109680803074722763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21579386959148808199260701 8092270109680803074722763)
                ·
                  refine ⟨12138405164521204612084145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8092270109680803074722763 12138405164521204612084145)
                  ·
                    refine ⟨9103803873390903459063109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12138405164521204612084145 9103803873390903459063109)
                    ·
                      refine ⟨1706963226260794398574333, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9103803873390903459063109 1706963226260794398574333)
                      ·
                        rfl

theorem cell23_3324299_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 4, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 4, 1, 3, 1, 2, 4].length) (baseStart_3324299 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3324299 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3324299 prefixEnd_3324299 := by exact prefixLift 3324299
  have htrace : WordTrace (prefixWord ++ tailWord_3324299) baseStart_3324299 baseEnd_3324299 := by
    simpa [prefixWord, tailWord_3324299, baseEnd_3324299] using wordTrace_append hprefix tailTrace_3324299
  have hstable : (prefixWord ++ tailWord_3324299).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3324299).length < 2 ^ (prefixWord ++ tailWord_3324299).sum := by decide
  have hdescent : baseEnd_3324299 < baseStart_3324299 := by decide
  rcases family_descends (prefixWord ++ tailWord_3324299) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3324320 : List Nat := [2, 1, 1, 4, 1, 3, 1, 5, 1, 2, 2]
def baseStart_3324320 : Nat := 118140960795 + 3324320 * 2 ^ 59
def prefixEnd_3324320 : Nat := 4983230072969 + 3 ^ 40 * 3324320 * 2
def baseEnd_3324320 : Nat := 1706974009354538816411737

theorem tailTrace_3324320 : CollatzResearch.WordTrace tailWord_3324320 prefixEnd_3324320 1706974009354538816411737 := by
  unfold tailWord_3324320
  simp only [CollatzResearch.WordTrace]
  refine ⟨60623955658281931750165207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80831940877709242333553609 60623955658281931750165207)
  ·
    refine ⟨90935933487422897625247811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60623955658281931750165207 90935933487422897625247811)
    ·
      refine ⟨136403900231134346437871717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90935933487422897625247811 136403900231134346437871717)
      ·
        refine ⟨25575731293337689957100947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 136403900231134346437871717 25575731293337689957100947)
        ·
          refine ⟨38363596940006534935651421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25575731293337689957100947 38363596940006534935651421)
          ·
            refine ⟨14386348852502450600869283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 38363596940006534935651421 14386348852502450600869283)
            ·
              refine ⟨21579523278753675901303925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14386348852502450600869283 21579523278753675901303925)
              ·
                refine ⟨2023080307383157115747243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 21579523278753675901303925 2023080307383157115747243)
                ·
                  refine ⟨3034620461074735673620865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2023080307383157115747243 3034620461074735673620865)
                  ·
                    refine ⟨2275965345806051755215649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3034620461074735673620865 2275965345806051755215649)
                    ·
                      refine ⟨1706974009354538816411737, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2275965345806051755215649 1706974009354538816411737)
                      ·
                        rfl

theorem cell23_3324320_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 3, 1, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 3, 1, 5, 1, 2, 2].length) (baseStart_3324320 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3324320 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3324320 prefixEnd_3324320 := by exact prefixLift 3324320
  have htrace : WordTrace (prefixWord ++ tailWord_3324320) baseStart_3324320 baseEnd_3324320 := by
    simpa [prefixWord, tailWord_3324320, baseEnd_3324320] using wordTrace_append hprefix tailTrace_3324320
  have hstable : (prefixWord ++ tailWord_3324320).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3324320).length < 2 ^ (prefixWord ++ tailWord_3324320).sum := by decide
  have hdescent : baseEnd_3324320 < baseStart_3324320 := by decide
  rcases family_descends (prefixWord ++ tailWord_3324320) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3324323 : List Nat := [1, 1, 1, 4, 1, 4, 4, 1, 1, 2, 3]
def baseStart_3324323 : Nat := 118140960795 + 3324323 * 2 ^ 59
def prefixEnd_3324323 : Nat := 4983230072969 + 3 ^ 40 * 3324323 * 2
def baseEnd_3324323 : Nat := 1706975549796502304674223

theorem tailTrace_3324323 : CollatzResearch.WordTrace tailWord_3324323 prefixEnd_3324323 1706975549796502304674223 := by
  unfold tailWord_3324323
  simp only [CollatzResearch.WordTrace]
  refine ⟨121248020735552995012689623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80832013823701996675126415 121248020735552995012689623)
  ·
    refine ⟨181872031103329492519034435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121248020735552995012689623 181872031103329492519034435)
    ·
      refine ⟨272808046654994238778551653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 181872031103329492519034435 272808046654994238778551653)
      ·
        refine ⟨51151508747811419770978435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 272808046654994238778551653 51151508747811419770978435)
        ·
          refine ⟨76727263121717129656467653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51151508747811419770978435 76727263121717129656467653)
          ·
            refine ⟨14386361835321961810587685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 76727263121717129656467653 14386361835321961810587685)
            ·
              refine ⟨2697442844122867839485191, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 14386361835321961810587685 2697442844122867839485191)
              ·
                refine ⟨4046164266184301759227787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2697442844122867839485191 4046164266184301759227787)
                ·
                  refine ⟨6069246399276452638841681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4046164266184301759227787 6069246399276452638841681)
                  ·
                    refine ⟨4551934799457339479131261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6069246399276452638841681 4551934799457339479131261)
                    ·
                      refine ⟨1706975549796502304674223, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4551934799457339479131261 1706975549796502304674223)
                      ·
                        rfl

theorem cell23_3324323_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 4, 4, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 4, 4, 1, 1, 2, 3].length) (baseStart_3324323 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3324323 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3324323 prefixEnd_3324323 := by exact prefixLift 3324323
  have htrace : WordTrace (prefixWord ++ tailWord_3324323) baseStart_3324323 baseEnd_3324323 := by
    simpa [prefixWord, tailWord_3324323, baseEnd_3324323] using wordTrace_append hprefix tailTrace_3324323
  have hstable : (prefixWord ++ tailWord_3324323).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3324323).length < 2 ^ (prefixWord ++ tailWord_3324323).sum := by decide
  have hdescent : baseEnd_3324323 < baseStart_3324323 := by decide
  rcases family_descends (prefixWord ++ tailWord_3324323) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3324340 : List Nat := [2, 5, 2, 2, 1, 1, 1, 2, 1, 1, 5]
def baseStart_3324340 : Nat := 118140960795 + 3324340 * 2 ^ 59
def prefixEnd_3324340 : Nat := 4983230072969 + 3 ^ 40 * 3324340 * 2
def baseEnd_3324340 : Nat := 1706984278967628738161645

theorem tailTrace_3324340 : CollatzResearch.WordTrace tailWord_3324340 prefixEnd_3324340 1706984278967628738161645 := by
  unfold tailWord_3324340
  simp only [CollatzResearch.WordTrace]
  refine ⟨60624320388245703458029237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80832427184327604610705649 60624320388245703458029237)
  ·
    refine ⟨5683530036398034699190241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 60624320388245703458029237 5683530036398034699190241)
    ·
      refine ⟨4262647527298526024392681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5683530036398034699190241 4262647527298526024392681)
      ·
        refine ⟨3196985645473894518294511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4262647527298526024392681 3196985645473894518294511)
        ·
          refine ⟨4795478468210841777441767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3196985645473894518294511 4795478468210841777441767)
          ·
            refine ⟨7193217702316262666162651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4795478468210841777441767 7193217702316262666162651)
            ·
              refine ⟨10789826553474393999243977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7193217702316262666162651 10789826553474393999243977)
              ·
                refine ⟨8092369915105795499432983, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10789826553474393999243977 8092369915105795499432983)
                ·
                  refine ⟨12138554872658693249149475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8092369915105795499432983 12138554872658693249149475)
                  ·
                    refine ⟨18207832308988039873724213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12138554872658693249149475 18207832308988039873724213)
                    ·
                      refine ⟨1706984278967628738161645, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 18207832308988039873724213 1706984278967628738161645)
                      ·
                        rfl

theorem cell23_3324340_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 2, 1, 1, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 2, 1, 1, 1, 2, 1, 1, 5].length) (baseStart_3324340 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3324340 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3324340 prefixEnd_3324340 := by exact prefixLift 3324340
  have htrace : WordTrace (prefixWord ++ tailWord_3324340) baseStart_3324340 baseEnd_3324340 := by
    simpa [prefixWord, tailWord_3324340, baseEnd_3324340] using wordTrace_append hprefix tailTrace_3324340
  have hstable : (prefixWord ++ tailWord_3324340).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3324340).length < 2 ^ (prefixWord ++ tailWord_3324340).sum := by decide
  have hdescent : baseEnd_3324340 < baseStart_3324340 := by decide
  rcases family_descends (prefixWord ++ tailWord_3324340) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3324346 : List Nat := [3, 1, 1, 1, 2, 1, 1, 3, 5, 3, 2]
def baseStart_3324346 : Nat := 118140960795 + 3324346 * 2 ^ 59
def prefixEnd_3324346 : Nat := 4983230072969 + 3 ^ 40 * 3324346 * 2
def baseEnd_3324346 : Nat := 1706987359851555714686617

theorem tailTrace_3324346 : CollatzResearch.WordTrace tailWord_3324346 prefixEnd_3324346 1706987359851555714686617 := by
  unfold tailWord_3324346
  simp only [CollatzResearch.WordTrace]
  refine ⟨30312214903617417485194223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 80832573076313113293851261 30312214903617417485194223)
  ·
    refine ⟨45468322355426126227791335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30312214903617417485194223 45468322355426126227791335)
    ·
      refine ⟨68202483533139189341687003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45468322355426126227791335 68202483533139189341687003)
      ·
        refine ⟨102303725299708784012530505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68202483533139189341687003 102303725299708784012530505)
        ·
          refine ⟨76727793974781588009397879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 102303725299708784012530505 76727793974781588009397879)
          ·
            refine ⟨115091690962172382014096819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 76727793974781588009397879 115091690962172382014096819)
            ·
              refine ⟨172637536443258573021145229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 115091690962172382014096819 172637536443258573021145229)
              ·
                refine ⟨64739076166221964882929461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 172637536443258573021145229 64739076166221964882929461)
                ·
                  refine ⟨6069288390583309207774637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 64739076166221964882929461 6069288390583309207774637)
                  ·
                    refine ⟨2275983146468740952915489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6069288390583309207774637 2275983146468740952915489)
                    ·
                      refine ⟨1706987359851555714686617, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2275983146468740952915489 1706987359851555714686617)
                      ·
                        rfl

theorem cell23_3324346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 1, 3, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 1, 3, 5, 3, 2].length) (baseStart_3324346 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3324346 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3324346 prefixEnd_3324346 := by exact prefixLift 3324346
  have htrace : WordTrace (prefixWord ++ tailWord_3324346) baseStart_3324346 baseEnd_3324346 := by
    simpa [prefixWord, tailWord_3324346, baseEnd_3324346] using wordTrace_append hprefix tailTrace_3324346
  have hstable : (prefixWord ++ tailWord_3324346).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3324346).length < 2 ^ (prefixWord ++ tailWord_3324346).sum := by decide
  have hdescent : baseEnd_3324346 < baseStart_3324346 := by decide
  rcases family_descends (prefixWord ++ tailWord_3324346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3324376 : List Nat := [2, 1, 2, 2, 2, 1, 1, 3, 3, 4, 2]
def baseStart_3324376 : Nat := 118140960795 + 3324376 * 2 ^ 59
def prefixEnd_3324376 : Nat := 4983230072969 + 3 ^ 40 * 3324376 * 2
def baseEnd_3324376 : Nat := 1707002764271190597311479

theorem tailTrace_3324376 : CollatzResearch.WordTrace tailWord_3324376 prefixEnd_3324376 1707002764271190597311479 := by
  unfold tailWord_3324376
  simp only [CollatzResearch.WordTrace]
  refine ⟨60624976902180492532184491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80833302536240656709579321 60624976902180492532184491)
  ·
    refine ⟨90937465353270738798276737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60624976902180492532184491 90937465353270738798276737)
    ·
      refine ⟨68203099014953054098707553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 90937465353270738798276737 68203099014953054098707553)
      ·
        refine ⟨51152324261214790574030665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 68203099014953054098707553 51152324261214790574030665)
        ·
          refine ⟨38364243195911092930522999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51152324261214790574030665 38364243195911092930522999)
          ·
            refine ⟨57546364793866639395784499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38364243195911092930522999 57546364793866639395784499)
            ·
              refine ⟨86319547190799959093676749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 57546364793866639395784499 86319547190799959093676749)
              ·
                refine ⟨32369830196549984660128781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 86319547190799959093676749 32369830196549984660128781)
                ·
                  refine ⟨12138686323706244247548293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 32369830196549984660128781 12138686323706244247548293)
                  ·
                    refine ⟨2276003685694920796415305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 12138686323706244247548293 2276003685694920796415305)
                    ·
                      refine ⟨1707002764271190597311479, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2276003685694920796415305 1707002764271190597311479)
                      ·
                        rfl

theorem cell23_3324376_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 1, 3, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 1, 3, 3, 4, 2].length) (baseStart_3324376 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3324376 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3324376 prefixEnd_3324376 := by exact prefixLift 3324376
  have htrace : WordTrace (prefixWord ++ tailWord_3324376) baseStart_3324376 baseEnd_3324376 := by
    simpa [prefixWord, tailWord_3324376, baseEnd_3324376] using wordTrace_append hprefix tailTrace_3324376
  have hstable : (prefixWord ++ tailWord_3324376).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3324376).length < 2 ^ (prefixWord ++ tailWord_3324376).sum := by decide
  have hdescent : baseEnd_3324376 < baseStart_3324376 := by decide
  rcases family_descends (prefixWord ++ tailWord_3324376) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3324406 : List Nat := [5, 1, 1, 1, 2, 1, 2, 1, 1, 4, 4]
def baseStart_3324406 : Nat := 118140960795 + 3324406 * 2 ^ 59
def prefixEnd_3324406 : Nat := 4983230072969 + 3 ^ 40 * 3324406 * 2
def baseEnd_3324406 : Nat := 1707018168690825479936341

theorem tailTrace_3324406 : CollatzResearch.WordTrace tailWord_3324406 prefixEnd_3324406 1707018168690825479936341 := by
  unfold tailWord_3324406
  simp only [CollatzResearch.WordTrace]
  refine ⟨7578190499640768761747567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 80834031996168200125307381 7578190499640768761747567)
  ·
    refine ⟨11367285749461153142621351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7578190499640768761747567 11367285749461153142621351)
    ·
      refine ⟨17050928624191729713932027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11367285749461153142621351 17050928624191729713932027)
      ·
        refine ⟨25576392936287594570898041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17050928624191729713932027 25576392936287594570898041)
        ·
          refine ⟨19182294702215695928173531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25576392936287594570898041 19182294702215695928173531)
          ·
            refine ⟨28773442053323543892260297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19182294702215695928173531 28773442053323543892260297)
            ·
              refine ⟨21580081539992657919195223, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28773442053323543892260297 21580081539992657919195223)
              ·
                refine ⟨32370122309988986878792835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21580081539992657919195223 32370122309988986878792835)
                ·
                  refine ⟨48555183464983480318189253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32370122309988986878792835 48555183464983480318189253)
                  ·
                    refine ⟨9104096899684402559660485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 48555183464983480318189253 9104096899684402559660485)
                    ·
                      refine ⟨1707018168690825479936341, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9104096899684402559660485 1707018168690825479936341)
                      ·
                        rfl

theorem cell23_3324406_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 2, 1, 1, 4, 4].length) (baseStart_3324406 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3324406 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3324406 prefixEnd_3324406 := by exact prefixLift 3324406
  have htrace : WordTrace (prefixWord ++ tailWord_3324406) baseStart_3324406 baseEnd_3324406 := by
    simpa [prefixWord, tailWord_3324406, baseEnd_3324406] using wordTrace_append hprefix tailTrace_3324406
  have hstable : (prefixWord ++ tailWord_3324406).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3324406).length < 2 ^ (prefixWord ++ tailWord_3324406).sum := by decide
  have hdescent : baseEnd_3324406 < baseStart_3324406 := by decide
  rcases family_descends (prefixWord ++ tailWord_3324406) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3324466 : List Nat := [3, 2, 1, 1, 2, 1, 2, 2, 4, 1, 4]
def baseStart_3324466 : Nat := 118140960795 + 3324466 * 2 ^ 59
def prefixEnd_3324466 : Nat := 4983230072969 + 3 ^ 40 * 3324466 * 2
def baseEnd_3324466 : Nat := 1707048977530095245186065

theorem tailTrace_3324466 : CollatzResearch.WordTrace tailWord_3324466 prefixEnd_3324466 1707048977530095245186065 := by
  unfold tailWord_3324466
  simp only [CollatzResearch.WordTrace]
  refine ⟨30313309093508732608786313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 80835490916023286956763501 30313309093508732608786313)
  ·
    refine ⟨22734981820131549456589735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30313309093508732608786313 22734981820131549456589735)
    ·
      refine ⟨34102472730197324184884603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22734981820131549456589735 34102472730197324184884603)
      ·
        refine ⟨51153709095295986277326905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34102472730197324184884603 51153709095295986277326905)
        ·
          refine ⟨38365281821471989707995179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51153709095295986277326905 38365281821471989707995179)
          ·
            refine ⟨57547922732207984561992769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38365281821471989707995179 57547922732207984561992769)
            ·
              refine ⟨43160942049155988421494577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 57547922732207984561992769 43160942049155988421494577)
              ·
                refine ⟨32370706536866991316120933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 43160942049155988421494577 32370706536866991316120933)
                ·
                  refine ⟨6069507475662560871772675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 32370706536866991316120933 6069507475662560871772675)
                  ·
                    refine ⟨9104261213493841307659013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6069507475662560871772675 9104261213493841307659013)
                    ·
                      refine ⟨1707048977530095245186065, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9104261213493841307659013 1707048977530095245186065)
                      ·
                        rfl

theorem cell23_3324466_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 2, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 2, 2, 4, 1, 4].length) (baseStart_3324466 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3324466 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3324466 prefixEnd_3324466 := by exact prefixLift 3324466
  have htrace : WordTrace (prefixWord ++ tailWord_3324466) baseStart_3324466 baseEnd_3324466 := by
    simpa [prefixWord, tailWord_3324466, baseEnd_3324466] using wordTrace_append hprefix tailTrace_3324466
  have hstable : (prefixWord ++ tailWord_3324466).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3324466).length < 2 ^ (prefixWord ++ tailWord_3324466).sum := by decide
  have hdescent : baseEnd_3324466 < baseStart_3324466 := by decide
  rcases family_descends (prefixWord ++ tailWord_3324466) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3324484 : List Nat := [2, 3, 5, 1, 1, 1, 2, 3, 5]
def baseStart_3324484 : Nat := 118140960795 + 3324484 * 2 ^ 59
def prefixEnd_3324484 : Nat := 4983230072969 + 3 ^ 40 * 3324484 * 2
def baseEnd_3324484 : Nat := 189673135575764019417887

theorem tailTrace_3324484 : CollatzResearch.WordTrace tailWord_3324484 prefixEnd_3324484 189673135575764019417887 := by
  unfold tailWord_3324484
  simp only [CollatzResearch.WordTrace]
  refine ⟨60626946443984859754650253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80835928591979813006200337 60626946443984859754650253)
  ·
    refine ⟨22735104916494322407993845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 60626946443984859754650253 22735104916494322407993845)
    ·
      refine ⟨2131416085921342725749423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 22735104916494322407993845 2131416085921342725749423)
      ·
        refine ⟨3197124128882014088624135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2131416085921342725749423 3197124128882014088624135)
        ·
          refine ⟨4795686193323021132936203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3197124128882014088624135 4795686193323021132936203)
          ·
            refine ⟨7193529289984531699404305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4795686193323021132936203 7193529289984531699404305)
            ·
              refine ⟨5395146967488398774553229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7193529289984531699404305 5395146967488398774553229)
              ·
                refine ⟨2023180112808149540457461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5395146967488398774553229 2023180112808149540457461)
                ·
                  refine ⟨189673135575764019417887, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2023180112808149540457461 189673135575764019417887)
                  ·
                    rfl

theorem cell23_3324484_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 5, 1, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 5, 1, 1, 1, 2, 3, 5].length) (baseStart_3324484 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3324484 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3324484 prefixEnd_3324484 := by exact prefixLift 3324484
  have htrace : WordTrace (prefixWord ++ tailWord_3324484) baseStart_3324484 baseEnd_3324484 := by
    simpa [prefixWord, tailWord_3324484, baseEnd_3324484] using wordTrace_append hprefix tailTrace_3324484
  have hstable : (prefixWord ++ tailWord_3324484).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3324484).length < 2 ^ (prefixWord ++ tailWord_3324484).sum := by decide
  have hdescent : baseEnd_3324484 < baseStart_3324484 := by decide
  rcases family_descends (prefixWord ++ tailWord_3324484) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3324653 : List Nat := [1, 5, 1, 2, 1, 1, 2, 1, 2, 2, 5]
def baseStart_3324653 : Nat := 118140960795 + 3324653 * 2 ^ 59
def prefixEnd_3324653 : Nat := 4983230072969 + 3 ^ 40 * 3324653 * 2
def baseEnd_3324653 : Nat := 1707144998412486013547705

theorem tailTrace_3324653 : CollatzResearch.WordTrace tailWord_3324653 prefixEnd_3324653 1707144998412486013547705 := by
  unfold tailWord_3324653
  simp only [CollatzResearch.WordTrace]
  refine ⟨121260056824357461372202613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80840037882904974248135075 121260056824357461372202613)
  ·
    refine ⟨11368130327283512003643995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 121260056824357461372202613 11368130327283512003643995)
    ·
      refine ⟨17052195490925268005465993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11368130327283512003643995 17052195490925268005465993)
      ·
        refine ⟨12789146618193951004099495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17052195490925268005465993 12789146618193951004099495)
        ·
          refine ⟨19183719927290926506149243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12789146618193951004099495 19183719927290926506149243)
          ·
            refine ⟨28775579890936389759223865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19183719927290926506149243 28775579890936389759223865)
            ·
              refine ⟨21581684918202292319417899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28775579890936389759223865 21581684918202292319417899)
              ·
                refine ⟨32372527377303438479126849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21581684918202292319417899 32372527377303438479126849)
                ·
                  refine ⟨24279395532977578859345137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32372527377303438479126849 24279395532977578859345137)
                  ·
                    refine ⟨18209546649733184144508853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 24279395532977578859345137 18209546649733184144508853)
                    ·
                      refine ⟨1707144998412486013547705, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 18209546649733184144508853 1707144998412486013547705)
                      ·
                        rfl

theorem cell23_3324653_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 2, 1, 2, 2, 5].length) (baseStart_3324653 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3324653 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3324653 prefixEnd_3324653 := by exact prefixLift 3324653
  have htrace : WordTrace (prefixWord ++ tailWord_3324653) baseStart_3324653 baseEnd_3324653 := by
    simpa [prefixWord, tailWord_3324653, baseEnd_3324653] using wordTrace_append hprefix tailTrace_3324653
  have hstable : (prefixWord ++ tailWord_3324653).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3324653).length < 2 ^ (prefixWord ++ tailWord_3324653).sum := by decide
  have hdescent : baseEnd_3324653 < baseStart_3324653 := by decide
  rcases family_descends (prefixWord ++ tailWord_3324653) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3324656 : List Nat := [2, 1, 1, 1, 3, 1, 3, 2, 1, 8]
def baseStart_3324656 : Nat := 118140960795 + 3324656 * 2 ^ 59
def prefixEnd_3324656 : Nat := 4983230072969 + 3 ^ 40 * 3324656 * 2
def baseEnd_3324656 : Nat := 569048846284816500603397

theorem tailTrace_3324656 : CollatzResearch.WordTrace tailWord_3324656 prefixEnd_3324656 569048846284816500603397 := by
  unfold tailWord_3324656
  simp only [CollatzResearch.WordTrace]
  refine ⟨60630083121673296442280911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80840110828897728589707881 60630083121673296442280911)
  ·
    refine ⟨90945124682509944663421367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60630083121673296442280911 90945124682509944663421367)
    ·
      refine ⟨136417687023764916995132051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90945124682509944663421367 136417687023764916995132051)
      ·
        refine ⟨204626530535647375492698077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 136417687023764916995132051 204626530535647375492698077)
        ·
          refine ⟨76734948950867765809761779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 204626530535647375492698077 76734948950867765809761779)
          ·
            refine ⟨115102423426301648714642669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 76734948950867765809761779 115102423426301648714642669)
            ·
              refine ⟨43163408784863118267991001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 115102423426301648714642669 43163408784863118267991001)
              ·
                refine ⟨32372556588647338700993251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 43163408784863118267991001 32372556588647338700993251)
                ·
                  refine ⟨48558834882971008051489877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32372556588647338700993251 48558834882971008051489877)
                  ·
                    refine ⟨569048846284816500603397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 48558834882971008051489877 569048846284816500603397)
                    ·
                      rfl

theorem cell23_3324656_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 3, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 3, 2, 1, 8].length) (baseStart_3324656 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3324656 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3324656 prefixEnd_3324656 := by exact prefixLift 3324656
  have htrace : WordTrace (prefixWord ++ tailWord_3324656) baseStart_3324656 baseEnd_3324656 := by
    simpa [prefixWord, tailWord_3324656, baseEnd_3324656] using wordTrace_append hprefix tailTrace_3324656
  have hstable : (prefixWord ++ tailWord_3324656).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3324656).length < 2 ^ (prefixWord ++ tailWord_3324656).sum := by decide
  have hdescent : baseEnd_3324656 < baseStart_3324656 := by decide
  rcases family_descends (prefixWord ++ tailWord_3324656) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3324661 : List Nat := [1, 3, 6, 1, 1, 1, 1, 3, 1, 2, 3]
def baseStart_3324661 : Nat := 118140960795 + 3324661 * 2 ^ 59
def prefixEnd_3324661 : Nat := 4983230072969 + 3 ^ 40 * 3324661 * 2
def baseEnd_3324661 : Nat := 1707149106257721982247669

theorem tailTrace_3324661 : CollatzResearch.WordTrace tailWord_3324661 prefixEnd_3324661 1707149106257721982247669 := by
  unfold tailWord_3324661
  simp only [CollatzResearch.WordTrace]
  refine ⟨121260348608328478738493837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80840232405552319158995891 121260348608328478738493837)
  ·
    refine ⟨45472630728123179526935189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 121260348608328478738493837 45472630728123179526935189)
    ·
      refine ⟨2131529565380774040325087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 45472630728123179526935189 2131529565380774040325087)
      ·
        refine ⟨3197294348071161060487631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2131529565380774040325087 3197294348071161060487631)
        ·
          refine ⟨4795941522106741590731447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3197294348071161060487631 4795941522106741590731447)
          ·
            refine ⟨7193912283160112386097171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4795941522106741590731447 7193912283160112386097171)
            ·
              refine ⟨10790868424740168579145757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7193912283160112386097171 10790868424740168579145757)
              ·
                refine ⟨4046575659277563217179659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10790868424740168579145757 4046575659277563217179659)
                ·
                  refine ⟨6069863488916344825769489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4046575659277563217179659 6069863488916344825769489)
                  ·
                    refine ⟨4552397616687258619327117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6069863488916344825769489 4552397616687258619327117)
                    ·
                      refine ⟨1707149106257721982247669, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4552397616687258619327117 1707149106257721982247669)
                      ·
                        rfl

theorem cell23_3324661_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 6, 1, 1, 1, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 6, 1, 1, 1, 1, 3, 1, 2, 3].length) (baseStart_3324661 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3324661 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3324661 prefixEnd_3324661 := by exact prefixLift 3324661
  have htrace : WordTrace (prefixWord ++ tailWord_3324661) baseStart_3324661 baseEnd_3324661 := by
    simpa [prefixWord, tailWord_3324661, baseEnd_3324661] using wordTrace_append hprefix tailTrace_3324661
  have hstable : (prefixWord ++ tailWord_3324661).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3324661).length < 2 ^ (prefixWord ++ tailWord_3324661).sum := by decide
  have hdescent : baseEnd_3324661 < baseStart_3324661 := by decide
  rcases family_descends (prefixWord ++ tailWord_3324661) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3324674 : List Nat := [3, 4, 1, 1, 1, 2, 3, 2, 2, 1, 3]
def baseStart_3324674 : Nat := 118140960795 + 3324674 * 2 ^ 59
def prefixEnd_3324674 : Nat := 4983230072969 + 3 ^ 40 * 3324674 * 2
def baseEnd_3324674 : Nat := 1707155781506230431385109

theorem tailTrace_3324674 : CollatzResearch.WordTrace tailWord_3324674 prefixEnd_3324674 1707155781506230431385109 := by
  unfold tailWord_3324674
  simp only [CollatzResearch.WordTrace]
  refine ⟨30315205689320345489679269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 80840548504854254639144717 30315205689320345489679269)
  ·
    refine ⟨5684101066747564779314863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 30315205689320345489679269 5684101066747564779314863)
    ·
      refine ⟨8526151600121347168972295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5684101066747564779314863 8526151600121347168972295)
      ·
        refine ⟨12789227400182020753458443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8526151600121347168972295 12789227400182020753458443)
        ·
          refine ⟨19183841100273031130187665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12789227400182020753458443 19183841100273031130187665)
          ·
            refine ⟨14387880825204773347640749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19183841100273031130187665 14387880825204773347640749)
            ·
              refine ⟨5395455309451790005365281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14387880825204773347640749 5395455309451790005365281)
              ·
                refine ⟨4046591482088842504023961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5395455309451790005365281 4046591482088842504023961)
                ·
                  refine ⟨3034943611566631878017971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4046591482088842504023961 3034943611566631878017971)
                  ·
                    refine ⟨4552415417349947817026957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3034943611566631878017971 4552415417349947817026957)
                    ·
                      refine ⟨1707155781506230431385109, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4552415417349947817026957 1707155781506230431385109)
                      ·
                        rfl

theorem cell23_3324674_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 2, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 2, 3, 2, 2, 1, 3].length) (baseStart_3324674 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3324674 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3324674 prefixEnd_3324674 := by exact prefixLift 3324674
  have htrace : WordTrace (prefixWord ++ tailWord_3324674) baseStart_3324674 baseEnd_3324674 := by
    simpa [prefixWord, tailWord_3324674, baseEnd_3324674] using wordTrace_append hprefix tailTrace_3324674
  have hstable : (prefixWord ++ tailWord_3324674).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3324674).length < 2 ^ (prefixWord ++ tailWord_3324674).sum := by decide
  have hdescent : baseEnd_3324674 < baseStart_3324674 := by decide
  rcases family_descends (prefixWord ++ tailWord_3324674) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3324693 : List Nat := [1, 3, 2, 1, 2, 2, 1, 3, 2, 2, 4]
def baseStart_3324693 : Nat := 118140960795 + 3324693 * 2 ^ 59
def prefixEnd_3324693 : Nat := 4983230072969 + 3 ^ 40 * 3324693 * 2
def baseEnd_3324693 : Nat := 1707165537638665857047521

theorem tailTrace_3324693 : CollatzResearch.WordTrace tailWord_3324693 prefixEnd_3324693 1707165537638665857047521 := by
  unfold tailWord_3324693
  simp only [CollatzResearch.WordTrace]
  refine ⟨121261515744212548203658733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80841010496141698802439155 121261515744212548203658733)
  ·
    refine ⟨45473068404079705576372025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 121261515744212548203658733 45473068404079705576372025)
    ·
      refine ⟨34104801303059779182279019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45473068404079705576372025 34104801303059779182279019)
      ·
        refine ⟨51157201954589668773418529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34104801303059779182279019 51157201954589668773418529)
        ·
          refine ⟨38367901465942251580063897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51157201954589668773418529 38367901465942251580063897)
          ·
            refine ⟨28775926099456688685047923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38367901465942251580063897 28775926099456688685047923)
            ·
              refine ⟨43163889149185033027571885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28775926099456688685047923 43163889149185033027571885)
              ·
                refine ⟨16186458430944387385339457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 43163889149185033027571885 16186458430944387385339457)
                ·
                  refine ⟨12139843823208290539004593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16186458430944387385339457 12139843823208290539004593)
                  ·
                    refine ⟨9104882867406217904253445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12139843823208290539004593 9104882867406217904253445)
                    ·
                      refine ⟨1707165537638665857047521, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9104882867406217904253445 1707165537638665857047521)
                      ·
                        rfl

theorem cell23_3324693_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 1, 3, 2, 2, 4].length) (baseStart_3324693 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3324693 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3324693 prefixEnd_3324693 := by exact prefixLift 3324693
  have htrace : WordTrace (prefixWord ++ tailWord_3324693) baseStart_3324693 baseEnd_3324693 := by
    simpa [prefixWord, tailWord_3324693, baseEnd_3324693] using wordTrace_append hprefix tailTrace_3324693
  have hstable : (prefixWord ++ tailWord_3324693).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3324693).length < 2 ^ (prefixWord ++ tailWord_3324693).sum := by decide
  have hdescent : baseEnd_3324693 < baseStart_3324693 := by decide
  rcases family_descends (prefixWord ++ tailWord_3324693) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3324701 : List Nat := [1, 4, 2, 4, 1, 1, 2, 2, 1, 3, 2]
def baseStart_3324701 : Nat := 118140960795 + 3324701 * 2 ^ 59
def prefixEnd_3324701 : Nat := 4983230072969 + 3 ^ 40 * 3324701 * 2
def baseEnd_3324701 : Nat := 1707169645483901825747485

theorem tailTrace_3324701 : CollatzResearch.WordTrace tailWord_3324701 prefixEnd_3324701 1707169645483901825747485 := by
  unfold tailWord_3324701
  simp only [CollatzResearch.WordTrace]
  refine ⟨121261807528183565569949957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80841205018789043713299971 121261807528183565569949957)
  ·
    refine ⟨22736588911534418544365617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 121261807528183565569949957 22736588911534418544365617)
    ·
      refine ⟨17052441683650813908274213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22736588911534418544365617 17052441683650813908274213)
      ·
        refine ⟨3197332815684527607801415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 17052441683650813908274213 3197332815684527607801415)
        ·
          refine ⟨4795999223526791411702123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3197332815684527607801415 4795999223526791411702123)
          ·
            refine ⟨7193998835290187117553185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4795999223526791411702123 7193998835290187117553185)
            ·
              refine ⟨5395499126467640338164889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7193998835290187117553185 5395499126467640338164889)
              ·
                refine ⟨4046624344850730253623667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5395499126467640338164889 4046624344850730253623667)
                ·
                  refine ⟨6069936517276095380435501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4046624344850730253623667 6069936517276095380435501)
                  ·
                    refine ⟨2276226193978535767663313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6069936517276095380435501 2276226193978535767663313)
                    ·
                      refine ⟨1707169645483901825747485, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2276226193978535767663313 1707169645483901825747485)
                      ·
                        rfl

theorem cell23_3324701_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 4, 1, 1, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 4, 1, 1, 2, 2, 1, 3, 2].length) (baseStart_3324701 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3324701 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3324701 prefixEnd_3324701 := by exact prefixLift 3324701
  have htrace : WordTrace (prefixWord ++ tailWord_3324701) baseStart_3324701 baseEnd_3324701 := by
    simpa [prefixWord, tailWord_3324701, baseEnd_3324701] using wordTrace_append hprefix tailTrace_3324701
  have hstable : (prefixWord ++ tailWord_3324701).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3324701).length < 2 ^ (prefixWord ++ tailWord_3324701).sum := by decide
  have hdescent : baseEnd_3324701 < baseStart_3324701 := by decide
  rcases family_descends (prefixWord ++ tailWord_3324701) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3324703 : List Nat := [1, 1, 2, 4, 2, 2, 2, 2, 7]
def baseStart_3324703 : Nat := 118140960795 + 3324703 * 2 ^ 59
def prefixEnd_3324703 : Nat := 4983230072969 + 3 ^ 40 * 3324703 * 2
def baseEnd_3324703 : Nat := 189685630271690090880275

theorem tailTrace_3324703 : CollatzResearch.WordTrace tailWord_3324703 prefixEnd_3324703 189685630271690090880275 := by
  unfold tailWord_3324703
  simp only [CollatzResearch.WordTrace]
  refine ⟨121261880474176319911522763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80841253649450879941015175 121261880474176319911522763)
  ·
    refine ⟨181892820711264479867284145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121261880474176319911522763 181892820711264479867284145)
    ·
      refine ⟨136419615533448359900463109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 181892820711264479867284145 136419615533448359900463109)
      ·
        refine ⟨25578677912521567481336833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 136419615533448359900463109 25578677912521567481336833)
        ·
          refine ⟨19184008434391175611002625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25578677912521567481336833 19184008434391175611002625)
          ·
            refine ⟨14388006325793381708251969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19184008434391175611002625 14388006325793381708251969)
            ·
              refine ⟨10791004744345036281188977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14388006325793381708251969 10791004744345036281188977)
              ·
                refine ⟨8093253558258777210891733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10791004744345036281188977 8093253558258777210891733)
                ·
                  refine ⟨189685630271690090880275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 8093253558258777210891733 189685630271690090880275)
                  ·
                    rfl

theorem cell23_3324703_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 2, 2, 2, 7].length) (baseStart_3324703 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3324703 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3324703 prefixEnd_3324703 := by exact prefixLift 3324703
  have htrace : WordTrace (prefixWord ++ tailWord_3324703) baseStart_3324703 baseEnd_3324703 := by
    simpa [prefixWord, tailWord_3324703, baseEnd_3324703] using wordTrace_append hprefix tailTrace_3324703
  have hstable : (prefixWord ++ tailWord_3324703).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3324703).length < 2 ^ (prefixWord ++ tailWord_3324703).sum := by decide
  have hdescent : baseEnd_3324703 < baseStart_3324703 := by decide
  rcases family_descends (prefixWord ++ tailWord_3324703) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3324911 : List Nat := [1, 1, 2, 1, 4, 5, 1, 1, 3, 2, 2]
def baseStart_3324911 : Nat := 118140960795 + 3324911 * 2 ^ 59
def prefixEnd_3324911 : Nat := 4983230072969 + 3 ^ 40 * 3324911 * 2
def baseEnd_3324911 : Nat := 1707277476421346004121519

theorem tailTrace_3324911 : CollatzResearch.WordTrace tailWord_3324911 prefixEnd_3324911 1707277476421346004121519 := by
  unfold tailWord_3324911
  simp only [CollatzResearch.WordTrace]
  refine ⟨121269466857422771435094587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80846311238281847623396391 121269466857422771435094587)
  ·
    refine ⟨181904200286134157152641881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121269466857422771435094587 181904200286134157152641881)
    ·
      refine ⟨136428150214600617864481411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 181904200286134157152641881 136428150214600617864481411)
      ·
        refine ⟨204642225321900926796722117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 136428150214600617864481411 204642225321900926796722117)
        ·
          refine ⟨38370417247856423774385397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 204642225321900926796722117 38370417247856423774385397)
          ·
            refine ⟨3597226616986539728848631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 38370417247856423774385397 3597226616986539728848631)
            ·
              refine ⟨5395839925479809593272947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3597226616986539728848631 5395839925479809593272947)
              ·
                refine ⟨8093759888219714389909421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5395839925479809593272947 8093759888219714389909421)
                ·
                  refine ⟨3035159958082392896216033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8093759888219714389909421 3035159958082392896216033)
                  ·
                    refine ⟨2276369968561794672162025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3035159958082392896216033 2276369968561794672162025)
                    ·
                      refine ⟨1707277476421346004121519, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2276369968561794672162025 1707277476421346004121519)
                      ·
                        rfl

theorem cell23_3324911_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 5, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 5, 1, 1, 3, 2, 2].length) (baseStart_3324911 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3324911 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3324911 prefixEnd_3324911 := by exact prefixLift 3324911
  have htrace : WordTrace (prefixWord ++ tailWord_3324911) baseStart_3324911 baseEnd_3324911 := by
    simpa [prefixWord, tailWord_3324911, baseEnd_3324911] using wordTrace_append hprefix tailTrace_3324911
  have hstable : (prefixWord ++ tailWord_3324911).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3324911).length < 2 ^ (prefixWord ++ tailWord_3324911).sum := by decide
  have hdescent : baseEnd_3324911 < baseStart_3324911 := by decide
  rcases family_descends (prefixWord ++ tailWord_3324911) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3324961 : List Nat := [1, 2, 3, 2, 3, 2, 2, 2, 2, 1, 3]
def baseStart_3324961 : Nat := 118140960795 + 3324961 * 2 ^ 59
def prefixEnd_3324961 : Nat := 4983230072969 + 3 ^ 40 * 3324961 * 2
def baseEnd_3324961 : Nat := 1707303150454070808496289

theorem tailTrace_3324961 : CollatzResearch.WordTrace tailWord_3324961 prefixEnd_3324961 1707303150454070808496289 := by
  unfold tailWord_3324961
  simp only [CollatzResearch.WordTrace]
  refine ⟨121271290507241629974414737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80847527004827753316276491 121271290507241629974414737)
  ·
    refine ⟨90953467880431222480811053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 121271290507241629974414737 90953467880431222480811053)
    ·
      refine ⟨34107550455161708430304145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 90953467880431222480811053 34107550455161708430304145)
      ·
        refine ⟨25580662841371281322728109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34107550455161708430304145 25580662841371281322728109)
        ·
          refine ⟨9592748565514230496023041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25580662841371281322728109 9592748565514230496023041)
          ·
            refine ⟨7194561424135672872017281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9592748565514230496023041 7194561424135672872017281)
            ·
              refine ⟨5395921068101754654012961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7194561424135672872017281 5395921068101754654012961)
              ·
                refine ⟨4046940801076315990509721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5395921068101754654012961 4046940801076315990509721)
                ·
                  refine ⟨3035205600807236992882291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4046940801076315990509721 3035205600807236992882291)
                  ·
                    refine ⟨4552808401210855489323437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3035205600807236992882291 4552808401210855489323437)
                    ·
                      refine ⟨1707303150454070808496289, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4552808401210855489323437 1707303150454070808496289)
                      ·
                        rfl

theorem cell23_3324961_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 2, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 2, 2, 2, 2, 1, 3].length) (baseStart_3324961 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3324961 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3324961 prefixEnd_3324961 := by exact prefixLift 3324961
  have htrace : WordTrace (prefixWord ++ tailWord_3324961) baseStart_3324961 baseEnd_3324961 := by
    simpa [prefixWord, tailWord_3324961, baseEnd_3324961] using wordTrace_append hprefix tailTrace_3324961
  have hstable : (prefixWord ++ tailWord_3324961).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3324961).length < 2 ^ (prefixWord ++ tailWord_3324961).sum := by decide
  have hdescent : baseEnd_3324961 < baseStart_3324961 := by decide
  rcases family_descends (prefixWord ++ tailWord_3324961) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3324984 : List Nat := [2, 1, 2, 1, 5, 1, 1, 3, 1, 4, 2]
def baseStart_3324984 : Nat := 118140960795 + 3324984 * 2 ^ 59
def prefixEnd_3324984 : Nat := 4983230072969 + 3 ^ 40 * 3324984 * 2
def baseEnd_3324984 : Nat := 1707314960509124218508683

theorem tailTrace_3324984 : CollatzResearch.WordTrace tailWord_3324984 prefixEnd_3324984 1707314960509124218508683 := by
  unfold tailWord_3324984
  simp only [CollatzResearch.WordTrace]
  refine ⟨60636064693079152451251003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80848086257438869935001337 60636064693079152451251003)
  ·
    refine ⟨90954097039618728676876505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60636064693079152451251003 90954097039618728676876505)
    ·
      refine ⟨68215572779714046507657379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 90954097039618728676876505 68215572779714046507657379)
      ·
        refine ⟨102323359169571069761486069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68215572779714046507657379 102323359169571069761486069)
        ·
          refine ⟨9592814922147287790139319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 102323359169571069761486069 9592814922147287790139319)
          ·
            refine ⟨14389222383220931685208979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9592814922147287790139319 14389222383220931685208979)
            ·
              refine ⟨21583833574831397527813469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14389222383220931685208979 21583833574831397527813469)
              ·
                refine ⟨8093937590561774072930051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21583833574831397527813469 8093937590561774072930051)
                ·
                  refine ⟨12140906385842661109395077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8093937590561774072930051 12140906385842661109395077)
                  ·
                    refine ⟨2276419947345498958011577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 12140906385842661109395077 2276419947345498958011577)
                    ·
                      refine ⟨1707314960509124218508683, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2276419947345498958011577 1707314960509124218508683)
                      ·
                        rfl

theorem cell23_3324984_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 1, 1, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 1, 1, 3, 1, 4, 2].length) (baseStart_3324984 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3324984 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3324984 prefixEnd_3324984 := by exact prefixLift 3324984
  have htrace : WordTrace (prefixWord ++ tailWord_3324984) baseStart_3324984 baseEnd_3324984 := by
    simpa [prefixWord, tailWord_3324984, baseEnd_3324984] using wordTrace_append hprefix tailTrace_3324984
  have hstable : (prefixWord ++ tailWord_3324984).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3324984).length < 2 ^ (prefixWord ++ tailWord_3324984).sum := by decide
  have hdescent : baseEnd_3324984 < baseStart_3324984 := by decide
  rcases family_descends (prefixWord ++ tailWord_3324984) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3325005 : List Nat := [1, 6, 1, 1, 1, 4, 2, 1, 1, 3, 2]
def baseStart_3325005 : Nat := 118140960795 + 3325005 * 2 ^ 59
def prefixEnd_3325005 : Nat := 4983230072969 + 3 ^ 40 * 3325005 * 2
def baseEnd_3325005 : Nat := 1707325743602868636346087

theorem tailTrace_3325005 : CollatzResearch.WordTrace tailWord_3325005 prefixEnd_3325005 1707325743602868636346087 := by
  unfold tailWord_3325005
  simp only [CollatzResearch.WordTrace]
  refine ⟨121272895319082225489016469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80848596879388150326010979 121272895319082225489016469)
  ·
    refine ⟨5684666968081979319797647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 121272895319082225489016469 5684666968081979319797647)
    ·
      refine ⟨8527000452122968979696471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5684666968081979319797647 8527000452122968979696471)
      ·
        refine ⟨12790500678184453469544707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8527000452122968979696471 12790500678184453469544707)
        ·
          refine ⟨19185751017276680204317061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12790500678184453469544707 19185751017276680204317061)
          ·
            refine ⟨3597328315739377538309449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 19185751017276680204317061 3597328315739377538309449)
            ·
              refine ⟨2697996236804533153732087, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3597328315739377538309449 2697996236804533153732087)
              ·
                refine ⟨4046994355206799730598131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2697996236804533153732087 4046994355206799730598131)
                ·
                  refine ⟨6070491532810199595897197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4046994355206799730598131 6070491532810199595897197)
                  ·
                    refine ⟨2276434324803824848461449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6070491532810199595897197 2276434324803824848461449)
                    ·
                      refine ⟨1707325743602868636346087, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2276434324803824848461449 1707325743602868636346087)
                      ·
                        rfl

theorem cell23_3325005_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 4, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 4, 2, 1, 1, 3, 2].length) (baseStart_3325005 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3325005 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3325005 prefixEnd_3325005 := by exact prefixLift 3325005
  have htrace : WordTrace (prefixWord ++ tailWord_3325005) baseStart_3325005 baseEnd_3325005 := by
    simpa [prefixWord, tailWord_3325005, baseEnd_3325005] using wordTrace_append hprefix tailTrace_3325005
  have hstable : (prefixWord ++ tailWord_3325005).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3325005).length < 2 ^ (prefixWord ++ tailWord_3325005).sum := by decide
  have hdescent : baseEnd_3325005 < baseStart_3325005 := by decide
  rcases family_descends (prefixWord ++ tailWord_3325005) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3325034 : List Nat := [3, 1, 3, 2, 2, 1, 2, 1, 2, 3, 3]
def baseStart_3325034 : Nat := 118140960795 + 3325034 * 2 ^ 59
def prefixEnd_3325034 : Nat := 4983230072969 + 3 ^ 40 * 3325034 * 2
def baseEnd_3325034 : Nat := 1707340634541849022883453

theorem tailTrace_3325034 : CollatzResearch.WordTrace tailWord_3325034 prefixEnd_3325034 1707340634541849022883453 := by
  unfold tailWord_3325034
  simp only [CollatzResearch.WordTrace]
  refine ⟨30318488258994290860455539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 80849302023984775627881437 30318488258994290860455539)
  ·
    refine ⟨45477732388491436290683309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30318488258994290860455539 45477732388491436290683309)
    ·
      refine ⟨17054149645684288609006241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 45477732388491436290683309 17054149645684288609006241)
      ·
        refine ⟨12790612234263216456754681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17054149645684288609006241 12790612234263216456754681)
        ·
          refine ⟨9592959175697412342566011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12790612234263216456754681 9592959175697412342566011)
          ·
            refine ⟨14389438763546118513849017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9592959175697412342566011 14389438763546118513849017)
            ·
              refine ⟨10792079072659588885386763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14389438763546118513849017 10792079072659588885386763)
              ·
                refine ⟨16188118608989383328080145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10792079072659588885386763 16188118608989383328080145)
                ·
                  refine ⟨12141088956742037496060109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16188118608989383328080145 12141088956742037496060109)
                  ·
                    refine ⟨4552908358778264061022541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12141088956742037496060109 4552908358778264061022541)
                    ·
                      refine ⟨1707340634541849022883453, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4552908358778264061022541 1707340634541849022883453)
                      ·
                        rfl

theorem cell23_3325034_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 1, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 1, 2, 1, 2, 3, 3].length) (baseStart_3325034 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3325034 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3325034 prefixEnd_3325034 := by exact prefixLift 3325034
  have htrace : WordTrace (prefixWord ++ tailWord_3325034) baseStart_3325034 baseEnd_3325034 := by
    simpa [prefixWord, tailWord_3325034, baseEnd_3325034] using wordTrace_append hprefix tailTrace_3325034
  have hstable : (prefixWord ++ tailWord_3325034).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3325034).length < 2 ^ (prefixWord ++ tailWord_3325034).sum := by decide
  have hdescent : baseEnd_3325034 < baseStart_3325034 := by decide
  rcases family_descends (prefixWord ++ tailWord_3325034) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3325037 : List Nat := [1, 5, 1, 1, 2, 2, 1, 2, 1, 7]
def baseStart_3325037 : Nat := 118140960795 + 3325037 * 2 ^ 59
def prefixEnd_3325037 : Nat := 4983230072969 + 3 ^ 40 * 3325037 * 2
def baseEnd_3325037 : Nat := 569114058327937503715313

theorem tailTrace_3325037 : CollatzResearch.WordTrace tailWord_3325037 prefixEnd_3325037 569114058327937503715313 := by
  unfold tailWord_3325037
  simp only [CollatzResearch.WordTrace]
  refine ⟨121274062454966294954181365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80849374969977529969454243 121274062454966294954181365)
  ·
    refine ⟨11369443355153090151954503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 121274062454966294954181365 11369443355153090151954503)
    ·
      refine ⟨17054165032729635227931755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11369443355153090151954503 17054165032729635227931755)
      ·
        refine ⟨25581247549094452841897633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17054165032729635227931755 25581247549094452841897633)
        ·
          refine ⟨19185935661820839631423225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25581247549094452841897633 19185935661820839631423225)
          ·
            refine ⟨14389451746365629723567419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19185935661820839631423225 14389451746365629723567419)
            ·
              refine ⟨21584177619548444585351129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14389451746365629723567419 21584177619548444585351129)
              ·
                refine ⟨16188133214661333439013347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21584177619548444585351129 16188133214661333439013347)
                ·
                  refine ⟨24282199821992000158520021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16188133214661333439013347 24282199821992000158520021)
                  ·
                    refine ⟨569114058327937503715313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 24282199821992000158520021 569114058327937503715313)
                    ·
                      rfl

theorem cell23_3325037_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 2, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 2, 1, 2, 1, 7].length) (baseStart_3325037 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3325037 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3325037 prefixEnd_3325037 := by exact prefixLift 3325037
  have htrace : WordTrace (prefixWord ++ tailWord_3325037) baseStart_3325037 baseEnd_3325037 := by
    simpa [prefixWord, tailWord_3325037, baseEnd_3325037] using wordTrace_append hprefix tailTrace_3325037
  have hstable : (prefixWord ++ tailWord_3325037).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3325037).length < 2 ^ (prefixWord ++ tailWord_3325037).sum := by decide
  have hdescent : baseEnd_3325037 < baseStart_3325037 := by decide
  rcases family_descends (prefixWord ++ tailWord_3325037) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3325067 : List Nat := [1, 1, 1, 1, 4, 1, 1, 4, 5, 4]
def baseStart_3325067 : Nat := 118140960795 + 3325067 * 2 ^ 59
def prefixEnd_3325067 : Nat := 4983230072969 + 3 ^ 40 * 3325067 * 2
def baseEnd_3325067 : Nat := 569119193134482464590267

theorem tailTrace_3325067 : CollatzResearch.WordTrace tailWord_3325067 prefixEnd_3325067 569119193134482464590267 := by
  unfold tailWord_3325067
  simp only [CollatzResearch.WordTrace]
  refine ⟨121275156644857610077773455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80850104429905073385182303 121275156644857610077773455)
  ·
    refine ⟨181912734967286415116660183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121275156644857610077773455 181912734967286415116660183)
    ·
      refine ⟨272869102450929622674990275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 181912734967286415116660183 272869102450929622674990275)
      ·
        refine ⟨409303653676394434012485413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 272869102450929622674990275 409303653676394434012485413)
        ·
          refine ⟨76744435064323956377341015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 409303653676394434012485413 76744435064323956377341015)
          ·
            refine ⟨115116652596485934566011523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 76744435064323956377341015 115116652596485934566011523)
            ·
              refine ⟨172674978894728901849017285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 115116652596485934566011523 172674978894728901849017285)
              ·
                refine ⟨32376558542761669096690741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 172674978894728901849017285 32376558542761669096690741)
                ·
                  refine ⟨3035302363383906477814757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 32376558542761669096690741 3035302363383906477814757)
                  ·
                    refine ⟨569119193134482464590267, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3035302363383906477814757 569119193134482464590267)
                    ·
                      rfl

theorem cell23_3325067_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 1, 4, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 1, 4, 5, 4].length) (baseStart_3325067 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3325067 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3325067 prefixEnd_3325067 := by exact prefixLift 3325067
  have htrace : WordTrace (prefixWord ++ tailWord_3325067) baseStart_3325067 baseEnd_3325067 := by
    simpa [prefixWord, tailWord_3325067, baseEnd_3325067] using wordTrace_append hprefix tailTrace_3325067
  have hstable : (prefixWord ++ tailWord_3325067).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3325067).length < 2 ^ (prefixWord ++ tailWord_3325067).sum := by decide
  have hdescent : baseEnd_3325067 < baseStart_3325067 := by decide
  rcases family_descends (prefixWord ++ tailWord_3325067) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3325074 : List Nat := [3, 2, 3, 1, 1, 2, 1, 1, 4, 1, 4]
def baseStart_3325074 : Nat := 118140960795 + 3325074 * 2 ^ 59
def prefixEnd_3325074 : Nat := 4983230072969 + 3 ^ 40 * 3325074 * 2
def baseEnd_3325074 : Nat := 1707361173768028866383269

theorem tailTrace_3325074 : CollatzResearch.WordTrace tailWord_3325074 prefixEnd_3325074 1707361173768028866383269 := by
  unfold tailWord_3325074
  simp only [CollatzResearch.WordTrace]
  refine ⟨30318852988958062568319569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 80850274637221500182185517 30318852988958062568319569)
  ·
    refine ⟨22739139741718546926239677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30318852988958062568319569 22739139741718546926239677)
    ·
      refine ⟨8527177403144455097339879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22739139741718546926239677 8527177403144455097339879)
      ·
        refine ⟨12790766104716682646009819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8527177403144455097339879 12790766104716682646009819)
        ·
          refine ⟨19186149157075023969014729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12790766104716682646009819 19186149157075023969014729)
          ·
            refine ⟨14389611867806267976761047, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19186149157075023969014729 14389611867806267976761047)
            ·
              refine ⟨21584417801709401965141571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14389611867806267976761047 21584417801709401965141571)
              ·
                refine ⟨32376626702564102947712357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21584417801709401965141571 32376626702564102947712357)
                ·
                  refine ⟨6070617506730769302696067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 32376626702564102947712357 6070617506730769302696067)
                  ·
                    refine ⟨9105926260096153954044101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6070617506730769302696067 9105926260096153954044101)
                    ·
                      refine ⟨1707361173768028866383269, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9105926260096153954044101 1707361173768028866383269)
                      ·
                        rfl

theorem cell23_3325074_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 2, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 2, 1, 1, 4, 1, 4].length) (baseStart_3325074 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3325074 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3325074 prefixEnd_3325074 := by exact prefixLift 3325074
  have htrace : WordTrace (prefixWord ++ tailWord_3325074) baseStart_3325074 baseEnd_3325074 := by
    simpa [prefixWord, tailWord_3325074, baseEnd_3325074] using wordTrace_append hprefix tailTrace_3325074
  have hstable : (prefixWord ++ tailWord_3325074).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3325074).length < 2 ^ (prefixWord ++ tailWord_3325074).sum := by decide
  have hdescent : baseEnd_3325074 < baseStart_3325074 := by decide
  rcases family_descends (prefixWord ++ tailWord_3325074) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3325077 : List Nat := [1, 3, 2, 1, 1, 1, 2, 2, 3, 4, 3]
def baseStart_3325077 : Nat := 118140960795 + 3325077 * 2 ^ 59
def prefixEnd_3325077 : Nat := 4983230072969 + 3 ^ 40 * 3325077 * 2
def baseEnd_3325077 : Nat := 1707362714209992354645755

theorem tailTrace_3325077 : CollatzResearch.WordTrace tailWord_3325077 prefixEnd_3325077 1707362714209992354645755 := by
  unfold tailWord_3325077
  simp only [CollatzResearch.WordTrace]
  refine ⟨121275521374821381785637485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80850347583214254523758323 121275521374821381785637485)
  ·
    refine ⟨45478320515558018169614057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 121275521374821381785637485 45478320515558018169614057)
    ·
      refine ⟨34108740386668513627210543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45478320515558018169614057 34108740386668513627210543)
      ·
        refine ⟨51163110580002770440815815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34108740386668513627210543 51163110580002770440815815)
        ·
          refine ⟨76744665870004155661223723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51163110580002770440815815 76744665870004155661223723)
          ·
            refine ⟨115116998805006233491835585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 76744665870004155661223723 115116998805006233491835585)
            ·
              refine ⟨86337749103754675118876689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 115116998805006233491835585 86337749103754675118876689)
              ·
                refine ⟨64753311827816006339157517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 86337749103754675118876689 64753311827816006339157517)
                ·
                  refine ⟨24282491935431002377184069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 64753311827816006339157517 24282491935431002377184069)
                  ·
                    refine ⟨4552967237893312945722013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 24282491935431002377184069 4552967237893312945722013)
                    ·
                      refine ⟨1707362714209992354645755, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4552967237893312945722013 1707362714209992354645755)
                      ·
                        rfl

theorem cell23_3325077_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 2, 2, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 2, 2, 3, 4, 3].length) (baseStart_3325077 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3325077 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3325077 prefixEnd_3325077 := by exact prefixLift 3325077
  have htrace : WordTrace (prefixWord ++ tailWord_3325077) baseStart_3325077 baseEnd_3325077 := by
    simpa [prefixWord, tailWord_3325077, baseEnd_3325077] using wordTrace_append hprefix tailTrace_3325077
  have hstable : (prefixWord ++ tailWord_3325077).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3325077).length < 2 ^ (prefixWord ++ tailWord_3325077).sum := by decide
  have hdescent : baseEnd_3325077 < baseStart_3325077 := by decide
  rcases family_descends (prefixWord ++ tailWord_3325077) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3325107 : List Nat := [1, 1, 1, 2, 3, 2, 2, 1, 2, 5, 3]
def baseStart_3325107 : Nat := 118140960795 + 3325107 * 2 ^ 59
def prefixEnd_3325107 : Nat := 4983230072969 + 3 ^ 40 * 3325107 * 2
def baseEnd_3325107 : Nat := 1707378118629627237270617

theorem tailTrace_3325107 : CollatzResearch.WordTrace tailWord_3325107 prefixEnd_3325107 1707378118629627237270617 := by
  unfold tailWord_3325107
  simp only [CollatzResearch.WordTrace]
  refine ⟨121276615564712696909229575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80851077043141797939486383 121276615564712696909229575)
  ·
    refine ⟨181914923347069045363844363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121276615564712696909229575 181914923347069045363844363)
    ·
      refine ⟨272872385020603568045766545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 181914923347069045363844363 272872385020603568045766545)
      ·
        refine ⟨204654288765452676034324909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 272872385020603568045766545 204654288765452676034324909)
        ·
          refine ⟨76745358287044753512871841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 204654288765452676034324909 76745358287044753512871841)
          ·
            refine ⟨57559018715283565134653881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 76745358287044753512871841 57559018715283565134653881)
            ·
              refine ⟨43169264036462673850990411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 57559018715283565134653881 43169264036462673850990411)
              ·
                refine ⟨64753896054694010776485617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43169264036462673850990411 64753896054694010776485617)
                ·
                  refine ⟨48565422041020508082364213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 64753896054694010776485617 48565422041020508082364213)
                  ·
                    refine ⟨4553008316345672632721645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 48565422041020508082364213 4553008316345672632721645)
                    ·
                      refine ⟨1707378118629627237270617, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4553008316345672632721645 1707378118629627237270617)
                      ·
                        rfl

theorem cell23_3325107_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 2, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 2, 1, 2, 5, 3].length) (baseStart_3325107 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3325107 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3325107 prefixEnd_3325107 := by exact prefixLift 3325107
  have htrace : WordTrace (prefixWord ++ tailWord_3325107) baseStart_3325107 baseEnd_3325107 := by
    simpa [prefixWord, tailWord_3325107, baseEnd_3325107] using wordTrace_append hprefix tailTrace_3325107
  have hstable : (prefixWord ++ tailWord_3325107).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3325107).length < 2 ^ (prefixWord ++ tailWord_3325107).sum := by decide
  have hdescent : baseEnd_3325107 < baseStart_3325107 := by decide
  rcases family_descends (prefixWord ++ tailWord_3325107) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3325164 : List Nat := [2, 2, 1, 1, 2, 4, 2, 1, 3, 1, 4]
def baseStart_3325164 : Nat := 118140960795 + 3325164 * 2 ^ 59
def prefixEnd_3325164 : Nat := 4983230072969 + 3 ^ 40 * 3325164 * 2
def baseEnd_3325164 : Nat := 1707407387026933514257855

theorem tailTrace_3325164 : CollatzResearch.WordTrace tailWord_3325164 prefixEnd_3325164 1707407387026933514257855 := by
  unfold tailWord_3325164
  simp only [CollatzResearch.WordTrace]
  refine ⟨60639347262753097822027273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80852463017004130429369697 60639347262753097822027273)
  ·
    refine ⟨45479510447064823366520455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60639347262753097822027273 45479510447064823366520455)
    ·
      refine ⟨68219265670597235049780683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45479510447064823366520455 68219265670597235049780683)
      ·
        refine ⟨102328898505895852574671025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68219265670597235049780683 102328898505895852574671025)
        ·
          refine ⟨76746673879421889431003269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 102328898505895852574671025 76746673879421889431003269)
          ·
            refine ⟨14390001352391604268313113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 76746673879421889431003269 14390001352391604268313113)
            ·
              refine ⟨10792501014293703201234835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14390001352391604268313113 10792501014293703201234835)
              ·
                refine ⟨16188751521440554801852253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10792501014293703201234835 16188751521440554801852253)
                ·
                  refine ⟨6070781820540208050694595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16188751521440554801852253 6070781820540208050694595)
                  ·
                    refine ⟨9106172730810312076041893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6070781820540208050694595 9106172730810312076041893)
                    ·
                      refine ⟨1707407387026933514257855, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9106172730810312076041893 1707407387026933514257855)
                      ·
                        rfl

theorem cell23_3325164_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 3, 1, 4].length) (baseStart_3325164 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3325164 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3325164 prefixEnd_3325164 := by exact prefixLift 3325164
  have htrace : WordTrace (prefixWord ++ tailWord_3325164) baseStart_3325164 baseEnd_3325164 := by
    simpa [prefixWord, tailWord_3325164, baseEnd_3325164] using wordTrace_append hprefix tailTrace_3325164
  have hstable : (prefixWord ++ tailWord_3325164).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3325164).length < 2 ^ (prefixWord ++ tailWord_3325164).sum := by decide
  have hdescent : baseEnd_3325164 < baseStart_3325164 := by decide
  rcases family_descends (prefixWord ++ tailWord_3325164) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3325187 : List Nat := [1, 1, 1, 3, 2, 5, 10]
def baseStart_3325187 : Nat := 118140960795 + 3325187 * 2 ^ 59
def prefixEnd_3325187 : Nat := 4983230072969 + 3 ^ 40 * 3325187 * 2
def baseEnd_3325187 : Nat := 21079249346691196595929

theorem tailTrace_3325187 : CollatzResearch.WordTrace tailWord_3325187 prefixEnd_3325187 21079249346691196595929 := by
  unfold tailWord_3325187
  simp only [CollatzResearch.WordTrace]
  refine ⟨121279533404422870572141815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80853022269615247048094543 121279533404422870572141815)
  ·
    refine ⟨181919300106634305858212723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121279533404422870572141815 181919300106634305858212723)
    ·
      refine ⟨272878950159951458787319085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 181919300106634305858212723 272878950159951458787319085)
      ·
        refine ⟨102329606309981797045244657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 272878950159951458787319085 102329606309981797045244657)
        ·
          refine ⟨76747204732486347783933493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 102329606309981797045244657 76747204732486347783933493)
          ·
            refine ⟨7195050443670595104743765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 76747204732486347783933493 7195050443670595104743765)
            ·
              refine ⟨21079249346691196595929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 7195050443670595104743765 21079249346691196595929)
              ·
                rfl

theorem cell23_3325187_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 5, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 5, 10].length) (baseStart_3325187 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3325187 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3325187 prefixEnd_3325187 := by exact prefixLift 3325187
  have htrace : WordTrace (prefixWord ++ tailWord_3325187) baseStart_3325187 baseEnd_3325187 := by
    simpa [prefixWord, tailWord_3325187, baseEnd_3325187] using wordTrace_append hprefix tailTrace_3325187
  have hstable : (prefixWord ++ tailWord_3325187).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3325187).length < 2 ^ (prefixWord ++ tailWord_3325187).sum := by decide
  have hdescent : baseEnd_3325187 < baseStart_3325187 := by decide
  rcases family_descends (prefixWord ++ tailWord_3325187) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3325198 : List Nat := [4, 1, 1, 2, 1, 3, 1, 3, 3, 2, 2]
def baseStart_3325198 : Nat := 118140960795 + 3325198 * 2 ^ 59
def prefixEnd_3325198 : Nat := 4983230072969 + 3 ^ 40 * 3325198 * 2
def baseEnd_3325198 : Nat := 1707424845369186381232699

theorem tailTrace_3325198 : CollatzResearch.WordTrace tailWord_3325198 prefixEnd_3325198 1707424845369186381232699 := by
  unfold tailWord_3325198
  simp only [CollatzResearch.WordTrace]
  refine ⟨15159991825922877431349031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 80853289738255346300528165 15159991825922877431349031)
  ·
    refine ⟨22739987738884316147023547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15159991825922877431349031 22739987738884316147023547)
    ·
      refine ⟨34109981608326474220535321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22739987738884316147023547 34109981608326474220535321)
      ·
        refine ⟨25582486206244855665401491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34109981608326474220535321 25582486206244855665401491)
        ·
          refine ⟨38373729309367283498102237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25582486206244855665401491 38373729309367283498102237)
          ·
            refine ⟨14390148491012731311788339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 38373729309367283498102237 14390148491012731311788339)
            ·
              refine ⟨21585222736519096967682509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14390148491012731311788339 21585222736519096967682509)
              ·
                refine ⟨8094458526194661362880941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21585222736519096967682509 8094458526194661362880941)
                ·
                  refine ⟨3035421947322998011080353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8094458526194661362880941 3035421947322998011080353)
                  ·
                    refine ⟨2276566460492248508310265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3035421947322998011080353 2276566460492248508310265)
                    ·
                      refine ⟨1707424845369186381232699, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2276566460492248508310265 1707424845369186381232699)
                      ·
                        rfl

theorem cell23_3325198_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 3, 1, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 3, 1, 3, 3, 2, 2].length) (baseStart_3325198 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3325198 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3325198 prefixEnd_3325198 := by exact prefixLift 3325198
  have htrace : WordTrace (prefixWord ++ tailWord_3325198) baseStart_3325198 baseEnd_3325198 := by
    simpa [prefixWord, tailWord_3325198, baseEnd_3325198] using wordTrace_append hprefix tailTrace_3325198
  have hstable : (prefixWord ++ tailWord_3325198).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3325198).length < 2 ^ (prefixWord ++ tailWord_3325198).sum := by decide
  have hdescent : baseEnd_3325198 < baseStart_3325198 := by decide
  rcases family_descends (prefixWord ++ tailWord_3325198) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3325208 : List Nat := [2, 1, 2, 3, 1, 4, 3, 1, 2, 4]
def baseStart_3325208 : Nat := 118140960795 + 3325208 * 2 ^ 59
def prefixEnd_3325208 : Nat := 4983230072969 + 3 ^ 40 * 3325208 * 2
def baseEnd_3325208 : Nat := 569143326725243780702551

theorem tailTrace_3325208 : CollatzResearch.WordTrace tailWord_3325208 prefixEnd_3325208 569143326725243780702551 := by
  unfold tailWord_3325208
  simp only [CollatzResearch.WordTrace]
  refine ⟨60640149668673395579328139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80853532891564527439104185 60640149668673395579328139)
  ·
    refine ⟨90960224503010093368992209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60640149668673395579328139 90960224503010093368992209)
    ·
      refine ⟨68220168377257570026744157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 90960224503010093368992209 68220168377257570026744157)
      ·
        refine ⟨25582563141471588760029059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 68220168377257570026744157 25582563141471588760029059)
        ·
          refine ⟨38373844712207383140043589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25582563141471588760029059 38373844712207383140043589)
          ·
            refine ⟨7195095883538884338758173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 38373844712207383140043589 7195095883538884338758173)
            ·
              refine ⟨2698160956327081627034315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7195095883538884338758173 2698160956327081627034315)
              ·
                refine ⟨4047241434490622440551473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2698160956327081627034315 4047241434490622440551473)
                ·
                  refine ⟨3035431075867966830413605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4047241434490622440551473 3035431075867966830413605)
                  ·
                    refine ⟨569143326725243780702551, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3035431075867966830413605 569143326725243780702551)
                    ·
                      rfl

theorem cell23_3325208_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 4, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 4, 3, 1, 2, 4].length) (baseStart_3325208 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3325208 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3325208 prefixEnd_3325208 := by exact prefixLift 3325208
  have htrace : WordTrace (prefixWord ++ tailWord_3325208) baseStart_3325208 baseEnd_3325208 := by
    simpa [prefixWord, tailWord_3325208, baseEnd_3325208] using wordTrace_append hprefix tailTrace_3325208
  have hstable : (prefixWord ++ tailWord_3325208).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3325208).length < 2 ^ (prefixWord ++ tailWord_3325208).sum := by decide
  have hdescent : baseEnd_3325208 < baseStart_3325208 := by decide
  rcases family_descends (prefixWord ++ tailWord_3325208) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3325221 : List Nat := [1, 3, 1, 2, 4, 3, 2, 7]
def baseStart_3325221 : Nat := 118140960795 + 3325221 * 2 ^ 59
def prefixEnd_3325221 : Nat := 4983230072969 + 3 ^ 40 * 3325221 * 2
def baseEnd_3325221 : Nat := 63238394645342214490559

theorem tailTrace_3325221 : CollatzResearch.WordTrace tailWord_3325221 prefixEnd_3325221 63238394645342214490559 := by
  unfold tailWord_3325221
  simp only [CollatzResearch.WordTrace]
  refine ⟨121280773486299694378879517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80853848990866462919253011 121280773486299694378879517)
  ·
    refine ⟨45480290057362385392079819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 121280773486299694378879517 45480290057362385392079819)
    ·
      refine ⟨68220435086043578088119729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45480290057362385392079819 68220435086043578088119729)
      ·
        refine ⟨51165326314532683566089797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 68220435086043578088119729 51165326314532683566089797)
        ·
          refine ⟨9593498683974878168641837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 51165326314532683566089797 9593498683974878168641837)
          ·
            refine ⟨3597562006490579313240689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9593498683974878168641837 3597562006490579313240689)
            ·
              refine ⟨2698171504867934484930517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3597562006490579313240689 2698171504867934484930517)
              ·
                refine ⟨63238394645342214490559, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2698171504867934484930517 63238394645342214490559)
                ·
                  rfl

theorem cell23_3325221_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 3, 2, 7].length) (baseStart_3325221 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3325221 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3325221 prefixEnd_3325221 := by exact prefixLift 3325221
  have htrace : WordTrace (prefixWord ++ tailWord_3325221) baseStart_3325221 baseEnd_3325221 := by
    simpa [prefixWord, tailWord_3325221, baseEnd_3325221] using wordTrace_append hprefix tailTrace_3325221
  have hstable : (prefixWord ++ tailWord_3325221).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3325221).length < 2 ^ (prefixWord ++ tailWord_3325221).sum := by decide
  have hdescent : baseEnd_3325221 < baseStart_3325221 := by decide
  rcases family_descends (prefixWord ++ tailWord_3325221) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3325238 : List Nat := [5, 1, 2, 3, 1, 2, 9]
def baseStart_3325238 : Nat := 118140960795 + 3325238 * 2 ^ 59
def prefixEnd_3325238 : Nat := 4983230072969 + 3 ^ 40 * 3325238 * 2
def baseEnd_3325238 : Nat := 21079572649325508947315

theorem tailTrace_3325238 : CollatzResearch.WordTrace tailWord_3325238 prefixEnd_3325238 21079572649325508947315 := by
  unfold tailWord_3325238
  simp only [CollatzResearch.WordTrace]
  refine ⟨7580087095452381642640523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 80854262351492070854832245 7580087095452381642640523)
  ·
    refine ⟨11370130643178572463960785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7580087095452381642640523 11370130643178572463960785)
    ·
      refine ⟨8527597982383929347970589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11370130643178572463960785 8527597982383929347970589)
      ·
        refine ⟨3197849243393973505488971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8527597982383929347970589 3197849243393973505488971)
        ·
          refine ⟨4796773865090960258233457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3197849243393973505488971 4796773865090960258233457)
          ·
            refine ⟨3597580398818220193675093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4796773865090960258233457 3597580398818220193675093)
            ·
              refine ⟨21079572649325508947315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 3597580398818220193675093 21079572649325508947315)
              ·
                rfl

theorem cell23_3325238_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 3, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 3, 1, 2, 9].length) (baseStart_3325238 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3325238 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3325238 prefixEnd_3325238 := by exact prefixLift 3325238
  have htrace : WordTrace (prefixWord ++ tailWord_3325238) baseStart_3325238 baseEnd_3325238 := by
    simpa [prefixWord, tailWord_3325238, baseEnd_3325238] using wordTrace_append hprefix tailTrace_3325238
  have hstable : (prefixWord ++ tailWord_3325238).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3325238).length < 2 ^ (prefixWord ++ tailWord_3325238).sum := by decide
  have hdescent : baseEnd_3325238 < baseStart_3325238 := by decide
  rcases family_descends (prefixWord ++ tailWord_3325238) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3325249 : List Nat := [1, 2, 5, 2, 1, 2, 3, 2, 1, 2, 2]
def baseStart_3325249 : Nat := 118140960795 + 3325249 * 2 ^ 59
def prefixEnd_3325249 : Nat := 4983230072969 + 3 ^ 40 * 3325249 * 2
def baseEnd_3325249 : Nat := 1707451032882565681694965

theorem tailTrace_3325249 : CollatzResearch.WordTrace tailWord_3325249 prefixEnd_3325249 1707451032882565681694965 := by
  unfold tailWord_3325249
  simp only [CollatzResearch.WordTrace]
  refine ⟨121281794730198255160898801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80854529820132170107265867 121281794730198255160898801)
  ·
    refine ⟨90961346047648691370674101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 121281794730198255160898801 90961346047648691370674101)
    ·
      refine ⟨8527626191967064816000697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 90961346047648691370674101 8527626191967064816000697)
      ·
        refine ⟨6395719643975298612000523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8527626191967064816000697 6395719643975298612000523)
        ·
          refine ⟨9593579465962947918000785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6395719643975298612000523 9593579465962947918000785)
          ·
            refine ⟨7195184599472210938500589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9593579465962947918000785 7195184599472210938500589)
            ·
              refine ⟨2698194224802079101937721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7195184599472210938500589 2698194224802079101937721)
              ·
                refine ⟨2023645668601559326453291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2698194224802079101937721 2023645668601559326453291)
                ·
                  refine ⟨3035468502902338989679937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2023645668601559326453291 3035468502902338989679937)
                  ·
                    refine ⟨2276601377176754242259953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3035468502902338989679937 2276601377176754242259953)
                    ·
                      refine ⟨1707451032882565681694965, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2276601377176754242259953 1707451032882565681694965)
                      ·
                        rfl

theorem cell23_3325249_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 2, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 2, 3, 2, 1, 2, 2].length) (baseStart_3325249 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3325249 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3325249 prefixEnd_3325249 := by exact prefixLift 3325249
  have htrace : WordTrace (prefixWord ++ tailWord_3325249) baseStart_3325249 baseEnd_3325249 := by
    simpa [prefixWord, tailWord_3325249, baseEnd_3325249] using wordTrace_append hprefix tailTrace_3325249
  have hstable : (prefixWord ++ tailWord_3325249).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3325249).length < 2 ^ (prefixWord ++ tailWord_3325249).sum := by decide
  have hdescent : baseEnd_3325249 < baseStart_3325249 := by decide
  rcases family_descends (prefixWord ++ tailWord_3325249) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3325274 : List Nat := [3, 1, 1, 2, 1, 2, 3, 2, 2, 1, 5]
def baseStart_3325274 : Nat := 118140960795 + 3325274 * 2 ^ 59
def prefixEnd_3325274 : Nat := 4983230072969 + 3 ^ 40 * 3325274 * 2
def baseEnd_3325274 : Nat := 1707463869898928083882349

theorem tailTrace_3325274 : CollatzResearch.WordTrace tailWord_3325274 prefixEnd_3325274 1707463869898928083882349 := by
  unfold tailWord_3325274
  simp only [CollatzResearch.WordTrace]
  refine ⟨30320676638776921107639719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 80855137703405122953705917 30320676638776921107639719)
  ·
    refine ⟨45481014958165381661459579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30320676638776921107639719 45481014958165381661459579)
    ·
      refine ⟨68221522437248072492189369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45481014958165381661459579 68221522437248072492189369)
      ·
        refine ⟨51166141827936054369142027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 68221522437248072492189369 51166141827936054369142027)
        ·
          refine ⟨76749212741904081553713041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51166141827936054369142027 76749212741904081553713041)
          ·
            refine ⟨57561909556428061165284781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 76749212741904081553713041 57561909556428061165284781)
            ·
              refine ⟨21585716083660522936981793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 57561909556428061165284781 21585716083660522936981793)
              ·
                refine ⟨16189287062745392202736345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21585716083660522936981793 16189287062745392202736345)
                ·
                  refine ⟨12141965297059044152052259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16189287062745392202736345 12141965297059044152052259)
                  ·
                    refine ⟨18212947945588566228078389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12141965297059044152052259 18212947945588566228078389)
                    ·
                      refine ⟨1707463869898928083882349, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 18212947945588566228078389 1707463869898928083882349)
                      ·
                        rfl

theorem cell23_3325274_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 3, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 3, 2, 2, 1, 5].length) (baseStart_3325274 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3325274 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3325274 prefixEnd_3325274 := by exact prefixLift 3325274
  have htrace : WordTrace (prefixWord ++ tailWord_3325274) baseStart_3325274 baseEnd_3325274 := by
    simpa [prefixWord, tailWord_3325274, baseEnd_3325274] using wordTrace_append hprefix tailTrace_3325274
  have hstable : (prefixWord ++ tailWord_3325274).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3325274).length < 2 ^ (prefixWord ++ tailWord_3325274).sum := by decide
  have hdescent : baseEnd_3325274 < baseStart_3325274 := by decide
  rcases family_descends (prefixWord ++ tailWord_3325274) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3325304 : List Nat := [2, 1, 2, 1, 1, 1, 1, 1, 5, 5, 3]
def baseStart_3325304 : Nat := 118140960795 + 3325304 * 2 ^ 59
def prefixEnd_3325304 : Nat := 4983230072969 + 3 ^ 40 * 3325304 * 2
def baseEnd_3325304 : Nat := 1707479274318562966507211

theorem tailTrace_3325304 : CollatzResearch.WordTrace tailWord_3325304 prefixEnd_3325304 1707479274318562966507211 := by
  unfold tailWord_3325304
  simp only [CollatzResearch.WordTrace]
  refine ⟨60641900372499499777075483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80855867163332666369433977 60641900372499499777075483)
  ·
    refine ⟨90962850558749249665613225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60641900372499499777075483 90962850558749249665613225)
    ·
      refine ⟨68222137919061937249209919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 90962850558749249665613225 68222137919061937249209919)
      ·
        refine ⟨102333206878592905873814879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68222137919061937249209919 102333206878592905873814879)
        ·
          refine ⟨153499810317889358810722319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 102333206878592905873814879 153499810317889358810722319)
          ·
            refine ⟨230249715476834038216083479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 153499810317889358810722319 230249715476834038216083479)
            ·
              refine ⟨345374573215251057324125219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 230249715476834038216083479 345374573215251057324125219)
              ·
                refine ⟨518061859822876585986187829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 345374573215251057324125219 518061859822876585986187829)
                ·
                  refine ⟨48568299358394679936205109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 518061859822876585986187829 48568299358394679936205109)
                  ·
                    refine ⟨4553278064849501244019229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 48568299358394679936205109 4553278064849501244019229)
                    ·
                      refine ⟨1707479274318562966507211, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4553278064849501244019229 1707479274318562966507211)
                      ·
                        rfl

theorem cell23_3325304_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 1, 5, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 1, 5, 5, 3].length) (baseStart_3325304 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3325304 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3325304 prefixEnd_3325304 := by exact prefixLift 3325304
  have htrace : WordTrace (prefixWord ++ tailWord_3325304) baseStart_3325304 baseEnd_3325304 := by
    simpa [prefixWord, tailWord_3325304, baseEnd_3325304] using wordTrace_append hprefix tailTrace_3325304
  have hstable : (prefixWord ++ tailWord_3325304).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3325304).length < 2 ^ (prefixWord ++ tailWord_3325304).sum := by decide
  have hdescent : baseEnd_3325304 < baseStart_3325304 := by decide
  rcases family_descends (prefixWord ++ tailWord_3325304) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3325324 : List Nat := [2, 2, 1, 2, 1, 3, 2, 2, 1, 7]
def baseStart_3325324 : Nat := 118140960795 + 3325324 * 2 ^ 59
def prefixEnd_3325324 : Nat := 4983230072969 + 3 ^ 40 * 3325324 * 2
def baseEnd_3325324 : Nat := 569163181310550962752373

theorem tailTrace_3325324 : CollatzResearch.WordTrace tailWord_3325324 prefixEnd_3325324 569163181310550962752373 := by
  unfold tailWord_3325324
  simp only [CollatzResearch.WordTrace]
  refine ⟨60642265102463271484939513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80856353469951028646586017 60642265102463271484939513)
  ·
    refine ⟨45481698826847453613704635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60642265102463271484939513 45481698826847453613704635)
    ·
      refine ⟨68222548240271180420556953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45481698826847453613704635 68222548240271180420556953)
      ·
        refine ⟨51166911180203385315417715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 68222548240271180420556953 51166911180203385315417715)
        ·
          refine ⟨76750366770305077973126573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51166911180203385315417715 76750366770305077973126573)
          ·
            refine ⟨28781387538864404239922465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 76750366770305077973126573 28781387538864404239922465)
            ·
              refine ⟨21586040654148303179941849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28781387538864404239922465 21586040654148303179941849)
              ·
                refine ⟨16189530490611227384956387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21586040654148303179941849 16189530490611227384956387)
                ·
                  refine ⟨24284295735916841077434581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16189530490611227384956387 24284295735916841077434581)
                  ·
                    refine ⟨569163181310550962752373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 24284295735916841077434581 569163181310550962752373)
                    ·
                      rfl

theorem cell23_3325324_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 2, 2, 1, 7].length) (baseStart_3325324 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3325324 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3325324 prefixEnd_3325324 := by exact prefixLift 3325324
  have htrace : WordTrace (prefixWord ++ tailWord_3325324) baseStart_3325324 baseEnd_3325324 := by
    simpa [prefixWord, tailWord_3325324, baseEnd_3325324] using wordTrace_append hprefix tailTrace_3325324
  have hstable : (prefixWord ++ tailWord_3325324).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3325324).length < 2 ^ (prefixWord ++ tailWord_3325324).sum := by decide
  have hdescent : baseEnd_3325324 < baseStart_3325324 := by decide
  rcases family_descends (prefixWord ++ tailWord_3325324) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3325341 : List Nat := [1, 4, 2, 1, 3, 2, 1, 1, 1, 7]
def baseStart_3325341 : Nat := 118140960795 + 3325341 * 2 ^ 59
def prefixEnd_3325341 : Nat := 4983230072969 + 3 ^ 40 * 3325341 * 2
def baseEnd_3325341 : Nat := 569166091034259773914847

theorem tailTrace_3325341 : CollatzResearch.WordTrace tailWord_3325341 prefixEnd_3325341 569166091034259773914847 := by
  unfold tailWord_3325341
  simp only [CollatzResearch.WordTrace]
  refine ⟨121285150245864954873247877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80856766830576636582165251 121285150245864954873247877)
  ·
    refine ⟨22740965671099679038733977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 121285150245864954873247877 22740965671099679038733977)
    ·
      refine ⟨17055724253324759279050483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22740965671099679038733977 17055724253324759279050483)
      ·
        refine ⟨25583586379987138918575725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17055724253324759279050483 25583586379987138918575725)
        ·
          refine ⟨9593844892495177094465897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25583586379987138918575725 9593844892495177094465897)
          ·
            refine ⟨7195383669371382820849423, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9593844892495177094465897 7195383669371382820849423)
            ·
              refine ⟨10793075504057074231274135, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7195383669371382820849423 10793075504057074231274135)
              ·
                refine ⟨16189613256085611346911203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10793075504057074231274135 16189613256085611346911203)
                ·
                  refine ⟨24284419884128417020366805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16189613256085611346911203 24284419884128417020366805)
                  ·
                    refine ⟨569166091034259773914847, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 24284419884128417020366805 569166091034259773914847)
                    ·
                      rfl

theorem cell23_3325341_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 2, 1, 1, 1, 7].length) (baseStart_3325341 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3325341 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3325341 prefixEnd_3325341 := by exact prefixLift 3325341
  have htrace : WordTrace (prefixWord ++ tailWord_3325341) baseStart_3325341 baseEnd_3325341 := by
    simpa [prefixWord, tailWord_3325341, baseEnd_3325341] using wordTrace_append hprefix tailTrace_3325341
  have hstable : (prefixWord ++ tailWord_3325341).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3325341).length < 2 ^ (prefixWord ++ tailWord_3325341).sum := by decide
  have hdescent : baseEnd_3325341 < baseStart_3325341 := by decide
  rcases family_descends (prefixWord ++ tailWord_3325341) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3325361 : List Nat := [1, 2, 2, 4, 1, 1, 2, 1, 4, 1, 4]
def baseStart_3325361 : Nat := 118140960795 + 3325361 * 2 ^ 59
def prefixEnd_3325361 : Nat := 4983230072969 + 3 ^ 40 * 3325361 * 2
def baseEnd_3325361 : Nat := 1707508542715869243494449

theorem tailTrace_3325361 : CollatzResearch.WordTrace tailWord_3325361 prefixEnd_3325361 1707508542715869243494449 := by
  unfold tailWord_3325361
  simp only [CollatzResearch.WordTrace]
  refine ⟨121285879705792498288975937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80857253137194998859317291 121285879705792498288975937)
  ·
    refine ⟨90964409779344373716731953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 121285879705792498288975937 90964409779344373716731953)
    ·
      refine ⟨68223307334508280287548965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 90964409779344373716731953 68223307334508280287548965)
      ·
        refine ⟨12791870125220302553915431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 68223307334508280287548965 12791870125220302553915431)
        ·
          refine ⟨19187805187830453830873147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12791870125220302553915431 19187805187830453830873147)
          ·
            refine ⟨28781707781745680746309721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19187805187830453830873147 28781707781745680746309721)
            ·
              refine ⟨21586280836309260559732291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28781707781745680746309721 21586280836309260559732291)
              ·
                refine ⟨32379421254463890839598437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21586280836309260559732291 32379421254463890839598437)
                ·
                  refine ⟨6071141485211979532424707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 32379421254463890839598437 6071141485211979532424707)
                  ·
                    refine ⟨9106712227817969298637061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6071141485211979532424707 9106712227817969298637061)
                    ·
                      refine ⟨1707508542715869243494449, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9106712227817969298637061 1707508542715869243494449)
                      ·
                        rfl

theorem cell23_3325361_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 2, 1, 4, 1, 4].length) (baseStart_3325361 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3325361 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3325361 prefixEnd_3325361 := by exact prefixLift 3325361
  have htrace : WordTrace (prefixWord ++ tailWord_3325361) baseStart_3325361 baseEnd_3325361 := by
    simpa [prefixWord, tailWord_3325361, baseEnd_3325361] using wordTrace_append hprefix tailTrace_3325361
  have hstable : (prefixWord ++ tailWord_3325361).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3325361).length < 2 ^ (prefixWord ++ tailWord_3325361).sum := by decide
  have hdescent : baseEnd_3325361 < baseStart_3325361 := by decide
  rcases family_descends (prefixWord ++ tailWord_3325361) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3325388 : List Nat := [2, 2, 1, 4, 2, 1, 2, 2, 3, 4]
def baseStart_3325388 : Nat := 118140960795 + 3325388 * 2 ^ 59
def prefixEnd_3325388 : Nat := 4983230072969 + 3 ^ 40 * 3325388 * 2
def baseEnd_3325388 : Nat := 569174135564513545952275

theorem tailTrace_3325388 : CollatzResearch.WordTrace tailWord_3325388 prefixEnd_3325388 569174135564513545952275 := by
  unfold tailWord_3325388
  simp only [CollatzResearch.WordTrace]
  refine ⟨60643432238347340950104409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80857909651129787933472545 60643432238347340950104409)
  ·
    refine ⟨45482574178760505712578307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60643432238347340950104409 45482574178760505712578307)
    ·
      refine ⟨68223861268140758568867461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45482574178760505712578307 68223861268140758568867461)
      ·
        refine ⟨12791973987776392231662649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 68223861268140758568867461 12791973987776392231662649)
        ·
          refine ⟨9593980490832294173746987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12791973987776392231662649 9593980490832294173746987)
          ·
            refine ⟨14390970736248441260620481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9593980490832294173746987 14390970736248441260620481)
            ·
              refine ⟨10793228052186330945465361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14390970736248441260620481 10793228052186330945465361)
              ·
                refine ⟨8094921039139748209099021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10793228052186330945465361 8094921039139748209099021)
                ·
                  refine ⟨3035595389677405578412133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8094921039139748209099021 3035595389677405578412133)
                  ·
                    refine ⟨569174135564513545952275, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3035595389677405578412133 569174135564513545952275)
                    ·
                      rfl

theorem cell23_3325388_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 1, 2, 2, 3, 4].length) (baseStart_3325388 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3325388 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3325388 prefixEnd_3325388 := by exact prefixLift 3325388
  have htrace : WordTrace (prefixWord ++ tailWord_3325388) baseStart_3325388 baseEnd_3325388 := by
    simpa [prefixWord, tailWord_3325388, baseEnd_3325388] using wordTrace_append hprefix tailTrace_3325388
  have hstable : (prefixWord ++ tailWord_3325388).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3325388).length < 2 ^ (prefixWord ++ tailWord_3325388).sum := by decide
  have hdescent : baseEnd_3325388 < baseStart_3325388 := by decide
  rcases family_descends (prefixWord ++ tailWord_3325388) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3325422 : List Nat := [4, 1, 2, 1, 2, 1, 5, 2, 1, 4]
def baseStart_3325422 : Nat := 118140960795 + 3325422 * 2 ^ 59
def prefixEnd_3325422 : Nat := 4983230072969 + 3 ^ 40 * 3325422 * 2
def baseEnd_3325422 : Nat := 569179955011931168277223

theorem tailTrace_3325422 : CollatzResearch.WordTrace tailWord_3325422 prefixEnd_3325422 569179955011931168277223 := by
  unfold tailWord_3325422
  simp only [CollatzResearch.WordTrace]
  refine ⟨15161013069821438213368315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 80858736372381003804631013 15161013069821438213368315)
  ·
    refine ⟨22741519604732157320052473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15161013069821438213368315 22741519604732157320052473)
    ·
      refine ⟨17056139703549117990039355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22741519604732157320052473 17056139703549117990039355)
      ·
        refine ⟨25584209555323676985059033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17056139703549117990039355 25584209555323676985059033)
        ·
          refine ⟨19188157166492757738794275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25584209555323676985059033 19188157166492757738794275)
          ·
            refine ⟨28782235749739136608191413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19188157166492757738794275 28782235749739136608191413)
            ·
              refine ⟨2698334601538044057017945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 28782235749739136608191413 2698334601538044057017945)
              ·
                refine ⟨2023750951153533042763459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2698334601538044057017945 2023750951153533042763459)
                ·
                  refine ⟨3035626426730299564145189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2023750951153533042763459 3035626426730299564145189)
                  ·
                    refine ⟨569179955011931168277223, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3035626426730299564145189 569179955011931168277223)
                    ·
                      rfl

theorem cell23_3325422_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 5, 2, 1, 4].length) (baseStart_3325422 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3325422 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3325422 prefixEnd_3325422 := by exact prefixLift 3325422
  have htrace : WordTrace (prefixWord ++ tailWord_3325422) baseStart_3325422 baseEnd_3325422 := by
    simpa [prefixWord, tailWord_3325422, baseEnd_3325422] using wordTrace_append hprefix tailTrace_3325422
  have hstable : (prefixWord ++ tailWord_3325422).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3325422).length < 2 ^ (prefixWord ++ tailWord_3325422).sum := by decide
  have hdescent : baseEnd_3325422 < baseStart_3325422 := by decide
  rcases family_descends (prefixWord ++ tailWord_3325422) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3325448 : List Nat := [2, 1, 3, 2, 1, 1, 5, 2, 1, 5]
def baseStart_3325448 : Nat := 118140960795 + 3325448 * 2 ^ 59
def prefixEnd_3325448 : Nat := 4983230072969 + 3 ^ 40 * 3325448 * 2
def baseEnd_3325448 : Nat := 569184405177603467702183

theorem tailTrace_3325448 : CollatzResearch.WordTrace tailWord_3325448 prefixEnd_3325448 569184405177603467702183 := by
  unfold tailWord_3325448
  simp only [CollatzResearch.WordTrace]
  refine ⟨60644526428238656073696499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80859368570984874764928665 60644526428238656073696499)
  ·
    refine ⟨90966789642357984110544749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60644526428238656073696499 90966789642357984110544749)
    ·
      refine ⟨34112546115884244041454281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 90966789642357984110544749 34112546115884244041454281)
      ·
        refine ⟨25584409586913183031090711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34112546115884244041454281 25584409586913183031090711)
        ·
          refine ⟨38376614380369774546636067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25584409586913183031090711 38376614380369774546636067)
          ·
            refine ⟨57564921570554661819954101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38376614380369774546636067 57564921570554661819954101)
            ·
              refine ⟨5396711397239499545620697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 57564921570554661819954101 5396711397239499545620697)
              ·
                refine ⟨4047533547929624659215523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5396711397239499545620697 4047533547929624659215523)
                ·
                  refine ⟨6071300321894436988823285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4047533547929624659215523 6071300321894436988823285)
                  ·
                    refine ⟨569184405177603467702183, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6071300321894436988823285 569184405177603467702183)
                    ·
                      rfl

theorem cell23_3325448_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 5, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 5, 2, 1, 5].length) (baseStart_3325448 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3325448 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3325448 prefixEnd_3325448 := by exact prefixLift 3325448
  have htrace : WordTrace (prefixWord ++ tailWord_3325448) baseStart_3325448 baseEnd_3325448 := by
    simpa [prefixWord, tailWord_3325448, baseEnd_3325448] using wordTrace_append hprefix tailTrace_3325448
  have hstable : (prefixWord ++ tailWord_3325448).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3325448).length < 2 ^ (prefixWord ++ tailWord_3325448).sum := by decide
  have hdescent : baseEnd_3325448 < baseStart_3325448 := by decide
  rcases family_descends (prefixWord ++ tailWord_3325448) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3325461 : List Nat := [1, 3, 2, 1, 3, 2, 1, 1, 3, 6]
def baseStart_3325461 : Nat := 118140960795 + 3325461 * 2 ^ 59
def prefixEnd_3325461 : Nat := 4983230072969 + 3 ^ 40 * 3325461 * 2
def baseEnd_3325461 : Nat := 569186630260439617414663

theorem tailTrace_3325461 : CollatzResearch.WordTrace tailWord_3325461 prefixEnd_3325461 569186630260439617414663 := by
  unfold tailWord_3325461
  simp only [CollatzResearch.WordTrace]
  refine ⟨121289527005430215367616237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80859684670286810245077491 121289527005430215367616237)
  ·
    refine ⟨45483572627036330762856089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 121289527005430215367616237 45483572627036330762856089)
    ·
      refine ⟨34112679470277248072142067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45483572627036330762856089 34112679470277248072142067)
      ·
        refine ⟨51169019205415872108213101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34112679470277248072142067 51169019205415872108213101)
        ·
          refine ⟨19188382202030952040579913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 51169019205415872108213101 19188382202030952040579913)
          ·
            refine ⟨14391286651523214030434935, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19188382202030952040579913 14391286651523214030434935)
            ·
              refine ⟨21586929977284821045652403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14391286651523214030434935 21586929977284821045652403)
              ·
                refine ⟨32380394965927231568478605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21586929977284821045652403 32380394965927231568478605)
                ·
                  refine ⟨12142648112222711838179477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 32380394965927231568478605 12142648112222711838179477)
                  ·
                    refine ⟨569186630260439617414663, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 12142648112222711838179477 569186630260439617414663)
                    ·
                      rfl

theorem cell23_3325461_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 2, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 2, 1, 1, 3, 6].length) (baseStart_3325461 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3325461 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3325461 prefixEnd_3325461 := by exact prefixLift 3325461
  have htrace : WordTrace (prefixWord ++ tailWord_3325461) baseStart_3325461 baseEnd_3325461 := by
    simpa [prefixWord, tailWord_3325461, baseEnd_3325461] using wordTrace_append hprefix tailTrace_3325461
  have hstable : (prefixWord ++ tailWord_3325461).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3325461).length < 2 ^ (prefixWord ++ tailWord_3325461).sum := by decide
  have hdescent : baseEnd_3325461 < baseStart_3325461 := by decide
  rcases family_descends (prefixWord ++ tailWord_3325461) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3325491 : List Nat := [1, 1, 1, 2, 4, 3, 3, 8]
def baseStart_3325491 : Nat := 118140960795 + 3325491 * 2 ^ 59
def prefixEnd_3325491 : Nat := 4983230072969 + 3 ^ 40 * 3325491 * 2
def baseEnd_3325491 : Nat := 63243529451887175365513

theorem tailTrace_3325491 : CollatzResearch.WordTrace tailWord_3325491 prefixEnd_3325491 63243529451887175365513 := by
  unfold tailWord_3325491
  simp only [CollatzResearch.WordTrace]
  refine ⟨121290621195321530491208327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80860414130214353660805551 121290621195321530491208327)
  ·
    refine ⟨181935931792982295736812491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121290621195321530491208327 181935931792982295736812491)
    ·
      refine ⟨272903897689473443605218737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 181935931792982295736812491 272903897689473443605218737)
      ·
        refine ⟨204677923267105082703914053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 272903897689473443605218737 204677923267105082703914053)
        ·
          refine ⟨38377110612582203006983885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 204677923267105082703914053 38377110612582203006983885)
          ·
            refine ⟨14391416479718326127618957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 38377110612582203006983885 14391416479718326127618957)
            ·
              refine ⟨5396781179894372297857109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14391416479718326127618957 5396781179894372297857109)
              ·
                refine ⟨63243529451887175365513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 5396781179894372297857109 63243529451887175365513)
                ·
                  rfl

theorem cell23_3325491_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 3, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 3, 3, 8].length) (baseStart_3325491 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3325491 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3325491 prefixEnd_3325491 := by exact prefixLift 3325491
  have htrace : WordTrace (prefixWord ++ tailWord_3325491) baseStart_3325491 baseEnd_3325491 := by
    simpa [prefixWord, tailWord_3325491, baseEnd_3325491] using wordTrace_append hprefix tailTrace_3325491
  have hstable : (prefixWord ++ tailWord_3325491).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3325491).length < 2 ^ (prefixWord ++ tailWord_3325491).sum := by decide
  have hdescent : baseEnd_3325491 < baseStart_3325491 := by decide
  rcases family_descends (prefixWord ++ tailWord_3325491) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3325498 : List Nat := [3, 1, 1, 1, 3, 2, 4, 1, 1, 2, 4]
def baseStart_3325498 : Nat := 118140960795 + 3325498 * 2 ^ 59
def prefixEnd_3325498 : Nat := 4983230072969 + 3 ^ 40 * 3325498 * 2
def baseEnd_3325498 : Nat := 1707578889565535207481319

theorem tailTrace_3325498 : CollatzResearch.WordTrace tailWord_3325498 prefixEnd_3325498 1707578889565535207481319 := by
  unfold tailWord_3325498
  simp only [CollatzResearch.WordTrace]
  refine ⟨30322719126574042671678287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 80860584337530780457808765 30322719126574042671678287)
  ·
    refine ⟨45484078689861064007517431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30322719126574042671678287 45484078689861064007517431)
    ·
      refine ⟨68226118034791596011276147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45484078689861064007517431 68226118034791596011276147)
      ·
        refine ⟨102339177052187394016914221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68226118034791596011276147 102339177052187394016914221)
        ·
          refine ⟨38377191394570272756342833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 102339177052187394016914221 38377191394570272756342833)
          ·
            refine ⟨28782893545927704567257125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38377191394570272756342833 28782893545927704567257125)
            ·
              refine ⟨5396792539861444606360711, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 28782893545927704567257125 5396792539861444606360711)
              ·
                refine ⟨8095188809792166909541067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5396792539861444606360711 8095188809792166909541067)
                ·
                  refine ⟨12142783214688250364311601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8095188809792166909541067 12142783214688250364311601)
                  ·
                    refine ⟨9107087411016187773233701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12142783214688250364311601 9107087411016187773233701)
                    ·
                      refine ⟨1707578889565535207481319, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9107087411016187773233701 1707578889565535207481319)
                      ·
                        rfl

theorem cell23_3325498_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 4, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 4, 1, 1, 2, 4].length) (baseStart_3325498 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3325498 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3325498 prefixEnd_3325498 := by exact prefixLift 3325498
  have htrace : WordTrace (prefixWord ++ tailWord_3325498) baseStart_3325498 baseEnd_3325498 := by
    simpa [prefixWord, tailWord_3325498, baseEnd_3325498] using wordTrace_append hprefix tailTrace_3325498
  have hstable : (prefixWord ++ tailWord_3325498).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3325498).length < 2 ^ (prefixWord ++ tailWord_3325498).sum := by decide
  have hdescent : baseEnd_3325498 < baseStart_3325498 := by decide
  rcases family_descends (prefixWord ++ tailWord_3325498) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3325505 : List Nat := [1, 2, 5, 1, 1, 1, 2, 4, 1, 2, 3]
def baseStart_3325505 : Nat := 118140960795 + 3325505 * 2 ^ 59
def prefixEnd_3325505 : Nat := 4983230072969 + 3 ^ 40 * 3325505 * 2
def baseEnd_3325505 : Nat := 1707582483930116680093787

theorem tailTrace_3325505 : CollatzResearch.WordTrace tailWord_3325505 prefixEnd_3325505 1707582483930116680093787 := by
  unfold tailWord_3325505
  simp only [CollatzResearch.WordTrace]
  refine ⟨121291131817270810882217969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80860754544847207254811979 121291131817270810882217969)
  ·
    refine ⟨90968348862953108161663477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 121291131817270810882217969 90968348862953108161663477)
    ·
      refine ⟨8528282705901853890155951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 90968348862953108161663477 8528282705901853890155951)
      ·
        refine ⟨12792424058852780835233927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8528282705901853890155951 12792424058852780835233927)
        ·
          refine ⟨19188636088279171252850891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12792424058852780835233927 19188636088279171252850891)
          ·
            refine ⟨28782954132418756879276337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19188636088279171252850891 28782954132418756879276337)
            ·
              refine ⟨21587215599314067659457253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28782954132418756879276337 21587215599314067659457253)
              ·
                refine ⟨4047602924871387686148235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 21587215599314067659457253 4047602924871387686148235)
                ·
                  refine ⟨6071404387307081529222353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4047602924871387686148235 6071404387307081529222353)
                  ·
                    refine ⟨4553553290480311146916765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6071404387307081529222353 4553553290480311146916765)
                    ·
                      refine ⟨1707582483930116680093787, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4553553290480311146916765 1707582483930116680093787)
                      ·
                        rfl

theorem cell23_3325505_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 2, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 2, 4, 1, 2, 3].length) (baseStart_3325505 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3325505 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3325505 prefixEnd_3325505 := by exact prefixLift 3325505
  have htrace : WordTrace (prefixWord ++ tailWord_3325505) baseStart_3325505 baseEnd_3325505 := by
    simpa [prefixWord, tailWord_3325505, baseEnd_3325505] using wordTrace_append hprefix tailTrace_3325505
  have hstable : (prefixWord ++ tailWord_3325505).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3325505).length < 2 ^ (prefixWord ++ tailWord_3325505).sum := by decide
  have hdescent : baseEnd_3325505 < baseStart_3325505 := by decide
  rcases family_descends (prefixWord ++ tailWord_3325505) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3325522 : List Nat := [3, 2, 2, 1, 2, 2, 4, 1, 1, 2, 3]
def baseStart_3325522 : Nat := 118140960795 + 3325522 * 2 ^ 59
def prefixEnd_3325522 : Nat := 4983230072969 + 3 ^ 40 * 3325522 * 2
def baseEnd_3325522 : Nat := 1707591213101243113581209

theorem tailTrace_3325522 : CollatzResearch.WordTrace tailWord_3325522 prefixEnd_3325522 1707591213101243113581209 := by
  unfold tailWord_3325522
  simp only [CollatzResearch.WordTrace]
  refine ⟨30322937964552305696396705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 80861167905472815190391213 30322937964552305696396705)
  ·
    refine ⟨22742203473414229272297529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30322937964552305696396705 22742203473414229272297529)
    ·
      refine ⟨17056652605060671954223147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22742203473414229272297529 17056652605060671954223147)
      ·
        refine ⟨25584978907591007931334721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17056652605060671954223147 25584978907591007931334721)
        ·
          refine ⟨19188734180693255948501041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25584978907591007931334721 19188734180693255948501041)
          ·
            refine ⟨14391550635519941961375781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19188734180693255948501041 14391550635519941961375781)
            ·
              refine ⟨2698415744159989117757959, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 14391550635519941961375781 2698415744159989117757959)
              ·
                refine ⟨4047623616239983676636939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2698415744159989117757959 4047623616239983676636939)
                ·
                  refine ⟨6071435424359975514955409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4047623616239983676636939 6071435424359975514955409)
                  ·
                    refine ⟨4553576568269981636216557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6071435424359975514955409 4553576568269981636216557)
                    ·
                      refine ⟨1707591213101243113581209, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4553576568269981636216557 1707591213101243113581209)
                      ·
                        rfl

theorem cell23_3325522_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 2, 4, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 2, 4, 1, 1, 2, 3].length) (baseStart_3325522 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3325522 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3325522 prefixEnd_3325522 := by exact prefixLift 3325522
  have htrace : WordTrace (prefixWord ++ tailWord_3325522) baseStart_3325522 baseEnd_3325522 := by
    simpa [prefixWord, tailWord_3325522, baseEnd_3325522] using wordTrace_append hprefix tailTrace_3325522
  have hstable : (prefixWord ++ tailWord_3325522).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3325522).length < 2 ^ (prefixWord ++ tailWord_3325522).sum := by decide
  have hdescent : baseEnd_3325522 < baseStart_3325522 := by decide
  rcases family_descends (prefixWord ++ tailWord_3325522) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3325578 : List Nat := [3, 1, 2, 3, 2, 1, 1, 1, 1, 3, 5]
def baseStart_3325578 : Nat := 118140960795 + 3325578 * 2 ^ 59
def prefixEnd_3325578 : Nat := 4983230072969 + 3 ^ 40 * 3325578 * 2
def baseEnd_3325578 : Nat := 1707619968017894894480951

theorem tailTrace_3325578 : CollatzResearch.WordTrace tailWord_3325578 prefixEnd_3325578 1707619968017894894480951 := by
  unfold tailWord_3325578
  simp only [CollatzResearch.WordTrace]
  refine ⟨30323448586501586087406347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 80862529564004229566416925 30323448586501586087406347)
  ·
    refine ⟨45485172879752379131109521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30323448586501586087406347 45485172879752379131109521)
    ·
      refine ⟨34113879659814284348332141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45485172879752379131109521 34113879659814284348332141)
      ·
        refine ⟨12792704872430356630624553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 34113879659814284348332141 12792704872430356630624553)
        ·
          refine ⟨9594528654322767472968415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12792704872430356630624553 9594528654322767472968415)
          ·
            refine ⟨14391792981484151209452623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9594528654322767472968415 14391792981484151209452623)
            ·
              refine ⟨21587689472226226814178935, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14391792981484151209452623 21587689472226226814178935)
              ·
                refine ⟨32381534208339340221268403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21587689472226226814178935 32381534208339340221268403)
                ·
                  refine ⟨48572301312509010331902605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32381534208339340221268403 48572301312509010331902605)
                  ·
                    refine ⟨18214612992190878874463477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 48572301312509010331902605 18214612992190878874463477)
                    ·
                      refine ⟨1707619968017894894480951, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 18214612992190878874463477 1707619968017894894480951)
                      ·
                        rfl

theorem cell23_3325578_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 1, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 1, 1, 1, 1, 3, 5].length) (baseStart_3325578 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3325578 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3325578 prefixEnd_3325578 := by exact prefixLift 3325578
  have htrace : WordTrace (prefixWord ++ tailWord_3325578) baseStart_3325578 baseEnd_3325578 := by
    simpa [prefixWord, tailWord_3325578, baseEnd_3325578] using wordTrace_append hprefix tailTrace_3325578
  have hstable : (prefixWord ++ tailWord_3325578).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3325578).length < 2 ^ (prefixWord ++ tailWord_3325578).sum := by decide
  have hdescent : baseEnd_3325578 < baseStart_3325578 := by decide
  rcases family_descends (prefixWord ++ tailWord_3325578) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3325592 : List Nat := [2, 1, 2, 4, 1, 2, 2, 1, 4, 2, 2]
def baseStart_3325592 : Nat := 118140960795 + 3325592 * 2 ^ 59
def prefixEnd_3325592 : Nat := 4983230072969 + 3 ^ 40 * 3325592 * 2
def baseEnd_3325592 : Nat := 1707627156747057839705887

theorem tailTrace_3325592 : CollatzResearch.WordTrace tailWord_3325592 prefixEnd_3325592 1707627156747057839705887 := by
  unfold tailWord_3325592
  simp only [CollatzResearch.WordTrace]
  refine ⟨60647152483977812370317515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80862869978637083160423353 60647152483977812370317515)
  ·
    refine ⟨90970728725966718555476273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60647152483977812370317515 90970728725966718555476273)
    ·
      refine ⟨68228046544475038916607205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 90970728725966718555476273 68228046544475038916607205)
      ·
        refine ⟨12792758727089069796863851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 68228046544475038916607205 12792758727089069796863851)
        ·
          refine ⟨19189138090633604695295777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12792758727089069796863851 19189138090633604695295777)
          ·
            refine ⟨14391853567975203521471833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19189138090633604695295777 14391853567975203521471833)
            ·
              refine ⟨10793890175981402641103875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14391853567975203521471833 10793890175981402641103875)
              ·
                refine ⟨16190835263972103961655813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10793890175981402641103875 16190835263972103961655813)
                ·
                  refine ⟨3035781611994769492810465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 16190835263972103961655813 3035781611994769492810465)
                  ·
                    refine ⟨2276836208996077119607849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3035781611994769492810465 2276836208996077119607849)
                    ·
                      refine ⟨1707627156747057839705887, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2276836208996077119607849 1707627156747057839705887)
                      ·
                        rfl

theorem cell23_3325592_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 2, 2, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 2, 2, 1, 4, 2, 2].length) (baseStart_3325592 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3325592 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3325592 prefixEnd_3325592 := by exact prefixLift 3325592
  have htrace : WordTrace (prefixWord ++ tailWord_3325592) baseStart_3325592 baseEnd_3325592 := by
    simpa [prefixWord, tailWord_3325592, baseEnd_3325592] using wordTrace_append hprefix tailTrace_3325592
  have hstable : (prefixWord ++ tailWord_3325592).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3325592).length < 2 ^ (prefixWord ++ tailWord_3325592).sum := by decide
  have hdescent : baseEnd_3325592 < baseStart_3325592 := by decide
  rcases family_descends (prefixWord ++ tailWord_3325592) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3325648 : List Nat := [2, 1, 1, 1, 1, 2, 1, 5, 4, 1, 4]
def baseStart_3325648 : Nat := 118140960795 + 3325648 * 2 ^ 59
def prefixEnd_3325648 : Nat := 4983230072969 + 3 ^ 40 * 3325648 * 2
def baseEnd_3325648 : Nat := 1707655911663709620605629

theorem tailTrace_3325648 : CollatzResearch.WordTrace tailWord_3325648 prefixEnd_3325648 1707655911663709620605629 := by
  unfold tailWord_3325648
  simp only [CollatzResearch.WordTrace]
  refine ⟨60648173727876373152336799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80864231637168497536449065 60648173727876373152336799)
  ·
    refine ⟨90972260591814559728505199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60648173727876373152336799 90972260591814559728505199)
    ·
      refine ⟨136458390887721839592757799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90972260591814559728505199 136458390887721839592757799)
      ·
        refine ⟨204687586331582759389136699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 136458390887721839592757799 204687586331582759389136699)
        ·
          refine ⟨307031379497374139083705049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 204687586331582759389136699 307031379497374139083705049)
          ·
            refine ⟨230273534623030604312778787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 307031379497374139083705049 230273534623030604312778787)
            ·
              refine ⟨345410301934545906469168181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 230273534623030604312778787 345410301934545906469168181)
              ·
                refine ⟨32382215806363678731484517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 345410301934545906469168181 32382215806363678731484517)
                ·
                  refine ⟨6071665463693189762153347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 32382215806363678731484517 6071665463693189762153347)
                  ·
                    refine ⟨9107498195539784643230021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6071665463693189762153347 9107498195539784643230021)
                    ·
                      refine ⟨1707655911663709620605629, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9107498195539784643230021 1707655911663709620605629)
                      ·
                        rfl

theorem cell23_3325648_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 5, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 5, 4, 1, 4].length) (baseStart_3325648 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3325648 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3325648 prefixEnd_3325648 := by exact prefixLift 3325648
  have htrace : WordTrace (prefixWord ++ tailWord_3325648) baseStart_3325648 baseEnd_3325648 := by
    simpa [prefixWord, tailWord_3325648, baseEnd_3325648] using wordTrace_append hprefix tailTrace_3325648
  have hstable : (prefixWord ++ tailWord_3325648).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3325648).length < 2 ^ (prefixWord ++ tailWord_3325648).sum := by decide
  have hdescent : baseEnd_3325648 < baseStart_3325648 := by decide
  rcases family_descends (prefixWord ++ tailWord_3325648) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3325652 : List Nat := [2, 4, 1, 3, 1, 1, 1, 1, 2, 5, 2]
def baseStart_3325652 : Nat := 118140960795 + 3325652 * 2 ^ 59
def prefixEnd_3325652 : Nat := 4983230072969 + 3 ^ 40 * 3325652 * 2
def baseEnd_3325652 : Nat := 1707657965586327604955611

theorem tailTrace_3325652 : CollatzResearch.WordTrace tailWord_3325652 prefixEnd_3325652 1707657965586327604955611 := by
  unfold tailWord_3325652
  simp only [CollatzResearch.WordTrace]
  refine ⟨60648246673869127493909605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80864328898492169991879473 60648246673869127493909605)
  ·
    refine ⟨11371546251350461405108051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 60648246673869127493909605 11371546251350461405108051)
    ·
      refine ⟨17057319377025692107662077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11371546251350461405108051 17057319377025692107662077)
      ·
        refine ⟨6396494766384634540373279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17057319377025692107662077 6396494766384634540373279)
        ·
          refine ⟨9594742149576951810559919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6396494766384634540373279 9594742149576951810559919)
          ·
            refine ⟨14392113224365427715839879, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9594742149576951810559919 14392113224365427715839879)
            ·
              refine ⟨21588169836548141573759819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14392113224365427715839879 21588169836548141573759819)
              ·
                refine ⟨32382254754822212360639729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21588169836548141573759819 32382254754822212360639729)
                ·
                  refine ⟨24286691066116659270479797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32382254754822212360639729 24286691066116659270479797)
                  ·
                    refine ⟨2276877287448436806607481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 24286691066116659270479797 2276877287448436806607481)
                    ·
                      refine ⟨1707657965586327604955611, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2276877287448436806607481 1707657965586327604955611)
                      ·
                        rfl

theorem cell23_3325652_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 1, 1, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 1, 1, 1, 2, 5, 2].length) (baseStart_3325652 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3325652 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3325652 prefixEnd_3325652 := by exact prefixLift 3325652
  have htrace : WordTrace (prefixWord ++ tailWord_3325652) baseStart_3325652 baseEnd_3325652 := by
    simpa [prefixWord, tailWord_3325652, baseEnd_3325652] using wordTrace_append hprefix tailTrace_3325652
  have hstable : (prefixWord ++ tailWord_3325652).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3325652).length < 2 ^ (prefixWord ++ tailWord_3325652).sum := by decide
  have hdescent : baseEnd_3325652 < baseStart_3325652 := by decide
  rcases family_descends (prefixWord ++ tailWord_3325652) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3325708 : List Nat := [2, 2, 1, 2, 2, 1, 3, 1, 1, 2, 6]
def baseStart_3325708 : Nat := 118140960795 + 3325708 * 2 ^ 59
def prefixEnd_3325708 : Nat := 4983230072969 + 3 ^ 40 * 3325708 * 2
def baseEnd_3325708 : Nat := 1707686720502979385855353

theorem tailTrace_3325708 : CollatzResearch.WordTrace tailWord_3325708 prefixEnd_3325708 1707686720502979385855353 := by
  unfold tailWord_3325708
  simp only [CollatzResearch.WordTrace]
  refine ⟨60649267917767688275928889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80865690557023584367905185 60649267917767688275928889)
  ·
    refine ⟨45486950938325766206946667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60649267917767688275928889 45486950938325766206946667)
    ·
      refine ⟨68230426407488649310420001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45486950938325766206946667 68230426407488649310420001)
      ·
        refine ⟨51172819805616486982815001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 68230426407488649310420001 51172819805616486982815001)
        ·
          refine ⟨38379614854212365237111251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51172819805616486982815001 38379614854212365237111251)
          ·
            refine ⟨57569422281318547855666877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38379614854212365237111251 57569422281318547855666877)
            ·
              refine ⟨21588533355494455445875079, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 57569422281318547855666877 21588533355494455445875079)
              ·
                refine ⟨32382800033241683168812619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21588533355494455445875079 32382800033241683168812619)
                ·
                  refine ⟨48574200049862524753218929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32382800033241683168812619 48574200049862524753218929)
                  ·
                    refine ⟨36430650037396893564914197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 48574200049862524753218929 36430650037396893564914197)
                    ·
                      refine ⟨1707686720502979385855353, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 36430650037396893564914197 1707686720502979385855353)
                      ·
                        rfl

theorem cell23_3325708_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 3, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 3, 1, 1, 2, 6].length) (baseStart_3325708 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3325708 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3325708 prefixEnd_3325708 := by exact prefixLift 3325708
  have htrace : WordTrace (prefixWord ++ tailWord_3325708) baseStart_3325708 baseEnd_3325708 := by
    simpa [prefixWord, tailWord_3325708, baseEnd_3325708] using wordTrace_append hprefix tailTrace_3325708
  have hstable : (prefixWord ++ tailWord_3325708).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3325708).length < 2 ^ (prefixWord ++ tailWord_3325708).sum := by decide
  have hdescent : baseEnd_3325708 < baseStart_3325708 := by decide
  rcases family_descends (prefixWord ++ tailWord_3325708) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3325722 : List Nat := [3, 1, 1, 3, 2, 3, 3, 1, 6]
def baseStart_3325722 : Nat := 118140960795 + 3325722 * 2 ^ 59
def prefixEnd_3325722 : Nat := 4983230072969 + 3 ^ 40 * 3325722 * 2
def baseEnd_3325722 : Nat := 189743767692460259008921

theorem tailTrace_3325722 : CollatzResearch.WordTrace tailWord_3325722 prefixEnd_3325722 189743767692460259008921 := by
  unfold tailWord_3325722
  simp only [CollatzResearch.WordTrace]
  refine ⟨30324761614371164235716855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 80866030971656437961911613 30324761614371164235716855)
  ·
    refine ⟨45487142421556746353575283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30324761614371164235716855 45487142421556746353575283)
    ·
      refine ⟨68230713632335119530362925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45487142421556746353575283 68230713632335119530362925)
      ·
        refine ⟨25586517612125669823886097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 68230713632335119530362925 25586517612125669823886097)
        ·
          refine ⟨19189888209094252367914573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25586517612125669823886097 19189888209094252367914573)
          ·
            refine ⟨7196208078410344637967965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19189888209094252367914573 7196208078410344637967965)
            ·
              refine ⟨2698578029403879239237987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7196208078410344637967965 2698578029403879239237987)
              ·
                refine ⟨4047867044105818858856981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2698578029403879239237987 4047867044105818858856981)
                ·
                  refine ⟨189743767692460259008921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4047867044105818858856981 189743767692460259008921)
                  ·
                    rfl

theorem cell23_3325722_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 3, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 3, 3, 1, 6].length) (baseStart_3325722 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3325722 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3325722 prefixEnd_3325722 := by exact prefixLift 3325722
  have htrace : WordTrace (prefixWord ++ tailWord_3325722) baseStart_3325722 baseEnd_3325722 := by
    simpa [prefixWord, tailWord_3325722, baseEnd_3325722] using wordTrace_append hprefix tailTrace_3325722
  have hstable : (prefixWord ++ tailWord_3325722).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3325722).length < 2 ^ (prefixWord ++ tailWord_3325722).sum := by decide
  have hdescent : baseEnd_3325722 < baseStart_3325722 := by decide
  rcases family_descends (prefixWord ++ tailWord_3325722) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3325759 : List Nat := [1, 1, 2, 2, 6, 1, 1, 2, 2, 3, 2]
def baseStart_3325759 : Nat := 118140960795 + 3325759 * 2 ^ 59
def prefixEnd_3325759 : Nat := 4983230072969 + 3 ^ 40 * 3325759 * 2
def baseEnd_3325759 : Nat := 1707712908016358686317619

theorem tailTrace_3325759 : CollatzResearch.WordTrace tailWord_3325759 prefixEnd_3325759 1707712908016358686317619 := by
  unfold tailWord_3325759
  simp only [CollatzResearch.WordTrace]
  refine ⟨121300395958350612261964331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80866930638900408174642887 121300395958350612261964331)
  ·
    refine ⟨181950593937525918392946497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121300395958350612261964331 181950593937525918392946497)
    ·
      refine ⟨136462945453144438794709873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 181950593937525918392946497 136462945453144438794709873)
      ·
        refine ⟨102347209089858329096032405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 136462945453144438794709873 102347209089858329096032405)
        ·
          refine ⟨4797525426087109176376519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 102347209089858329096032405 4797525426087109176376519)
          ·
            refine ⟨7196288139130663764564779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4797525426087109176376519 7196288139130663764564779)
            ·
              refine ⟨10794432208695995646847169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7196288139130663764564779 10794432208695995646847169)
              ·
                refine ⟨8095824156521996735135377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10794432208695995646847169 8095824156521996735135377)
                ·
                  refine ⟨6071868117391497551351533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8095824156521996735135377 6071868117391497551351533)
                  ·
                    refine ⟨2276950544021811581756825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6071868117391497551351533 2276950544021811581756825)
                    ·
                      refine ⟨1707712908016358686317619, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2276950544021811581756825 1707712908016358686317619)
                      ·
                        rfl

theorem cell23_3325759_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 6, 1, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 6, 1, 1, 2, 2, 3, 2].length) (baseStart_3325759 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3325759 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3325759 prefixEnd_3325759 := by exact prefixLift 3325759
  have htrace : WordTrace (prefixWord ++ tailWord_3325759) baseStart_3325759 baseEnd_3325759 := by
    simpa [prefixWord, tailWord_3325759, baseEnd_3325759] using wordTrace_append hprefix tailTrace_3325759
  have hstable : (prefixWord ++ tailWord_3325759).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3325759).length < 2 ^ (prefixWord ++ tailWord_3325759).sum := by decide
  have hdescent : baseEnd_3325759 < baseStart_3325759 := by decide
  rcases family_descends (prefixWord ++ tailWord_3325759) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3325765 : List Nat := [1, 3, 1, 1, 1, 2, 3, 3, 4, 4]
def baseStart_3325765 : Nat := 118140960795 + 3325765 * 2 ^ 59
def prefixEnd_3325765 : Nat := 4983230072969 + 3 ^ 40 * 3325765 * 2
def baseEnd_3325765 : Nat := 569238662966761887614197

theorem tailTrace_3325765 : CollatzResearch.WordTrace tailWord_3325765 prefixEnd_3325765 569238662966761887614197 := by
  unfold tailWord_3325765
  simp only [CollatzResearch.WordTrace]
  refine ⟨121300614796328875286682749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80867076530885916857788499 121300614796328875286682749)
  ·
    refine ⟨45487730548623328232506031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 121300614796328875286682749 45487730548623328232506031)
    ·
      refine ⟨68231595822934992348759047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45487730548623328232506031 68231595822934992348759047)
      ·
        refine ⟨102347393734402488523138571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68231595822934992348759047 102347393734402488523138571)
        ·
          refine ⟨153521090601603732784707857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 102347393734402488523138571 153521090601603732784707857)
          ·
            refine ⟨115140817951202799588530893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 153521090601603732784707857 115140817951202799588530893)
            ·
              refine ⟨43177806731701049845699085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 115140817951202799588530893 43177806731701049845699085)
              ·
                refine ⟨16191677524387893692137157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 43177806731701049845699085 16191677524387893692137157)
                ·
                  refine ⟨3035939535822730067275717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 16191677524387893692137157 3035939535822730067275717)
                  ·
                    refine ⟨569238662966761887614197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3035939535822730067275717 569238662966761887614197)
                    ·
                      rfl

theorem cell23_3325765_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 3, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 3, 3, 4, 4].length) (baseStart_3325765 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3325765 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3325765 prefixEnd_3325765 := by exact prefixLift 3325765
  have htrace : WordTrace (prefixWord ++ tailWord_3325765) baseStart_3325765 baseEnd_3325765 := by
    simpa [prefixWord, tailWord_3325765, baseEnd_3325765] using wordTrace_append hprefix tailTrace_3325765
  have hstable : (prefixWord ++ tailWord_3325765).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3325765).length < 2 ^ (prefixWord ++ tailWord_3325765).sum := by decide
  have hdescent : baseEnd_3325765 < baseStart_3325765 := by decide
  rcases family_descends (prefixWord ++ tailWord_3325765) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3325785 : List Nat := [1, 2, 1, 2, 2, 3, 2, 3, 1, 2, 4]
def baseStart_3325785 : Nat := 118140960795 + 3325785 * 2 ^ 59
def prefixEnd_3325785 : Nat := 4983230072969 + 3 ^ 40 * 3325785 * 2
def baseEnd_3325785 : Nat := 1707726258513375584592499

theorem tailTrace_3325785 : CollatzResearch.WordTrace tailWord_3325785 prefixEnd_3325785 1707726258513375584592499 := by
  unfold tailWord_3325785
  simp only [CollatzResearch.WordTrace]
  refine ⟨121301344256256418702410809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80867562837504279134940539 121301344256256418702410809)
  ·
    refine ⟨90976008192192314026808107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 121301344256256418702410809 90976008192192314026808107)
    ·
      refine ⟨136464012288288471040212161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90976008192192314026808107 136464012288288471040212161)
      ·
        refine ⟨102348009216216353280159121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 136464012288288471040212161 102348009216216353280159121)
        ·
          refine ⟨76761006912162264960119341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 102348009216216353280159121 76761006912162264960119341)
          ·
            refine ⟨28785377592060849360044753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 76761006912162264960119341 28785377592060849360044753)
            ·
              refine ⟨21589033194045637020033565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28785377592060849360044753 21589033194045637020033565)
              ·
                refine ⟨8095887447767113882512587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21589033194045637020033565 8095887447767113882512587)
                ·
                  refine ⟨12143831171650670823768881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8095887447767113882512587 12143831171650670823768881)
                  ·
                    refine ⟨9107873378738003117826661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12143831171650670823768881 9107873378738003117826661)
                    ·
                      refine ⟨1707726258513375584592499, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9107873378738003117826661 1707726258513375584592499)
                      ·
                        rfl

theorem cell23_3325785_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 2, 3, 1, 2, 4].length) (baseStart_3325785 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3325785 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3325785 prefixEnd_3325785 := by exact prefixLift 3325785
  have htrace : WordTrace (prefixWord ++ tailWord_3325785) baseStart_3325785 baseEnd_3325785 := by
    simpa [prefixWord, tailWord_3325785, baseEnd_3325785] using wordTrace_append hprefix tailTrace_3325785
  have hstable : (prefixWord ++ tailWord_3325785).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3325785).length < 2 ^ (prefixWord ++ tailWord_3325785).sum := by decide
  have hdescent : baseEnd_3325785 < baseStart_3325785 := by decide
  rcases family_descends (prefixWord ++ tailWord_3325785) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3325792 : List Nat := [2, 1, 1, 3, 3, 3, 1, 1, 3, 2, 3]
def baseStart_3325792 : Nat := 118140960795 + 3325792 * 2 ^ 59
def prefixEnd_3325792 : Nat := 4983230072969 + 3 ^ 40 * 3325792 * 2
def baseEnd_3325792 : Nat := 1707729852877957057204967

theorem tailTrace_3325792 : CollatzResearch.WordTrace tailWord_3325792 prefixEnd_3325792 1707729852877957057204967 := by
  unfold tailWord_3325792
  simp only [CollatzResearch.WordTrace]
  refine ⟨60650799783615529448957815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80867733044820705931943753 60650799783615529448957815)
  ·
    refine ⟨90976199675423294173436723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60650799783615529448957815 90976199675423294173436723)
    ·
      refine ⟨136464299513134941260155085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90976199675423294173436723 136464299513134941260155085)
      ·
        refine ⟨51174112317425602972558157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 136464299513134941260155085 51174112317425602972558157)
        ·
          refine ⟨19190292119034601114709309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 51174112317425602972558157 19190292119034601114709309)
          ·
            refine ⟨7196359544637975418015991, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19190292119034601114709309 7196359544637975418015991)
            ·
              refine ⟨10794539316956963127023987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7196359544637975418015991 10794539316956963127023987)
              ·
                refine ⟨16191808975435444690535981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10794539316956963127023987 16191808975435444690535981)
                ·
                  refine ⟨6071928365788291758950993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16191808975435444690535981 6071928365788291758950993)
                  ·
                    refine ⟨4553946274341218819213245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6071928365788291758950993 4553946274341218819213245)
                    ·
                      refine ⟨1707729852877957057204967, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4553946274341218819213245 1707729852877957057204967)
                      ·
                        rfl

theorem cell23_3325792_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 3, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 3, 1, 1, 3, 2, 3].length) (baseStart_3325792 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3325792 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3325792 prefixEnd_3325792 := by exact prefixLift 3325792
  have htrace : WordTrace (prefixWord ++ tailWord_3325792) baseStart_3325792 baseEnd_3325792 := by
    simpa [prefixWord, tailWord_3325792, baseEnd_3325792] using wordTrace_append hprefix tailTrace_3325792
  have hstable : (prefixWord ++ tailWord_3325792).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3325792).length < 2 ^ (prefixWord ++ tailWord_3325792).sum := by decide
  have hdescent : baseEnd_3325792 < baseStart_3325792 := by decide
  rcases family_descends (prefixWord ++ tailWord_3325792) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3325806 : List Nat := [4, 1, 2, 3, 1, 2, 3, 1, 1, 1, 4]
def baseStart_3325806 : Nat := 118140960795 + 3325806 * 2 ^ 59
def prefixEnd_3325806 : Nat := 4983230072969 + 3 ^ 40 * 3325806 * 2
def baseEnd_3325806 : Nat := 1707737041607120002429903

theorem tailTrace_3325806 : CollatzResearch.WordTrace tailWord_3325806 prefixEnd_3325806 1707737041607120002429903 := by
  unfold tailWord_3325806
  simp only [CollatzResearch.WordTrace]
  refine ⟨15162763773647542411115659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 80868073459453559525950181 15162763773647542411115659)
  ·
    refine ⟨22744145660471313616673489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15162763773647542411115659 22744145660471313616673489)
    ·
      refine ⟨17058109245353485212505117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22744145660471313616673489 17058109245353485212505117)
      ·
        refine ⟨6396790967007556954689419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17058109245353485212505117 6396790967007556954689419)
        ·
          refine ⟨9595186450511335432034129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6396790967007556954689419 9595186450511335432034129)
          ·
            refine ⟨7196389837883501574025597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9595186450511335432034129 7196389837883501574025597)
            ·
              refine ⟨2698646189206313090259599, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7196389837883501574025597 2698646189206313090259599)
              ·
                refine ⟨4047969283809469635389399, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2698646189206313090259599 4047969283809469635389399)
                ·
                  refine ⟨6071953925714204453084099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4047969283809469635389399 6071953925714204453084099)
                  ·
                    refine ⟨9107930888571306679626149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6071953925714204453084099 9107930888571306679626149)
                    ·
                      refine ⟨1707737041607120002429903, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9107930888571306679626149 1707737041607120002429903)
                      ·
                        rfl

theorem cell23_3325806_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 2, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 2, 3, 1, 1, 1, 4].length) (baseStart_3325806 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3325806 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3325806 prefixEnd_3325806 := by exact prefixLift 3325806
  have htrace : WordTrace (prefixWord ++ tailWord_3325806) baseStart_3325806 baseEnd_3325806 := by
    simpa [prefixWord, tailWord_3325806, baseEnd_3325806] using wordTrace_append hprefix tailTrace_3325806
  have hstable : (prefixWord ++ tailWord_3325806).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3325806).length < 2 ^ (prefixWord ++ tailWord_3325806).sum := by decide
  have hdescent : baseEnd_3325806 < baseStart_3325806 := by decide
  rcases family_descends (prefixWord ++ tailWord_3325806) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3325809 : List Nat := [1, 2, 2, 2, 1, 3, 5, 1, 1, 2, 3]
def baseStart_3325809 : Nat := 118140960795 + 3325809 * 2 ^ 59
def prefixEnd_3325809 : Nat := 4983230072969 + 3 ^ 40 * 3325809 * 2
def baseEnd_3325809 : Nat := 1707738582049083490692389

theorem tailTrace_3325809 : CollatzResearch.WordTrace tailWord_3325809 prefixEnd_3325809 1707738582049083490692389 := by
  unfold tailWord_3325809
  simp only [CollatzResearch.WordTrace]
  refine ⟨121302219608169470801284481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80868146405446313867522987 121302219608169470801284481)
  ·
    refine ⟨90976664706127103100963361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 121302219608169470801284481 90976664706127103100963361)
    ·
      refine ⟨68232498529595327325722521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 90976664706127103100963361 68232498529595327325722521)
      ·
        refine ⟨51174373897196495494291891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 68232498529595327325722521 51174373897196495494291891)
        ·
          refine ⟨76761560845794743241437837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51174373897196495494291891 76761560845794743241437837)
          ·
            refine ⟨28785585317173028715539189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 76761560845794743241437837 28785585317173028715539189)
            ·
              refine ⟨2698648623484971442081799, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 28785585317173028715539189 2698648623484971442081799)
              ·
                refine ⟨4047972935227457163122699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2698648623484971442081799 4047972935227457163122699)
                ·
                  refine ⟨6071959402841185744684049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4047972935227457163122699 6071959402841185744684049)
                  ·
                    refine ⟨4553969552130889308513037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6071959402841185744684049 4553969552130889308513037)
                    ·
                      refine ⟨1707738582049083490692389, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4553969552130889308513037 1707738582049083490692389)
                      ·
                        rfl

theorem cell23_3325809_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 5, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 5, 1, 1, 2, 3].length) (baseStart_3325809 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3325809 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3325809 prefixEnd_3325809 := by exact prefixLift 3325809
  have htrace : WordTrace (prefixWord ++ tailWord_3325809) baseStart_3325809 baseEnd_3325809 := by
    simpa [prefixWord, tailWord_3325809, baseEnd_3325809] using wordTrace_append hprefix tailTrace_3325809
  have hstable : (prefixWord ++ tailWord_3325809).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3325809).length < 2 ^ (prefixWord ++ tailWord_3325809).sum := by decide
  have hdescent : baseEnd_3325809 < baseStart_3325809 := by decide
  rcases family_descends (prefixWord ++ tailWord_3325809) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3325845 : List Nat := [1, 3, 2, 1, 1, 3, 1, 2, 2, 3, 4]
def baseStart_3325845 : Nat := 118140960795 + 3325845 * 2 ^ 59
def prefixEnd_3325845 : Nat := 4983230072969 + 3 ^ 40 * 3325845 * 2
def baseEnd_3325845 : Nat := 1707757067352645349842223

theorem tailTrace_3325845 : CollatzResearch.WordTrace tailWord_3325845 prefixEnd_3325845 1707757067352645349842223 := by
  unfold tailWord_3325845
  simp only [CollatzResearch.WordTrace]
  refine ⟨121303532636039048949594989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80869021757359365966396659 121303532636039048949594989)
  ·
    refine ⟨45488824738514643356098121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 121303532636039048949594989 45488824738514643356098121)
    ·
      refine ⟨34116618553885982517073591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45488824738514643356098121 34116618553885982517073591)
      ·
        refine ⟨51174927830828973775610387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34116618553885982517073591 51174927830828973775610387)
        ·
          refine ⟨76762391746243460663415581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51174927830828973775610387 76762391746243460663415581)
          ·
            refine ⟨28785896904841297748780843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 76762391746243460663415581 28785896904841297748780843)
            ·
              refine ⟨43178845357261946623171265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28785896904841297748780843 43178845357261946623171265)
              ·
                refine ⟨32384134017946459967378449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 43178845357261946623171265 32384134017946459967378449)
                ·
                  refine ⟨24288100513459844975533837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32384134017946459967378449 24288100513459844975533837)
                  ·
                    refine ⟨9108037692547441865825189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 24288100513459844975533837 9108037692547441865825189)
                    ·
                      refine ⟨1707757067352645349842223, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9108037692547441865825189 1707757067352645349842223)
                      ·
                        rfl

theorem cell23_3325845_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 1, 2, 2, 3, 4].length) (baseStart_3325845 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3325845 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3325845 prefixEnd_3325845 := by exact prefixLift 3325845
  have htrace : WordTrace (prefixWord ++ tailWord_3325845) baseStart_3325845 baseEnd_3325845 := by
    simpa [prefixWord, tailWord_3325845, baseEnd_3325845] using wordTrace_append hprefix tailTrace_3325845
  have hstable : (prefixWord ++ tailWord_3325845).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3325845).length < 2 ^ (prefixWord ++ tailWord_3325845).sum := by decide
  have hdescent : baseEnd_3325845 < baseStart_3325845 := by decide
  rcases family_descends (prefixWord ++ tailWord_3325845) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3325865 : List Nat := [1, 2, 1, 1, 1, 1, 4, 2, 1, 6, 3]
def baseStart_3325865 : Nat := 118140960795 + 3325865 * 2 ^ 59
def prefixEnd_3325865 : Nat := 4983230072969 + 3 ^ 40 * 3325865 * 2
def baseEnd_3325865 : Nat := 1707767336965735271592131

theorem tailTrace_3325865 : CollatzResearch.WordTrace tailWord_3325865 prefixEnd_3325865 1707767336965735271592131 := by
  unfold tailWord_3325865
  simp only [CollatzResearch.WordTrace]
  refine ⟨121304262095966592365323049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80869508063977728243548699 121304262095966592365323049)
  ·
    refine ⟨90978196571974944273992287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 121304262095966592365323049 90978196571974944273992287)
    ·
      refine ⟨136467294857962416410988431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90978196571974944273992287 136467294857962416410988431)
      ·
        refine ⟨204700942286943624616482647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 136467294857962416410988431 204700942286943624616482647)
        ·
          refine ⟨307051413430415436924723971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 204700942286943624616482647 307051413430415436924723971)
          ·
            refine ⟨460577120145623155387085957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 307051413430415436924723971 460577120145623155387085957)
            ·
              refine ⟨86358210027304341635078617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 460577120145623155387085957 86358210027304341635078617)
              ·
                refine ⟨64768657520478256226308963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 86358210027304341635078617 64768657520478256226308963)
                ·
                  refine ⟨97152986280717384339463445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 64768657520478256226308963 97152986280717384339463445)
                  ·
                    refine ⟨4554046231908627390912349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 97152986280717384339463445 4554046231908627390912349)
                    ·
                      refine ⟨1707767336965735271592131, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4554046231908627390912349 1707767336965735271592131)
                      ·
                        rfl

theorem cell23_3325865_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 4, 2, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 4, 2, 1, 6, 3].length) (baseStart_3325865 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3325865 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3325865 prefixEnd_3325865 := by exact prefixLift 3325865
  have htrace : WordTrace (prefixWord ++ tailWord_3325865) baseStart_3325865 baseEnd_3325865 := by
    simpa [prefixWord, tailWord_3325865, baseEnd_3325865] using wordTrace_append hprefix tailTrace_3325865
  have hstable : (prefixWord ++ tailWord_3325865).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3325865).length < 2 ^ (prefixWord ++ tailWord_3325865).sum := by decide
  have hdescent : baseEnd_3325865 < baseStart_3325865 := by decide
  rcases family_descends (prefixWord ++ tailWord_3325865) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3325875 : List Nat := [1, 1, 1, 2, 3, 1, 3, 1, 4, 2, 4]
def baseStart_3325875 : Nat := 118140960795 + 3325875 * 2 ^ 59
def prefixEnd_3325875 : Nat := 4983230072969 + 3 ^ 40 * 3325875 * 2
def baseEnd_3325875 : Nat := 1707772471772280232467085

theorem tailTrace_3325875 : CollatzResearch.WordTrace tailWord_3325875 prefixEnd_3325875 1707772471772280232467085 := by
  unfold tailWord_3325875
  simp only [CollatzResearch.WordTrace]
  refine ⟨121304626825930364073187079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80869751217286909382124719 121304626825930364073187079)
  ·
    refine ⟨181956940238895546109780619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121304626825930364073187079 181956940238895546109780619)
    ·
      refine ⟨272935410358343319164670929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 181956940238895546109780619 272935410358343319164670929)
      ·
        refine ⟨204701557768757489373503197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 272935410358343319164670929 204701557768757489373503197)
        ·
          refine ⟨76763084163284058515063699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 204701557768757489373503197 76763084163284058515063699)
          ·
            refine ⟨115144626244926087772595549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 76763084163284058515063699 115144626244926087772595549)
            ·
              refine ⟨43179234841847282914723331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 115144626244926087772595549 43179234841847282914723331)
              ·
                refine ⟨64768852262770924372084997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43179234841847282914723331 64768852262770924372084997)
                ·
                  refine ⟨12144159799269548319765937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 64768852262770924372084997 12144159799269548319765937)
                  ·
                    refine ⟨9108119849452161239824453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12144159799269548319765937 9108119849452161239824453)
                    ·
                      refine ⟨1707772471772280232467085, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9108119849452161239824453 1707772471772280232467085)
                      ·
                        rfl

theorem cell23_3325875_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 3, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 3, 1, 4, 2, 4].length) (baseStart_3325875 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3325875 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3325875 prefixEnd_3325875 := by exact prefixLift 3325875
  have htrace : WordTrace (prefixWord ++ tailWord_3325875) baseStart_3325875 baseEnd_3325875 := by
    simpa [prefixWord, tailWord_3325875, baseEnd_3325875] using wordTrace_append hprefix tailTrace_3325875
  have hstable : (prefixWord ++ tailWord_3325875).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3325875).length < 2 ^ (prefixWord ++ tailWord_3325875).sum := by decide
  have hdescent : baseEnd_3325875 < baseStart_3325875 := by decide
  rcases family_descends (prefixWord ++ tailWord_3325875) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3325896 : List Nat := [2, 1, 3, 1, 4, 3, 1, 1, 1, 4, 2]
def baseStart_3325896 : Nat := 118140960795 + 3325896 * 2 ^ 59
def prefixEnd_3325896 : Nat := 4983230072969 + 3 ^ 40 * 3325896 * 2
def baseEnd_3325896 : Nat := 1707783254866024650304489

theorem tailTrace_3325896 : CollatzResearch.WordTrace tailWord_3325896 prefixEnd_3325896 1707783254866024650304489 := by
  unfold tailWord_3325896
  simp only [CollatzResearch.WordTrace]
  refine ⟨60652696379427142329850771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80870261839236189773134361 60652696379427142329850771)
  ·
    refine ⟨90979044569140713494776157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60652696379427142329850771 90979044569140713494776157)
    ·
      refine ⟨34117141713427767560541059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 90979044569140713494776157 34117141713427767560541059)
      ·
        refine ⟨51175712570141651340811589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34117141713427767560541059 51175712570141651340811589)
        ·
          refine ⟨9595446106901559626402173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 51175712570141651340811589 9595446106901559626402173)
          ·
            refine ⟨3598292290088084859900815, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9595446106901559626402173 3598292290088084859900815)
            ·
              refine ⟨5397438435132127289851223, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3598292290088084859900815 5397438435132127289851223)
              ·
                refine ⟨8096157652698190934776835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5397438435132127289851223 8096157652698190934776835)
                ·
                  refine ⟨12144236479047286402165253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8096157652698190934776835 12144236479047286402165253)
                  ·
                    refine ⟨2277044339821366200405985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 12144236479047286402165253 2277044339821366200405985)
                    ·
                      refine ⟨1707783254866024650304489, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2277044339821366200405985 1707783254866024650304489)
                      ·
                        rfl

theorem cell23_3325896_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 3, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 3, 1, 1, 1, 4, 2].length) (baseStart_3325896 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3325896 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3325896 prefixEnd_3325896 := by exact prefixLift 3325896
  have htrace : WordTrace (prefixWord ++ tailWord_3325896) baseStart_3325896 baseEnd_3325896 := by
    simpa [prefixWord, tailWord_3325896, baseEnd_3325896] using wordTrace_append hprefix tailTrace_3325896
  have hstable : (prefixWord ++ tailWord_3325896).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3325896).length < 2 ^ (prefixWord ++ tailWord_3325896).sum := by decide
  have hdescent : baseEnd_3325896 < baseStart_3325896 := by decide
  rcases family_descends (prefixWord ++ tailWord_3325896) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3325919 : List Nat := [1, 1, 2, 3, 4, 1, 3, 3, 5]
def baseStart_3325919 : Nat := 118140960795 + 3325919 * 2 ^ 59
def prefixEnd_3325919 : Nat := 4983230072969 + 3 ^ 40 * 3325919 * 2
def baseEnd_3325919 : Nat := 189755007213453117812987

theorem tailTrace_3325919 : CollatzResearch.WordTrace tailWord_3325919 prefixEnd_3325919 189755007213453117812987 := by
  unfold tailWord_3325919
  simp only [CollatzResearch.WordTrace]
  refine ⟨121306231637770959587788811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80870821091847306391859207 121306231637770959587788811)
  ·
    refine ⟨181959347456656439381683217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121306231637770959587788811 181959347456656439381683217)
    ·
      refine ⟨136469510592492329536262413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 181959347456656439381683217 136469510592492329536262413)
      ·
        refine ⟨51176066472184623576098405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 136469510592492329536262413 51176066472184623576098405)
        ·
          refine ⟨9595512463534616920518451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 51176066472184623576098405 9595512463534616920518451)
          ·
            refine ⟨14393268695301925380777677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9595512463534616920518451 14393268695301925380777677)
            ·
              refine ⟨5397475760738222017791629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14393268695301925380777677 5397475760738222017791629)
              ·
                refine ⟨2024053410276833256671861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5397475760738222017791629 2024053410276833256671861)
                ·
                  refine ⟨189755007213453117812987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2024053410276833256671861 189755007213453117812987)
                  ·
                    rfl

theorem cell23_3325919_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 1, 3, 3, 5].length) (baseStart_3325919 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3325919 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3325919 prefixEnd_3325919 := by exact prefixLift 3325919
  have htrace : WordTrace (prefixWord ++ tailWord_3325919) baseStart_3325919 baseEnd_3325919 := by
    simpa [prefixWord, tailWord_3325919, baseEnd_3325919] using wordTrace_append hprefix tailTrace_3325919
  have hstable : (prefixWord ++ tailWord_3325919).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3325919).length < 2 ^ (prefixWord ++ tailWord_3325919).sum := by decide
  have hdescent : baseEnd_3325919 < baseStart_3325919 := by decide
  rcases family_descends (prefixWord ++ tailWord_3325919) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3325955 : List Nat := [1, 1, 1, 3, 2, 1, 1, 2, 1, 5, 5]
def baseStart_3325955 : Nat := 118140960795 + 3325955 * 2 ^ 59
def prefixEnd_3325955 : Nat := 4983230072969 + 3 ^ 40 * 3325955 * 2
def baseEnd_3325955 : Nat := 1707813550224639919466717

theorem tailTrace_3325955 : CollatzResearch.WordTrace tailWord_3325955 prefixEnd_3325955 1707813550224639919466717 := by
  unfold tailWord_3325955
  simp only [CollatzResearch.WordTrace]
  refine ⟨121307544665640537736099319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80871696443760358490732879 121307544665640537736099319)
  ·
    refine ⟨181961316998460806604148979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121307544665640537736099319 181961316998460806604148979)
    ·
      refine ⟨272941975497691209906223469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 181961316998460806604148979 272941975497691209906223469)
      ·
        refine ⟨102353240811634203714833801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 272941975497691209906223469 102353240811634203714833801)
        ·
          refine ⟨76764930608725652786125351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 102353240811634203714833801 76764930608725652786125351)
          ·
            refine ⟨115147395913088479179188027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 76764930608725652786125351 115147395913088479179188027)
            ·
              refine ⟨172721093869632718768782041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 115147395913088479179188027 172721093869632718768782041)
              ·
                refine ⟨129540820402224539076586531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 172721093869632718768782041 129540820402224539076586531)
                ·
                  refine ⟨194311230603336808614879797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 129540820402224539076586531 194311230603336808614879797)
                  ·
                    refine ⟨18216677869062825807644981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 194311230603336808614879797 18216677869062825807644981)
                    ·
                      refine ⟨1707813550224639919466717, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 18216677869062825807644981 1707813550224639919466717)
                      ·
                        rfl

theorem cell23_3325955_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 1, 2, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 1, 2, 1, 5, 5].length) (baseStart_3325955 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3325955 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3325955 prefixEnd_3325955 := by exact prefixLift 3325955
  have htrace : WordTrace (prefixWord ++ tailWord_3325955) baseStart_3325955 baseEnd_3325955 := by
    simpa [prefixWord, tailWord_3325955, baseEnd_3325955] using wordTrace_append hprefix tailTrace_3325955
  have hstable : (prefixWord ++ tailWord_3325955).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3325955).length < 2 ^ (prefixWord ++ tailWord_3325955).sum := by decide
  have hdescent : baseEnd_3325955 < baseStart_3325955 := by decide
  rcases family_descends (prefixWord ++ tailWord_3325955) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3325989 : List Nat := [1, 3, 1, 2, 2, 3, 2, 2, 2, 2, 3]
def baseStart_3325989 : Nat := 118140960795 + 3325989 * 2 ^ 59
def prefixEnd_3325989 : Nat := 4983230072969 + 3 ^ 40 * 3325989 * 2
def baseEnd_3325989 : Nat := 1707831008566892786441561

theorem tailTrace_3325989 : CollatzResearch.WordTrace tailWord_3325989 prefixEnd_3325989 1707831008566892786441561 := by
  unfold tailWord_3325989
  simp only [CollatzResearch.WordTrace]
  refine ⟨121308784747517361542837021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80872523165011574361891347 121308784747517361542837021)
  ·
    refine ⟨45490794280319010578563883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 121308784747517361542837021 45490794280319010578563883)
    ·
      refine ⟨68236191420478515867845825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45490794280319010578563883 68236191420478515867845825)
      ·
        refine ⟨51177143565358886900884369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 68236191420478515867845825 51177143565358886900884369)
        ·
          refine ⟨38382857674019165175663277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51177143565358886900884369 38382857674019165175663277)
          ·
            refine ⟨14393571627757186940873729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 38382857674019165175663277 14393571627757186940873729)
            ·
              refine ⟨10795178720817890205655297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14393571627757186940873729 10795178720817890205655297)
              ·
                refine ⟨8096384040613417654241473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10795178720817890205655297 8096384040613417654241473)
                ·
                  refine ⟨6072288030460063240681105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8096384040613417654241473 6072288030460063240681105)
                  ·
                    refine ⟨4554216022845047430510829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6072288030460063240681105 4554216022845047430510829)
                    ·
                      refine ⟨1707831008566892786441561, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4554216022845047430510829 1707831008566892786441561)
                      ·
                        rfl

theorem cell23_3325989_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 3, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 3, 2, 2, 2, 2, 3].length) (baseStart_3325989 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3325989 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3325989 prefixEnd_3325989 := by exact prefixLift 3325989
  have htrace : WordTrace (prefixWord ++ tailWord_3325989) baseStart_3325989 baseEnd_3325989 := by
    simpa [prefixWord, tailWord_3325989, baseEnd_3325989] using wordTrace_append hprefix tailTrace_3325989
  have hstable : (prefixWord ++ tailWord_3325989).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3325989).length < 2 ^ (prefixWord ++ tailWord_3325989).sum := by decide
  have hdescent : baseEnd_3325989 < baseStart_3325989 := by decide
  rcases family_descends (prefixWord ++ tailWord_3325989) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3326052 : List Nat := [2, 3, 1, 1, 2, 1, 2, 2, 3, 6]
def baseStart_3326052 : Nat := 118140960795 + 3326052 * 2 ^ 59
def prefixEnd_3326052 : Nat := 4983230072969 + 3 ^ 40 * 3326052 * 2
def baseEnd_3326052 : Nat := 569287785949375346651257

theorem tailTrace_3326052 : CollatzResearch.WordTrace tailWord_3326052 prefixEnd_3326052 569287785949375346651257 := by
  unfold tailWord_3326052
  simp only [CollatzResearch.WordTrace]
  refine ⟨60655541273144561651190205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80874055030859415534920273 60655541273144561651190205)
  ·
    refine ⟨22745827977429210619196327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 60655541273144561651190205 22745827977429210619196327)
    ·
      refine ⟨34118741966143815928794491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22745827977429210619196327 34118741966143815928794491)
      ·
        refine ⟨51178112949215723893191737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34118741966143815928794491 51178112949215723893191737)
        ·
          refine ⟨38383584711911792919893803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51178112949215723893191737 38383584711911792919893803)
          ·
            refine ⟨57575377067867689379840705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38383584711911792919893803 57575377067867689379840705)
            ·
              refine ⟨43181532800900767034880529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 57575377067867689379840705 43181532800900767034880529)
              ·
                refine ⟨32386149600675575276160397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 43181532800900767034880529 32386149600675575276160397)
                ·
                  refine ⟨12144806100253340728560149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 32386149600675575276160397 12144806100253340728560149)
                  ·
                    refine ⟨569287785949375346651257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 12144806100253340728560149 569287785949375346651257)
                    ·
                      rfl

theorem cell23_3326052_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 2, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 2, 2, 3, 6].length) (baseStart_3326052 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3326052 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3326052 prefixEnd_3326052 := by exact prefixLift 3326052
  have htrace : WordTrace (prefixWord ++ tailWord_3326052) baseStart_3326052 baseEnd_3326052 := by
    simpa [prefixWord, tailWord_3326052, baseEnd_3326052] using wordTrace_append hprefix tailTrace_3326052
  have hstable : (prefixWord ++ tailWord_3326052).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3326052).length < 2 ^ (prefixWord ++ tailWord_3326052).sum := by decide
  have hdescent : baseEnd_3326052 < baseStart_3326052 := by decide
  rcases family_descends (prefixWord ++ tailWord_3326052) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3326053 : List Nat := [1, 3, 1, 3, 2, 2, 2, 4, 1, 1, 3]
def baseStart_3326053 : Nat := 118140960795 + 3326053 * 2 ^ 59
def prefixEnd_3326053 : Nat := 4983230072969 + 3 ^ 40 * 3326053 * 2
def baseEnd_3326053 : Nat := 1707863871328780536041267

theorem tailTrace_3326053 : CollatzResearch.WordTrace tailWord_3326053 prefixEnd_3326053 1707863871328780536041267 := by
  unfold tailWord_3326053
  simp only [CollatzResearch.WordTrace]
  refine ⟨121311119019285500473166813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80874079346190333648777875 121311119019285500473166813)
  ·
    refine ⟨45491669632232062677437555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 121311119019285500473166813 45491669632232062677437555)
    ·
      refine ⟨68237504448348094016156333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45491669632232062677437555 68237504448348094016156333)
      ·
        refine ⟨25589064168130535256058625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 68237504448348094016156333 25589064168130535256058625)
        ·
          refine ⟨19191798126097901442043969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25589064168130535256058625 19191798126097901442043969)
          ·
            refine ⟨14393848594573426081532977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19191798126097901442043969 14393848594573426081532977)
            ·
              refine ⟨10795386445930069561149733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14393848594573426081532977 10795386445930069561149733)
              ·
                refine ⟨2024134958611888042715575, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10795386445930069561149733 2024134958611888042715575)
                ·
                  refine ⟨3036202437917832064073363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2024134958611888042715575 3036202437917832064073363)
                  ·
                    refine ⟨4554303656876748096110045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3036202437917832064073363 4554303656876748096110045)
                    ·
                      refine ⟨1707863871328780536041267, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4554303656876748096110045 1707863871328780536041267)
                      ·
                        rfl

theorem cell23_3326053_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 2, 2, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 2, 2, 4, 1, 1, 3].length) (baseStart_3326053 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3326053 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3326053 prefixEnd_3326053 := by exact prefixLift 3326053
  have htrace : WordTrace (prefixWord ++ tailWord_3326053) baseStart_3326053 baseEnd_3326053 := by
    simpa [prefixWord, tailWord_3326053, baseEnd_3326053] using wordTrace_append hprefix tailTrace_3326053
  have hstable : (prefixWord ++ tailWord_3326053).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3326053).length < 2 ^ (prefixWord ++ tailWord_3326053).sum := by decide
  have hdescent : baseEnd_3326053 < baseStart_3326053 := by decide
  rcases family_descends (prefixWord ++ tailWord_3326053) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3326076 : List Nat := [2, 2, 2, 1, 1, 5, 2, 2, 1, 1, 4]
def baseStart_3326076 : Nat := 118140960795 + 3326076 * 2 ^ 59
def prefixEnd_3326076 : Nat := 4983230072969 + 3 ^ 40 * 3326076 * 2
def baseEnd_3326076 : Nat := 1707875681383833946053661

theorem tailTrace_3326076 : CollatzResearch.WordTrace tailWord_3326076 prefixEnd_3326076 1707875681383833946053661 := by
  unfold tailWord_3326076
  simp only [CollatzResearch.WordTrace]
  refine ⟨60655978949101087700627041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80874638598801450267502721 60655978949101087700627041)
  ·
    refine ⟨45491984211825815775470281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60655978949101087700627041 45491984211825815775470281)
    ·
      refine ⟨34118988158869361831602711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45491984211825815775470281 34118988158869361831602711)
      ·
        refine ⟨51178482238304042747404067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34118988158869361831602711 51178482238304042747404067)
        ·
          refine ⟨76767723357456064121106101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51178482238304042747404067 76767723357456064121106101)
          ·
            refine ⟨7196974064761506011353697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 76767723357456064121106101 7196974064761506011353697)
            ·
              refine ⟨5397730548571129508515273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7196974064761506011353697 5397730548571129508515273)
              ·
                refine ⟨4048297911428347131386455, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5397730548571129508515273 4048297911428347131386455)
                ·
                  refine ⟨6072446867142520697079683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4048297911428347131386455 6072446867142520697079683)
                  ·
                    refine ⟨9108670300713781045619525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6072446867142520697079683 9108670300713781045619525)
                    ·
                      refine ⟨1707875681383833946053661, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9108670300713781045619525 1707875681383833946053661)
                      ·
                        rfl

theorem cell23_3326076_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 5, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 5, 2, 2, 1, 1, 4].length) (baseStart_3326076 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3326076 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3326076 prefixEnd_3326076 := by exact prefixLift 3326076
  have htrace : WordTrace (prefixWord ++ tailWord_3326076) baseStart_3326076 baseEnd_3326076 := by
    simpa [prefixWord, tailWord_3326076, baseEnd_3326076] using wordTrace_append hprefix tailTrace_3326076
  have hstable : (prefixWord ++ tailWord_3326076).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3326076).length < 2 ^ (prefixWord ++ tailWord_3326076).sum := by decide
  have hdescent : baseEnd_3326076 < baseStart_3326076 := by decide
  rcases family_descends (prefixWord ++ tailWord_3326076) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3326136 : List Nat := [2, 1, 2, 1, 2, 1, 5, 1, 3, 3, 2]
def baseStart_3326136 : Nat := 118140960795 + 3326136 * 2 ^ 59
def prefixEnd_3326136 : Nat := 4983230072969 + 3 ^ 40 * 3326136 * 2
def baseEnd_3326136 : Nat := 1707906490223103711303385

theorem tailTrace_3326136 : CollatzResearch.WordTrace tailWord_3326136 prefixEnd_3326136 1707906490223103711303385 := by
  unfold tailWord_3326136
  simp only [CollatzResearch.WordTrace]
  refine ⟨60657073138992402824219131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80876097518656537098958841 60657073138992402824219131)
  ·
    refine ⟨90985609708488604236328697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60657073138992402824219131 90985609708488604236328697)
    ·
      refine ⟨68239207281366453177246523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 90985609708488604236328697 68239207281366453177246523)
      ·
        refine ⟨102358810922049679765869785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68239207281366453177246523 102358810922049679765869785)
        ·
          refine ⟨76769108191537259824402339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 102358810922049679765869785 76769108191537259824402339)
          ·
            refine ⟨115153662287305889736603509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 76769108191537259824402339 115153662287305889736603509)
            ·
              refine ⟨10795655839434927162806579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 115153662287305889736603509 10795655839434927162806579)
              ·
                refine ⟨16193483759152390744209869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10795655839434927162806579 16193483759152390744209869)
                ·
                  refine ⟨6072556409682146529078701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16193483759152390744209869 6072556409682146529078701)
                  ·
                    refine ⟨2277208653630804948404513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6072556409682146529078701 2277208653630804948404513)
                    ·
                      refine ⟨1707906490223103711303385, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2277208653630804948404513 1707906490223103711303385)
                      ·
                        rfl

theorem cell23_3326136_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 5, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 5, 1, 3, 3, 2].length) (baseStart_3326136 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3326136 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3326136 prefixEnd_3326136 := by exact prefixLift 3326136
  have htrace : WordTrace (prefixWord ++ tailWord_3326136) baseStart_3326136 baseEnd_3326136 := by
    simpa [prefixWord, tailWord_3326136, baseEnd_3326136] using wordTrace_append hprefix tailTrace_3326136
  have hstable : (prefixWord ++ tailWord_3326136).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3326136).length < 2 ^ (prefixWord ++ tailWord_3326136).sum := by decide
  have hdescent : baseEnd_3326136 < baseStart_3326136 := by decide
  rcases family_descends (prefixWord ++ tailWord_3326136) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3326169 : List Nat := [1, 2, 1, 2, 3, 1, 3, 1, 2, 4, 3]
def baseStart_3326169 : Nat := 118140960795 + 3326169 * 2 ^ 59
def prefixEnd_3326169 : Nat := 4983230072969 + 3 ^ 40 * 3326169 * 2
def baseEnd_3326169 : Nat := 1707923435084702082190733

theorem tailTrace_3326169 : CollatzResearch.WordTrace tailWord_3326169 prefixEnd_3326169 1707923435084702082190733 := by
  unfold tailWord_3326169
  simp only [CollatzResearch.WordTrace]
  refine ⟨121315349886865252284389561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80876899924576834856259707 121315349886865252284389561)
  ·
    refine ⟨90986512415148939213292171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 121315349886865252284389561 90986512415148939213292171)
    ·
      refine ⟨136479768622723408819938257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90986512415148939213292171 136479768622723408819938257)
      ·
        refine ⟨102359826467042556614953693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 136479768622723408819938257 102359826467042556614953693)
        ·
          refine ⟨38384934925140958730607635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 102359826467042556614953693 38384934925140958730607635)
          ·
            refine ⟨57577402387711438095911453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38384934925140958730607635 57577402387711438095911453)
            ·
              refine ⟨21591525895391789285966795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 57577402387711438095911453 21591525895391789285966795)
              ·
                refine ⟨32387288843087683928950193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21591525895391789285966795 32387288843087683928950193)
                ·
                  refine ⟨24290466632315762946712645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32387288843087683928950193 24290466632315762946712645)
                  ·
                    refine ⟨4554462493559205552508621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 24290466632315762946712645 4554462493559205552508621)
                    ·
                      refine ⟨1707923435084702082190733, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4554462493559205552508621 1707923435084702082190733)
                      ·
                        rfl

theorem cell23_3326169_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 3, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 3, 1, 2, 4, 3].length) (baseStart_3326169 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3326169 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3326169 prefixEnd_3326169 := by exact prefixLift 3326169
  have htrace : WordTrace (prefixWord ++ tailWord_3326169) baseStart_3326169 baseEnd_3326169 := by
    simpa [prefixWord, tailWord_3326169, baseEnd_3326169] using wordTrace_append hprefix tailTrace_3326169
  have hstable : (prefixWord ++ tailWord_3326169).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3326169).length < 2 ^ (prefixWord ++ tailWord_3326169).sum := by decide
  have hdescent : baseEnd_3326169 < baseStart_3326169 := by decide
  rcases family_descends (prefixWord ++ tailWord_3326169) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3326183 : List Nat := [1, 1, 5, 3, 1, 1, 1, 3, 1, 4, 2]
def baseStart_3326183 : Nat := 118140960795 + 3326183 * 2 ^ 59
def prefixEnd_3326183 : Nat := 4983230072969 + 3 ^ 40 * 3326183 * 2
def baseEnd_3326183 : Nat := 1707930623813865027415669

theorem tailTrace_3326183 : CollatzResearch.WordTrace tailWord_3326183 prefixEnd_3326183 1707930623813865027415669 := by
  unfold tailWord_3326183
  simp only [CollatzResearch.WordTrace]
  refine ⟨121315860508814532675399203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80877240339209688450266135 121315860508814532675399203)
  ·
    refine ⟨181973790763221799013098805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121315860508814532675399203 181973790763221799013098805)
    ·
      refine ⟨17060042884052043657478013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 181973790763221799013098805 17060042884052043657478013)
      ·
        refine ⟨6397516081519516371554255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17060042884052043657478013 6397516081519516371554255)
        ·
          refine ⟨9596274122279274557331383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6397516081519516371554255 9596274122279274557331383)
          ·
            refine ⟨14394411183418911835997075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9596274122279274557331383 14394411183418911835997075)
            ·
              refine ⟨21591616775128367753995613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14394411183418911835997075 21591616775128367753995613)
              ·
                refine ⟨8096856290673137907748355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21591616775128367753995613 8096856290673137907748355)
                ·
                  refine ⟨12145284436009706861622533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8096856290673137907748355 12145284436009706861622533)
                  ·
                    refine ⟨2277240831751820036554225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 12145284436009706861622533 2277240831751820036554225)
                    ·
                      refine ⟨1707930623813865027415669, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2277240831751820036554225 1707930623813865027415669)
                      ·
                        rfl

theorem cell23_3326183_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 1, 1, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 1, 1, 3, 1, 4, 2].length) (baseStart_3326183 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3326183 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3326183 prefixEnd_3326183 := by exact prefixLift 3326183
  have htrace : WordTrace (prefixWord ++ tailWord_3326183) baseStart_3326183 baseEnd_3326183 := by
    simpa [prefixWord, tailWord_3326183, baseEnd_3326183] using wordTrace_append hprefix tailTrace_3326183
  have hstable : (prefixWord ++ tailWord_3326183).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3326183).length < 2 ^ (prefixWord ++ tailWord_3326183).sum := by decide
  have hdescent : baseEnd_3326183 < baseStart_3326183 := by decide
  rcases family_descends (prefixWord ++ tailWord_3326183) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3326199 : List Nat := [1, 1, 3, 1, 1, 1, 2, 1, 6, 3, 3]
def baseStart_3326199 : Nat := 118140960795 + 3326199 * 2 ^ 59
def prefixEnd_3326199 : Nat := 4983230072969 + 3 ^ 40 * 3326199 * 2
def baseEnd_3326199 : Nat := 1707938839504336964815595

theorem tailTrace_3326199 : CollatzResearch.WordTrace tailWord_3326199 prefixEnd_3326199 1707938839504336964815595 := by
  unfold tailWord_3326199
  simp only [CollatzResearch.WordTrace]
  refine ⟨121316444076756567407981651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80877629384504378271987767 121316444076756567407981651)
  ·
    refine ⟨181974666115134851111972477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121316444076756567407981651 181974666115134851111972477)
    ·
      refine ⟨68240499793175569166989679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 181974666115134851111972477 68240499793175569166989679)
      ·
        refine ⟨102360749689763353750484519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68240499793175569166989679 102360749689763353750484519)
        ·
          refine ⟨153541124534645030625726779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 102360749689763353750484519 153541124534645030625726779)
          ·
            refine ⟨230311686801967545938590169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 153541124534645030625726779 230311686801967545938590169)
            ·
              refine ⟨172733765101475659453942627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 230311686801967545938590169 172733765101475659453942627)
              ·
                refine ⟨259100647652213489180913941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 172733765101475659453942627 259100647652213489180913941)
                ·
                  refine ⟨12145342858697507305355341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 259100647652213489180913941 12145342858697507305355341)
                  ·
                    refine ⟨4554503572011565239508253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12145342858697507305355341 4554503572011565239508253)
                    ·
                      refine ⟨1707938839504336964815595, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4554503572011565239508253 1707938839504336964815595)
                      ·
                        rfl

theorem cell23_3326199_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 2, 1, 6, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 2, 1, 6, 3, 3].length) (baseStart_3326199 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3326199 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3326199 prefixEnd_3326199 := by exact prefixLift 3326199
  have htrace : WordTrace (prefixWord ++ tailWord_3326199) baseStart_3326199 baseEnd_3326199 := by
    simpa [prefixWord, tailWord_3326199, baseEnd_3326199] using wordTrace_append hprefix tailTrace_3326199
  have hstable : (prefixWord ++ tailWord_3326199).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3326199).length < 2 ^ (prefixWord ++ tailWord_3326199).sum := by decide
  have hdescent : baseEnd_3326199 < baseStart_3326199 := by decide
  rcases family_descends (prefixWord ++ tailWord_3326199) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3326216 : List Nat := [2, 1, 3, 2, 3, 1, 1, 2, 2, 3, 3]
def baseStart_3326216 : Nat := 118140960795 + 3326216 * 2 ^ 59
def prefixEnd_3326216 : Nat := 4983230072969 + 3 ^ 40 * 3326216 * 2
def baseEnd_3326216 : Nat := 1707947568675463398303017

theorem tailTrace_3326216 : CollatzResearch.WordTrace tailWord_3326216 prefixEnd_3326216 1707947568675463398303017 := by
  unfold tailWord_3326216
  simp only [CollatzResearch.WordTrace]
  refine ⟨60658532058847489655675251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80878042745129986207567001 60658532058847489655675251)
  ·
    refine ⟨90987798088271234483512877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60658532058847489655675251 90987798088271234483512877)
    ·
      refine ⟨34120424283101712931317329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 90987798088271234483512877 34120424283101712931317329)
      ·
        refine ⟨25590318212326284698487997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34120424283101712931317329 25590318212326284698487997)
        ·
          refine ⟨9596369329622356761932999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25590318212326284698487997 9596369329622356761932999)
          ·
            refine ⟨14394553994433535142899499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9596369329622356761932999 14394553994433535142899499)
            ·
              refine ⟨21591830991650302714349249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14394553994433535142899499 21591830991650302714349249)
              ·
                refine ⟨16193873243737727035761937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21591830991650302714349249 16193873243737727035761937)
                ·
                  refine ⟨12145404932803295276821453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16193873243737727035761937 12145404932803295276821453)
                  ·
                    refine ⟨4554526849801235728808045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12145404932803295276821453 4554526849801235728808045)
                    ·
                      refine ⟨1707947568675463398303017, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4554526849801235728808045 1707947568675463398303017)
                      ·
                        rfl

theorem cell23_3326216_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 1, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 1, 1, 2, 2, 3, 3].length) (baseStart_3326216 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3326216 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3326216 prefixEnd_3326216 := by exact prefixLift 3326216
  have htrace : WordTrace (prefixWord ++ tailWord_3326216) baseStart_3326216 baseEnd_3326216 := by
    simpa [prefixWord, tailWord_3326216, baseEnd_3326216] using wordTrace_append hprefix tailTrace_3326216
  have hstable : (prefixWord ++ tailWord_3326216).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3326216).length < 2 ^ (prefixWord ++ tailWord_3326216).sum := by decide
  have hdescent : baseEnd_3326216 < baseStart_3326216 := by decide
  rcases family_descends (prefixWord ++ tailWord_3326216) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3326219 : List Nat := [1, 1, 1, 1, 5, 2, 2, 1, 4, 5]
def baseStart_3326219 : Nat := 118140960795 + 3326219 * 2 ^ 59
def prefixEnd_3326219 : Nat := 4983230072969 + 3 ^ 40 * 3326219 * 2
def baseEnd_3326219 : Nat := 569316369705808962188501

theorem tailTrace_3326219 : CollatzResearch.WordTrace tailWord_3326219 prefixEnd_3326219 569316369705808962188501 := by
  unfold tailWord_3326219
  simp only [CollatzResearch.WordTrace]
  refine ⟨121317173536684110823709711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80878115691122740549139807 121317173536684110823709711)
  ·
    refine ⟨181975760305026166235564567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121317173536684110823709711 181975760305026166235564567)
    ·
      refine ⟨272963640457539249353346851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 181975760305026166235564567 272963640457539249353346851)
      ·
        refine ⟨409445460686308874030020277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 272963640457539249353346851 409445460686308874030020277)
        ·
          refine ⟨38385511939341456940314401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 409445460686308874030020277 38385511939341456940314401)
          ·
            refine ⟨28789133954506092705235801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38385511939341456940314401 28789133954506092705235801)
            ·
              refine ⟨21591850465879569528926851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28789133954506092705235801 21591850465879569528926851)
              ·
                refine ⟨32387775698819354293390277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21591850465879569528926851 32387775698819354293390277)
                ·
                  refine ⟨6072707943528628930010677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 32387775698819354293390277 6072707943528628930010677)
                  ·
                    refine ⟨569316369705808962188501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6072707943528628930010677 569316369705808962188501)
                    ·
                      rfl

theorem cell23_3326219_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 2, 1, 4, 5].length) (baseStart_3326219 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3326219 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3326219 prefixEnd_3326219 := by exact prefixLift 3326219
  have htrace : WordTrace (prefixWord ++ tailWord_3326219) baseStart_3326219 baseEnd_3326219 := by
    simpa [prefixWord, tailWord_3326219, baseEnd_3326219] using wordTrace_append hprefix tailTrace_3326219
  have hstable : (prefixWord ++ tailWord_3326219).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3326219).length < 2 ^ (prefixWord ++ tailWord_3326219).sum := by decide
  have hdescent : baseEnd_3326219 < baseStart_3326219 := by decide
  rcases family_descends (prefixWord ++ tailWord_3326219) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3326229 : List Nat := [1, 3, 2, 1, 2, 1, 2, 3, 1, 2, 5]
def baseStart_3326229 : Nat := 118140960795 + 3326229 * 2 ^ 59
def prefixEnd_3326229 : Nat := 4983230072969 + 3 ^ 40 * 3326229 * 2
def baseEnd_3326229 : Nat := 1707954243923971847440457

theorem tailTrace_3326229 : CollatzResearch.WordTrace tailWord_3326229 prefixEnd_3326229 1707954243923971847440457 := by
  unfold tailWord_3326229
  simp only [CollatzResearch.WordTrace]
  refine ⟨121317538266647882531573741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80878358844431921687715827 121317538266647882531573741)
  ·
    refine ⟨45494076849992955949340153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 121317538266647882531573741 45494076849992955949340153)
    ·
      refine ⟨34120557637494716962005115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45494076849992955949340153 34120557637494716962005115)
      ·
        refine ⟨51180836456242075443007673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34120557637494716962005115 51180836456242075443007673)
        ·
          refine ⟨38385627342181556582255755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51180836456242075443007673 38385627342181556582255755)
          ·
            refine ⟨57578441013272334873383633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38385627342181556582255755 57578441013272334873383633)
            ·
              refine ⟨43183830759954251155037725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 57578441013272334873383633 43183830759954251155037725)
              ·
                refine ⟨16193936534982844183139147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 43183830759954251155037725 16193936534982844183139147)
                ·
                  refine ⟨24290904802474266274708721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16193936534982844183139147 24290904802474266274708721)
                  ·
                    refine ⟨18218178601855699706031541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 24290904802474266274708721 18218178601855699706031541)
                    ·
                      refine ⟨1707954243923971847440457, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 18218178601855699706031541 1707954243923971847440457)
                      ·
                        rfl

theorem cell23_3326229_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 2, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 2, 3, 1, 2, 5].length) (baseStart_3326229 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3326229 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3326229 prefixEnd_3326229 := by exact prefixLift 3326229
  have htrace : WordTrace (prefixWord ++ tailWord_3326229) baseStart_3326229 baseEnd_3326229 := by
    simpa [prefixWord, tailWord_3326229, baseEnd_3326229] using wordTrace_append hprefix tailTrace_3326229
  have hstable : (prefixWord ++ tailWord_3326229).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3326229).length < 2 ^ (prefixWord ++ tailWord_3326229).sum := by decide
  have hdescent : baseEnd_3326229 < baseStart_3326229 := by decide
  rcases family_descends (prefixWord ++ tailWord_3326229) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3326256 : List Nat := [2, 1, 1, 1, 2, 2, 2, 2, 4, 4, 2]
def baseStart_3326256 : Nat := 118140960795 + 3326256 * 2 ^ 59
def prefixEnd_3326256 : Nat := 4983230072969 + 3 ^ 40 * 3326256 * 2
def baseEnd_3326256 : Nat := 1707968107901643241802833

theorem tailTrace_3326256 : CollatzResearch.WordTrace tailWord_3326256 prefixEnd_3326256 1707968107901643241802833 := by
  unfold tailWord_3326256
  simp only [CollatzResearch.WordTrace]
  refine ⟨60659261518775033071403311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80879015358366710761871081 60659261518775033071403311)
  ·
    refine ⟨90988892278162549607104967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60659261518775033071403311 90988892278162549607104967)
    ·
      refine ⟨136483338417243824410657451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90988892278162549607104967 136483338417243824410657451)
      ·
        refine ⟨204725007625865736615986177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 136483338417243824410657451 204725007625865736615986177)
        ·
          refine ⟨153543755719399302461989633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 204725007625865736615986177 153543755719399302461989633)
          ·
            refine ⟨115157816789549476846492225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 153543755719399302461989633 115157816789549476846492225)
            ·
              refine ⟨86368362592162107634869169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 115157816789549476846492225 86368362592162107634869169)
              ·
                refine ⟨64776271944121580726151877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 86368362592162107634869169 64776271944121580726151877)
                ·
                  refine ⟨12145550989522796386153477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 64776271944121580726151877 12145550989522796386153477)
                  ·
                    refine ⟨2277290810535524322403777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 12145550989522796386153477 2277290810535524322403777)
                    ·
                      refine ⟨1707968107901643241802833, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2277290810535524322403777 1707968107901643241802833)
                      ·
                        rfl

theorem cell23_3326256_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 2, 2, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 2, 2, 4, 4, 2].length) (baseStart_3326256 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3326256 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3326256 prefixEnd_3326256 := by exact prefixLift 3326256
  have htrace : WordTrace (prefixWord ++ tailWord_3326256) baseStart_3326256 baseEnd_3326256 := by
    simpa [prefixWord, tailWord_3326256, baseEnd_3326256] using wordTrace_append hprefix tailTrace_3326256
  have hstable : (prefixWord ++ tailWord_3326256).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3326256).length < 2 ^ (prefixWord ++ tailWord_3326256).sum := by decide
  have hdescent : baseEnd_3326256 < baseStart_3326256 := by decide
  rcases family_descends (prefixWord ++ tailWord_3326256) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3326279 : List Nat := [1, 1, 4, 1, 2, 2, 1, 3, 8]
def baseStart_3326279 : Nat := 118140960795 + 3326279 * 2 ^ 59
def prefixEnd_3326279 : Nat := 4983230072969 + 3 ^ 40 * 3326279 * 2
def baseEnd_3326279 : Nat := 189775546439632961312803

theorem tailTrace_3326279 : CollatzResearch.WordTrace tailWord_3326279 prefixEnd_3326279 189775546439632961312803 := by
  unfold tailWord_3326279
  simp only [CollatzResearch.WordTrace]
  refine ⟨121319361916466741070893891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80879574610977827380595927 121319361916466741070893891)
  ·
    refine ⟨181979042874700111606340837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121319361916466741070893891 181979042874700111606340837)
    ·
      refine ⟨34121070539006270926188907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 181979042874700111606340837 34121070539006270926188907)
      ·
        refine ⟨51181605808509406389283361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34121070539006270926188907 51181605808509406389283361)
        ·
          refine ⟨38386204356382054791962521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51181605808509406389283361 38386204356382054791962521)
          ·
            refine ⟨28789653267286541093971891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38386204356382054791962521 28789653267286541093971891)
            ·
              refine ⟨43184479900929811640957837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28789653267286541093971891 43184479900929811640957837)
              ·
                refine ⟨16194179962848679365359189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 43184479900929811640957837 16194179962848679365359189)
                ·
                  refine ⟨189775546439632961312803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 16194179962848679365359189 189775546439632961312803)
                  ·
                    rfl

theorem cell23_3326279_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 1, 3, 8].length) (baseStart_3326279 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3326279 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3326279 prefixEnd_3326279 := by exact prefixLift 3326279
  have htrace : WordTrace (prefixWord ++ tailWord_3326279) baseStart_3326279 baseEnd_3326279 := by
    simpa [prefixWord, tailWord_3326279, baseEnd_3326279] using wordTrace_append hprefix tailTrace_3326279
  have hstable : (prefixWord ++ tailWord_3326279).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3326279).length < 2 ^ (prefixWord ++ tailWord_3326279).sum := by decide
  have hdescent : baseEnd_3326279 < baseStart_3326279 := by decide
  rcases family_descends (prefixWord ++ tailWord_3326279) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3326319 : List Nat := [1, 1, 2, 1, 3, 1, 2, 1, 2, 4, 5]
def baseStart_3326319 : Nat := 118140960795 + 3326319 * 2 ^ 59
def prefixEnd_3326319 : Nat := 4983230072969 + 3 ^ 40 * 3326319 * 2
def baseEnd_3326319 : Nat := 1708000457182876495315043

theorem tailTrace_3326319 : CollatzResearch.WordTrace tailWord_3326319 prefixEnd_3326319 1708000457182876495315043 := by
  unfold tailWord_3326319
  simp only [CollatzResearch.WordTrace]
  refine ⟨121320820836321827902350011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80880547224214551934900007 121320820836321827902350011)
  ·
    refine ⟨181981231254482741853525017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121320820836321827902350011 181981231254482741853525017)
    ·
      refine ⟨136485923440862056390143763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 181981231254482741853525017 136485923440862056390143763)
      ·
        refine ⟨204728885161293084585215645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 136485923440862056390143763 204728885161293084585215645)
        ·
          refine ⟨76773331935484906719455867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 204728885161293084585215645 76773331935484906719455867)
          ·
            refine ⟨115159997903227360079183801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 76773331935484906719455867 115159997903227360079183801)
            ·
              refine ⟨86369998427420520059387851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 115159997903227360079183801 86369998427420520059387851)
              ·
                refine ⟨129554997641130780089081777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 86369998427420520059387851 129554997641130780089081777)
                ·
                  refine ⟨97166248230848085066811333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 129554997641130780089081777 97166248230848085066811333)
                  ·
                    refine ⟨18218671543284015950027125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 97166248230848085066811333 18218671543284015950027125)
                    ·
                      refine ⟨1708000457182876495315043, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 18218671543284015950027125 1708000457182876495315043)
                      ·
                        rfl

theorem cell23_3326319_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 2, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 2, 1, 2, 4, 5].length) (baseStart_3326319 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3326319 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3326319 prefixEnd_3326319 := by exact prefixLift 3326319
  have htrace : WordTrace (prefixWord ++ tailWord_3326319) baseStart_3326319 baseEnd_3326319 := by
    simpa [prefixWord, tailWord_3326319, baseEnd_3326319] using wordTrace_append hprefix tailTrace_3326319
  have hstable : (prefixWord ++ tailWord_3326319).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3326319).length < 2 ^ (prefixWord ++ tailWord_3326319).sum := by decide
  have hdescent : baseEnd_3326319 < baseStart_3326319 := by decide
  rcases family_descends (prefixWord ++ tailWord_3326319) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3326397 : List Nat := [1, 4, 1, 2, 2, 3, 2, 1, 3, 2, 2]
def baseStart_3326397 : Nat := 118140960795 + 3326397 * 2 ^ 59
def prefixEnd_3326397 : Nat := 4983230072969 + 3 ^ 40 * 3326397 * 2
def baseEnd_3326397 : Nat := 1708040508673927190139685

theorem tailTrace_3326397 : CollatzResearch.WordTrace tailWord_3326397 prefixEnd_3326397 1708040508673927190139685 := by
  unfold tailWord_3326397
  simp only [CollatzResearch.WordTrace]
  refine ⟨121323665730039247223689445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80882443820026164815792963 121323665730039247223689445)
  ·
    refine ⟨22748187324382358854441771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 121323665730039247223689445 22748187324382358854441771)
    ·
      refine ⟨34122280986573538281662657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22748187324382358854441771 34122280986573538281662657)
      ·
        refine ⟨25591710739930153711246993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34122280986573538281662657 25591710739930153711246993)
        ·
          refine ⟨19193783054947615283435245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25591710739930153711246993 19193783054947615283435245)
          ·
            refine ⟨7197668645605355731288217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19193783054947615283435245 7197668645605355731288217)
            ·
              refine ⟨5398251484204016798466163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7197668645605355731288217 5398251484204016798466163)
              ·
                refine ⟨8097377226306025197699245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5398251484204016798466163 8097377226306025197699245)
                ·
                  refine ⟨3036516459864759449137217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8097377226306025197699245 3036516459864759449137217)
                  ·
                    refine ⟨2277387344898569586852913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3036516459864759449137217 2277387344898569586852913)
                    ·
                      refine ⟨1708040508673927190139685, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2277387344898569586852913 1708040508673927190139685)
                      ·
                        rfl

theorem cell23_3326397_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 3, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 3, 2, 1, 3, 2, 2].length) (baseStart_3326397 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3326397 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3326397 prefixEnd_3326397 := by exact prefixLift 3326397
  have htrace : WordTrace (prefixWord ++ tailWord_3326397) baseStart_3326397 baseEnd_3326397 := by
    simpa [prefixWord, tailWord_3326397, baseEnd_3326397] using wordTrace_append hprefix tailTrace_3326397
  have hstable : (prefixWord ++ tailWord_3326397).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3326397).length < 2 ^ (prefixWord ++ tailWord_3326397).sum := by decide
  have hdescent : baseEnd_3326397 < baseStart_3326397 := by decide
  rcases family_descends (prefixWord ++ tailWord_3326397) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3326420 : List Nat := [2, 4, 1, 2, 2, 3, 2, 7]
def baseStart_3326420 : Nat := 118140960795 + 3326420 * 2 ^ 59
def prefixEnd_3326420 : Nat := 4983230072969 + 3 ^ 40 * 3326420 * 2
def baseEnd_3326420 : Nat := 63261196989962244450077

theorem tailTrace_3326420 : CollatzResearch.WordTrace tailWord_3326420 prefixEnd_3326420 63261196989962244450077 := by
  unfold tailWord_3326420
  simp only [CollatzResearch.WordTrace]
  refine ⟨60662252304477961075888357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80883003072637281434517809 60662252304477961075888357)
  ·
    refine ⟨11374172307089617701729067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 60662252304477961075888357 11374172307089617701729067)
    ·
      refine ⟨17061258460634426552593601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11374172307089617701729067 17061258460634426552593601)
      ·
        refine ⟨12795943845475819914445201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17061258460634426552593601 12795943845475819914445201)
        ·
          refine ⟨9596957884106864935833901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12795943845475819914445201 9596957884106864935833901)
          ·
            refine ⟨3598859206540074350937713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9596957884106864935833901 3598859206540074350937713)
            ·
              refine ⟨2699144404905055763203285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3598859206540074350937713 2699144404905055763203285)
              ·
                refine ⟨63261196989962244450077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2699144404905055763203285 63261196989962244450077)
                ·
                  rfl

theorem cell23_3326420_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 3, 2, 7].length) (baseStart_3326420 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3326420 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3326420 prefixEnd_3326420 := by exact prefixLift 3326420
  have htrace : WordTrace (prefixWord ++ tailWord_3326420) baseStart_3326420 baseEnd_3326420 := by
    simpa [prefixWord, tailWord_3326420, baseEnd_3326420] using wordTrace_append hprefix tailTrace_3326420
  have hstable : (prefixWord ++ tailWord_3326420).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3326420).length < 2 ^ (prefixWord ++ tailWord_3326420).sum := by decide
  have hdescent : baseEnd_3326420 < baseStart_3326420 := by decide
  rcases family_descends (prefixWord ++ tailWord_3326420) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3326426 : List Nat := [3, 1, 1, 2, 3, 1, 1, 1, 1, 4, 5]
def baseStart_3326426 : Nat := 118140960795 + 3326426 * 2 ^ 59
def prefixEnd_3326426 : Nat := 4983230072969 + 3 ^ 40 * 3326426 * 2
def baseEnd_3326426 : Nat := 1708055399612907576677051

theorem tailTrace_3326426 : CollatzResearch.WordTrace tailWord_3326426 prefixEnd_3326426 1708055399612907576677051 := by
  unfold tailWord_3326426
  simp only [CollatzResearch.WordTrace]
  refine ⟨30331180861733546294123783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 80883148964622790117663421 30331180861733546294123783)
  ·
    refine ⟨45496771292600319441185675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30331180861733546294123783 45496771292600319441185675)
    ·
      refine ⟨68245156938900479161778513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45496771292600319441185675 68245156938900479161778513)
      ·
        refine ⟨51183867704175359371333885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 68245156938900479161778513 51183867704175359371333885)
        ·
          refine ⟨19193950389065759764250207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 51183867704175359371333885 19193950389065759764250207)
          ·
            refine ⟨28790925583598639646375311, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19193950389065759764250207 28790925583598639646375311)
            ·
              refine ⟨43186388375397959469562967, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28790925583598639646375311 43186388375397959469562967)
              ·
                refine ⟨64779582563096939204344451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43186388375397959469562967 64779582563096939204344451)
                ·
                  refine ⟨97169373844645408806516677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 64779582563096939204344451 97169373844645408806516677)
                  ·
                    refine ⟨18219257595871014151221877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 97169373844645408806516677 18219257595871014151221877)
                    ·
                      refine ⟨1708055399612907576677051, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 18219257595871014151221877 1708055399612907576677051)
                      ·
                        rfl

theorem cell23_3326426_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 1, 1, 1, 4, 5].length) (baseStart_3326426 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3326426 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3326426 prefixEnd_3326426 := by exact prefixLift 3326426
  have htrace : WordTrace (prefixWord ++ tailWord_3326426) baseStart_3326426 baseEnd_3326426 := by
    simpa [prefixWord, tailWord_3326426, baseEnd_3326426] using wordTrace_append hprefix tailTrace_3326426
  have hstable : (prefixWord ++ tailWord_3326426).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3326426).length < 2 ^ (prefixWord ++ tailWord_3326426).sum := by decide
  have hdescent : baseEnd_3326426 < baseStart_3326426 := by decide
  rcases family_descends (prefixWord ++ tailWord_3326426) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3326436 : List Nat := [2, 3, 1, 1, 1, 1, 1, 1, 3, 5, 4]
def baseStart_3326436 : Nat := 118140960795 + 3326436 * 2 ^ 59
def prefixEnd_3326436 : Nat := 4983230072969 + 3 ^ 40 * 3326436 * 2
def baseEnd_3326436 : Nat := 1708060534419452537552005

theorem tailTrace_3326436 : CollatzResearch.WordTrace tailWord_3326436 prefixEnd_3326436 1708060534419452537552005 := by
  unfold tailWord_3326436
  simp only [CollatzResearch.WordTrace]
  refine ⟨60662544088448978442179581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80883392117931971256239441 60662544088448978442179581)
  ·
    refine ⟨22748454033168366915817343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 60662544088448978442179581 22748454033168366915817343)
    ·
      refine ⟨34122681049752550373726015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22748454033168366915817343 34122681049752550373726015)
      ·
        refine ⟨51184021574628825560589023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34122681049752550373726015 51184021574628825560589023)
        ·
          refine ⟨76776032361943238340883535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51184021574628825560589023 76776032361943238340883535)
          ·
            refine ⟨115164048542914857511325303, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 76776032361943238340883535 115164048542914857511325303)
            ·
              refine ⟨172746072814372286266987955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 115164048542914857511325303 172746072814372286266987955)
              ·
                refine ⟨259119109221558429400481933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 172746072814372286266987955 259119109221558429400481933)
                ·
                  refine ⟨97169665958084411025180725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 259119109221558429400481933 97169665958084411025180725)
                  ·
                    refine ⟨9109656183570413533610693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 97169665958084411025180725 9109656183570413533610693)
                    ·
                      refine ⟨1708060534419452537552005, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9109656183570413533610693 1708060534419452537552005)
                      ·
                        rfl

theorem cell23_3326436_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 1, 1, 3, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 1, 1, 3, 5, 4].length) (baseStart_3326436 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3326436 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3326436 prefixEnd_3326436 := by exact prefixLift 3326436
  have htrace : WordTrace (prefixWord ++ tailWord_3326436) baseStart_3326436 baseEnd_3326436 := by
    simpa [prefixWord, tailWord_3326436, baseEnd_3326436] using wordTrace_append hprefix tailTrace_3326436
  have hstable : (prefixWord ++ tailWord_3326436).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3326436).length < 2 ^ (prefixWord ++ tailWord_3326436).sum := by decide
  have hdescent : baseEnd_3326436 < baseStart_3326436 := by decide
  rcases family_descends (prefixWord ++ tailWord_3326436) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3326456 : List Nat := [2, 1, 2, 1, 1, 4, 1, 2, 1, 3, 5]
def baseStart_3326456 : Nat := 118140960795 + 3326456 * 2 ^ 59
def prefixEnd_3326456 : Nat := 4983230072969 + 3 ^ 40 * 3326456 * 2
def baseEnd_3326456 : Nat := 1708070804032542459301913

theorem tailTrace_3326456 : CollatzResearch.WordTrace tailWord_3326456 prefixEnd_3326456 1708070804032542459301913 := by
  unfold tailWord_3326456
  simp only [CollatzResearch.WordTrace]
  refine ⟨60662908818412750150043611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80883878424550333533391481 60662908818412750150043611)
  ·
    refine ⟨90994363227619125225065417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60662908818412750150043611 90994363227619125225065417)
    ·
      refine ⟨68245772420714343918799063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 90994363227619125225065417 68245772420714343918799063)
      ·
        refine ⟨102368658631071515878198595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68245772420714343918799063 102368658631071515878198595)
        ·
          refine ⟨153552987946607273817297893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 102368658631071515878198595 153552987946607273817297893)
          ·
            refine ⟨28791185239988863840743355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 153552987946607273817297893 28791185239988863840743355)
            ·
              refine ⟨43186777859983295761115033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28791185239988863840743355 43186777859983295761115033)
              ·
                refine ⟨32390083394987471820836275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 43186777859983295761115033 32390083394987471820836275)
                ·
                  refine ⟨48585125092481207731254413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32390083394987471820836275 48585125092481207731254413)
                  ·
                    refine ⟨18219421909680452899220405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 48585125092481207731254413 18219421909680452899220405)
                    ·
                      refine ⟨1708070804032542459301913, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 18219421909680452899220405 1708070804032542459301913)
                      ·
                        rfl

theorem cell23_3326456_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 1, 2, 1, 3, 5].length) (baseStart_3326456 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3326456 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3326456 prefixEnd_3326456 := by exact prefixLift 3326456
  have htrace : WordTrace (prefixWord ++ tailWord_3326456) baseStart_3326456 baseEnd_3326456 := by
    simpa [prefixWord, tailWord_3326456, baseEnd_3326456] using wordTrace_append hprefix tailTrace_3326456
  have hstable : (prefixWord ++ tailWord_3326456).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3326456).length < 2 ^ (prefixWord ++ tailWord_3326456).sum := by decide
  have hdescent : baseEnd_3326456 < baseStart_3326456 := by decide
  rcases family_descends (prefixWord ++ tailWord_3326456) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3326504 : List Nat := [2, 1, 5, 2, 1, 1, 1, 4, 2, 2, 2]
def baseStart_3326504 : Nat := 118140960795 + 3326504 * 2 ^ 59
def prefixEnd_3326504 : Nat := 4983230072969 + 3 ^ 40 * 3326504 * 2
def baseEnd_3326504 : Nat := 1708095451103958271501693

theorem tailTrace_3326504 : CollatzResearch.WordTrace tailWord_3326504 prefixEnd_3326504 1708095451103958271501693 := by
  unfold tailWord_3326504
  simp only [CollatzResearch.WordTrace]
  refine ⟨60663784170325802248917283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80885045560434402998556377 60663784170325802248917283)
  ·
    refine ⟨90995676255488703373375925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60663784170325802248917283 90995676255488703373375925)
    ·
      refine ⟨8530844648952065941253993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 90995676255488703373375925 8530844648952065941253993)
      ·
        refine ⟨6398133486714049455940495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8530844648952065941253993 6398133486714049455940495)
        ·
          refine ⟨9597200230071074183910743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6398133486714049455940495 9597200230071074183910743)
          ·
            refine ⟨14395800345106611275866115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9597200230071074183910743 14395800345106611275866115)
            ·
              refine ⟨21593700517659916913799173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14395800345106611275866115 21593700517659916913799173)
              ·
                refine ⟨4048818847061234421337345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 21593700517659916913799173 4048818847061234421337345)
                ·
                  refine ⟨3036614135295925816003009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4048818847061234421337345 3036614135295925816003009)
                  ·
                    refine ⟨2277460601471944362002257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3036614135295925816003009 2277460601471944362002257)
                    ·
                      refine ⟨1708095451103958271501693, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2277460601471944362002257 1708095451103958271501693)
                      ·
                        rfl

theorem cell23_3326504_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 1, 1, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 1, 1, 4, 2, 2, 2].length) (baseStart_3326504 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3326504 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3326504 prefixEnd_3326504 := by exact prefixLift 3326504
  have htrace : WordTrace (prefixWord ++ tailWord_3326504) baseStart_3326504 baseEnd_3326504 := by
    simpa [prefixWord, tailWord_3326504, baseEnd_3326504] using wordTrace_append hprefix tailTrace_3326504
  have hstable : (prefixWord ++ tailWord_3326504).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3326504).length < 2 ^ (prefixWord ++ tailWord_3326504).sum := by decide
  have hdescent : baseEnd_3326504 < baseStart_3326504 := by decide
  rcases family_descends (prefixWord ++ tailWord_3326504) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3326560 : List Nat := [2, 1, 1, 3, 2, 1, 3, 2, 2, 4, 2]
def baseStart_3326560 : Nat := 118140960795 + 3326560 * 2 ^ 59
def prefixEnd_3326560 : Nat := 4983230072969 + 3 ^ 40 * 3326560 * 2
def baseEnd_3326560 : Nat := 1708124206020610052401435

theorem tailTrace_3326560 : CollatzResearch.WordTrace tailWord_3326560 prefixEnd_3326560 1708124206020610052401435 := by
  unfold tailWord_3326560
  simp only [CollatzResearch.WordTrace]
  refine ⟨60664805414224363030936567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80886407218965817374582089 60664805414224363030936567)
  ·
    refine ⟨90997208121336544546404851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60664805414224363030936567 90997208121336544546404851)
    ·
      refine ⟨136495812182004816819607277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90997208121336544546404851 136495812182004816819607277)
      ·
        refine ⟨51185929568251806307352729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 136495812182004816819607277 51185929568251806307352729)
        ·
          refine ⟨38389447176188854730514547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51185929568251806307352729 38389447176188854730514547)
          ·
            refine ⟨57584170764283282095771821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38389447176188854730514547 57584170764283282095771821)
            ·
              refine ⟨21594064036606230785914433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 57584170764283282095771821 21594064036606230785914433)
              ·
                refine ⟨16195548027454673089435825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21594064036606230785914433 16195548027454673089435825)
                ·
                  refine ⟨12146661020591004817076869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16195548027454673089435825 12146661020591004817076869)
                  ·
                    refine ⟨2277498941360813403201913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 12146661020591004817076869 2277498941360813403201913)
                    ·
                      refine ⟨1708124206020610052401435, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2277498941360813403201913 1708124206020610052401435)
                      ·
                        rfl

theorem cell23_3326560_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 3, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 3, 2, 2, 4, 2].length) (baseStart_3326560 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3326560 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3326560 prefixEnd_3326560 := by exact prefixLift 3326560
  have htrace : WordTrace (prefixWord ++ tailWord_3326560) baseStart_3326560 baseEnd_3326560 := by
    simpa [prefixWord, tailWord_3326560, baseEnd_3326560] using wordTrace_append hprefix tailTrace_3326560
  have hstable : (prefixWord ++ tailWord_3326560).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3326560).length < 2 ^ (prefixWord ++ tailWord_3326560).sum := by decide
  have hdescent : baseEnd_3326560 < baseStart_3326560 := by decide
  rcases family_descends (prefixWord ++ tailWord_3326560) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3326583 : List Nat := [1, 1, 3, 1, 1, 3, 2, 5, 6]
def baseStart_3326583 : Nat := 118140960795 + 3326583 * 2 ^ 59
def prefixEnd_3326583 : Nat := 4983230072969 + 3 ^ 40 * 3326583 * 2
def baseEnd_3326583 : Nat := 189792890675073718045981

theorem tailTrace_3326583 : CollatzResearch.WordTrace tailWord_3326583 prefixEnd_3326583 189792890675073718045981 := by
  unfold tailWord_3326583
  simp only [CollatzResearch.WordTrace]
  refine ⟨121330449707365400989960403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80886966471576933993306935 121330449707365400989960403)
  ·
    refine ⟨181995674561048101484940605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121330449707365400989960403 181995674561048101484940605)
    ·
      refine ⟨68248377960393038056852727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 181995674561048101484940605 68248377960393038056852727)
      ·
        refine ⟨102372566940589557085279091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68248377960393038056852727 102372566940589557085279091)
        ·
          refine ⟨153558850410884335627918637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 102372566940589557085279091 153558850410884335627918637)
          ·
            refine ⟨57584568904081625860469489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 153558850410884335627918637 57584568904081625860469489)
            ·
              refine ⟨43188426678061219395352117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 57584568904081625860469489 43188426678061219395352117)
              ·
                refine ⟨4048915001068239318314261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 43188426678061219395352117 4048915001068239318314261)
                ·
                  refine ⟨189792890675073718045981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4048915001068239318314261 189792890675073718045981)
                  ·
                    rfl

theorem cell23_3326583_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 2, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 2, 5, 6].length) (baseStart_3326583 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3326583 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3326583 prefixEnd_3326583 := by exact prefixLift 3326583
  have htrace : WordTrace (prefixWord ++ tailWord_3326583) baseStart_3326583 baseEnd_3326583 := by
    simpa [prefixWord, tailWord_3326583, baseEnd_3326583] using wordTrace_append hprefix tailTrace_3326583
  have hstable : (prefixWord ++ tailWord_3326583).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3326583).length < 2 ^ (prefixWord ++ tailWord_3326583).sum := by decide
  have hdescent : baseEnd_3326583 < baseStart_3326583 := by decide
  rcases family_descends (prefixWord ++ tailWord_3326583) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3326613 : List Nat := [1, 3, 2, 1, 1, 1, 1, 1, 7, 5]
def baseStart_3326613 : Nat := 118140960795 + 3326613 * 2 ^ 59
def prefixEnd_3326613 : Nat := 4983230072969 + 3 ^ 40 * 3326613 * 2
def baseEnd_3326613 : Nat := 569383806831766115012897

theorem tailTrace_3326613 : CollatzResearch.WordTrace tailWord_3326613 prefixEnd_3326613 569383806831766115012897 := by
  unfold tailWord_3326613
  simp only [CollatzResearch.WordTrace]
  refine ⟨121331543897256716113552493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80887695931504477409034995 121331543897256716113552493)
  ·
    refine ⟨45499328961471268542582185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 121331543897256716113552493 45499328961471268542582185)
    ·
      refine ⟨34124496721103451406936639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45499328961471268542582185 34124496721103451406936639)
      ·
        refine ⟨51186745081655177110404959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34124496721103451406936639 51186745081655177110404959)
        ·
          refine ⟨76780117622482765665607439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51186745081655177110404959 76780117622482765665607439)
          ·
            refine ⟨115170176433724148498411159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 76780117622482765665607439 115170176433724148498411159)
            ·
              refine ⟨172755264650586222747616739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 115170176433724148498411159 172755264650586222747616739)
              ·
                refine ⟨259132896975879334121425109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 172755264650586222747616739 259132896975879334121425109)
                ·
                  refine ⟨6073427272872171893470901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 259132896975879334121425109 6073427272872171893470901)
                  ·
                    refine ⟨569383806831766115012897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6073427272872171893470901 569383806831766115012897)
                    ·
                      rfl

theorem cell23_3326613_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 1, 1, 7, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 1, 1, 7, 5].length) (baseStart_3326613 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3326613 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3326613 prefixEnd_3326613 := by exact prefixLift 3326613
  have htrace : WordTrace (prefixWord ++ tailWord_3326613) baseStart_3326613 baseEnd_3326613 := by
    simpa [prefixWord, tailWord_3326613, baseEnd_3326613] using wordTrace_append hprefix tailTrace_3326613
  have hstable : (prefixWord ++ tailWord_3326613).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3326613).length < 2 ^ (prefixWord ++ tailWord_3326613).sum := by decide
  have hdescent : baseEnd_3326613 < baseStart_3326613 := by decide
  rcases family_descends (prefixWord ++ tailWord_3326613) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3326634 : List Nat := [3, 1, 5, 2, 1, 1, 1, 3, 6]
def baseStart_3326634 : Nat := 118140960795 + 3326634 * 2 ^ 59
def prefixEnd_3326634 : Nat := 4983230072969 + 3 ^ 40 * 3326634 * 2
def baseEnd_3326634 : Nat := 189795800398782529208455

theorem tailTrace_3326634 : CollatzResearch.WordTrace tailWord_3326634 prefixEnd_3326634 189795800398782529208455 := by
  unfold tailWord_3326634
  simp only [CollatzResearch.WordTrace]
  refine ⟨30333077457545159175016739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 80888206553453757800044637 30333077457545159175016739)
  ·
    refine ⟨45499616186317738762525109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30333077457545159175016739 45499616186317738762525109)
    ·
      refine ⟨4265589017467288008986729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 45499616186317738762525109 4265589017467288008986729)
      ·
        refine ⟨3199191763100466006740047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4265589017467288008986729 3199191763100466006740047)
        ·
          refine ⟨4798787644650699010110071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3199191763100466006740047 4798787644650699010110071)
          ·
            refine ⟨7198181466976048515165107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4798787644650699010110071 7198181466976048515165107)
            ·
              refine ⟨10797272200464072772747661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7198181466976048515165107 10797272200464072772747661)
              ·
                refine ⟨4048977075174027289780373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10797272200464072772747661 4048977075174027289780373)
                ·
                  refine ⟨189795800398782529208455, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4048977075174027289780373 189795800398782529208455)
                  ·
                    rfl

theorem cell23_3326634_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 2, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 2, 1, 1, 1, 3, 6].length) (baseStart_3326634 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3326634 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3326634 prefixEnd_3326634 := by exact prefixLift 3326634
  have htrace : WordTrace (prefixWord ++ tailWord_3326634) baseStart_3326634 baseEnd_3326634 := by
    simpa [prefixWord, tailWord_3326634, baseEnd_3326634] using wordTrace_append hprefix tailTrace_3326634
  have hstable : (prefixWord ++ tailWord_3326634).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3326634).length < 2 ^ (prefixWord ++ tailWord_3326634).sum := by decide
  have hdescent : baseEnd_3326634 < baseStart_3326634 := by decide
  rcases family_descends (prefixWord ++ tailWord_3326634) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3326650 : List Nat := [3, 1, 1, 1, 2, 3, 3, 1, 3, 1, 4]
def baseStart_3326650 : Nat := 118140960795 + 3326650 * 2 ^ 59
def prefixEnd_3326650 : Nat := 4983230072969 + 3 ^ 40 * 3326650 * 2
def baseEnd_3326650 : Nat := 1708170419279514700276021

theorem tailTrace_3326650 : CollatzResearch.WordTrace tailWord_3326650 prefixEnd_3326650 1708170419279514700276021 := by
  unfold tailWord_3326650
  simp only [CollatzResearch.WordTrace]
  refine ⟨30333223349530667858162351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 80888595598748447621766269 30333223349530667858162351)
  ·
    refine ⟨45499835024296001787243527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30333223349530667858162351 45499835024296001787243527)
    ·
      refine ⟨68249752536444002680865291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45499835024296001787243527 68249752536444002680865291)
      ·
        refine ⟨102374628804666004021297937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68249752536444002680865291 102374628804666004021297937)
        ·
          refine ⟨76780971603499503015973453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 102374628804666004021297937 76780971603499503015973453)
          ·
            refine ⟨28792864351312313630990045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 76780971603499503015973453 28792864351312313630990045)
            ·
              refine ⟨10797324131742117611621267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28792864351312313630990045 10797324131742117611621267)
              ·
                refine ⟨16195986197613176417431901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10797324131742117611621267 16195986197613176417431901)
                ·
                  refine ⟨6073494824104941156536963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16195986197613176417431901 6073494824104941156536963)
                  ·
                    refine ⟨9110242236157411734805445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6073494824104941156536963 9110242236157411734805445)
                    ·
                      refine ⟨1708170419279514700276021, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9110242236157411734805445 1708170419279514700276021)
                      ·
                        rfl

theorem cell23_3326650_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 3, 1, 3, 1, 4].length) (baseStart_3326650 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3326650 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3326650 prefixEnd_3326650 := by exact prefixLift 3326650
  have htrace : WordTrace (prefixWord ++ tailWord_3326650) baseStart_3326650 baseEnd_3326650 := by
    simpa [prefixWord, tailWord_3326650, baseEnd_3326650] using wordTrace_append hprefix tailTrace_3326650
  have hstable : (prefixWord ++ tailWord_3326650).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3326650).length < 2 ^ (prefixWord ++ tailWord_3326650).sum := by decide
  have hdescent : baseEnd_3326650 < baseStart_3326650 := by decide
  rcases family_descends (prefixWord ++ tailWord_3326650) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3326654 : List Nat := [4, 2, 1, 1, 2, 1, 4, 1, 2, 3, 2]
def baseStart_3326654 : Nat := 118140960795 + 3326654 * 2 ^ 59
def prefixEnd_3326654 : Nat := 4983230072969 + 3 ^ 40 * 3326654 * 2
def baseEnd_3326654 : Nat := 1708172473202132684626003

theorem tailTrace_3326654 : CollatzResearch.WordTrace tailWord_3326654 prefixEnd_3326654 1708172473202132684626003 := by
  unfold tailWord_3326654
  simp only [CollatzResearch.WordTrace]
  refine ⟨15166629911263522514474377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 80888692860072120077196677 15166629911263522514474377)
  ·
    refine ⟨11374972433447641885855783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15166629911263522514474377 11374972433447641885855783)
    ·
      refine ⟨17062458650171462828783675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11374972433447641885855783 17062458650171462828783675)
      ·
        refine ⟨25593687975257194243175513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17062458650171462828783675 25593687975257194243175513)
        ·
          refine ⟨19195265981442895682381635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25593687975257194243175513 19195265981442895682381635)
          ·
            refine ⟨28792898972164343523572453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19195265981442895682381635 28792898972164343523572453)
            ·
              refine ⟨5398668557280814410669835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 28792898972164343523572453 5398668557280814410669835)
              ·
                refine ⟨8098002835921221616004753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5398668557280814410669835 8098002835921221616004753)
                ·
                  refine ⟨6073502126940916212003565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8098002835921221616004753 6073502126940916212003565)
                  ·
                    refine ⟨2277563297602843579501337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6073502126940916212003565 2277563297602843579501337)
                    ·
                      refine ⟨1708172473202132684626003, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2277563297602843579501337 1708172473202132684626003)
                      ·
                        rfl

theorem cell23_3326654_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 4, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 4, 1, 2, 3, 2].length) (baseStart_3326654 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3326654 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3326654 prefixEnd_3326654 := by exact prefixLift 3326654
  have htrace : WordTrace (prefixWord ++ tailWord_3326654) baseStart_3326654 baseEnd_3326654 := by
    simpa [prefixWord, tailWord_3326654, baseEnd_3326654] using wordTrace_append hprefix tailTrace_3326654
  have hstable : (prefixWord ++ tailWord_3326654).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3326654).length < 2 ^ (prefixWord ++ tailWord_3326654).sum := by decide
  have hdescent : baseEnd_3326654 < baseStart_3326654 := by decide
  rcases family_descends (prefixWord ++ tailWord_3326654) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3326660 : List Nat := [2, 3, 3, 1, 1, 2, 1, 1, 3, 6]
def baseStart_3326660 : Nat := 118140960795 + 3326660 * 2 ^ 59
def prefixEnd_3326660 : Nat := 4983230072969 + 3 ^ 40 * 3326660 * 2
def baseEnd_3326660 : Nat := 569391851362019887050325

theorem tailTrace_3326660 : CollatzResearch.WordTrace tailWord_3326660 prefixEnd_3326660 569391851362019887050325 := by
  unfold tailWord_3326660
  simp only [CollatzResearch.WordTrace]
  refine ⟨60666629064043221570256717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80888838752057628760342289 60666629064043221570256717)
  ·
    refine ⟨22749985899016208088846269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 60666629064043221570256717 22749985899016208088846269)
    ·
      refine ⟨8531244712131078033317351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22749985899016208088846269 8531244712131078033317351)
      ·
        refine ⟨12796867068196617049976027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8531244712131078033317351 12796867068196617049976027)
        ·
          refine ⟨19195300602294925574964041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12796867068196617049976027 19195300602294925574964041)
          ·
            refine ⟨14396475451721194181223031, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19195300602294925574964041 14396475451721194181223031)
            ·
              refine ⟨21594713177581791271834547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14396475451721194181223031 21594713177581791271834547)
              ·
                refine ⟨32392069766372686907751821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21594713177581791271834547 32392069766372686907751821)
                ·
                  refine ⟨12147026162389757590406933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 32392069766372686907751821 12147026162389757590406933)
                  ·
                    refine ⟨569391851362019887050325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 12147026162389757590406933 569391851362019887050325)
                    ·
                      rfl

theorem cell23_3326660_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 2, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 2, 1, 1, 3, 6].length) (baseStart_3326660 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3326660 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3326660 prefixEnd_3326660 := by exact prefixLift 3326660
  have htrace : WordTrace (prefixWord ++ tailWord_3326660) baseStart_3326660 baseEnd_3326660 := by
    simpa [prefixWord, tailWord_3326660, baseEnd_3326660] using wordTrace_append hprefix tailTrace_3326660
  have hstable : (prefixWord ++ tailWord_3326660).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3326660).length < 2 ^ (prefixWord ++ tailWord_3326660).sum := by decide
  have hdescent : baseEnd_3326660 < baseStart_3326660 := by decide
  rcases family_descends (prefixWord ++ tailWord_3326660) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3326663 : List Nat := [1, 1, 4, 1, 1, 1, 2, 2, 3, 1, 6]
def baseStart_3326663 : Nat := 118140960795 + 3326663 * 2 ^ 59
def prefixEnd_3326663 : Nat := 4983230072969 + 3 ^ 40 * 3326663 * 2
def baseEnd_3326663 : Nat := 1708177094528023149413461

theorem tailTrace_3326663 : CollatzResearch.WordTrace tailWord_3326663 prefixEnd_3326663 1708177094528023149413461 := by
  unfold tailWord_3326663
  simp only [CollatzResearch.WordTrace]
  refine ⟨121333367547075574652872643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80888911698050383101915095 121333367547075574652872643)
  ·
    refine ⟨182000051320613361979308965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121333367547075574652872643 182000051320613361979308965)
    ·
      refine ⟨34125009622615005371120431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 182000051320613361979308965 34125009622615005371120431)
      ·
        refine ⟨51187514433922508056680647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34125009622615005371120431 51187514433922508056680647)
        ·
          refine ⟨76781271650883762085020971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51187514433922508056680647 76781271650883762085020971)
          ·
            refine ⟨115171907476325643127531457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 76781271650883762085020971 115171907476325643127531457)
            ·
              refine ⟨86378930607244232345648593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 115171907476325643127531457 86378930607244232345648593)
              ·
                refine ⟨64784197955433174259236445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 86378930607244232345648593 64784197955433174259236445)
                ·
                  refine ⟨24294074233287440347213667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 64784197955433174259236445 24294074233287440347213667)
                  ·
                    refine ⟨36441111349931160520820501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 24294074233287440347213667 36441111349931160520820501)
                    ·
                      refine ⟨1708177094528023149413461, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 36441111349931160520820501 1708177094528023149413461)
                      ·
                        rfl

theorem cell23_3326663_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 2, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 2, 2, 3, 1, 6].length) (baseStart_3326663 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3326663 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3326663 prefixEnd_3326663 := by exact prefixLift 3326663
  have htrace : WordTrace (prefixWord ++ tailWord_3326663) baseStart_3326663 baseEnd_3326663 := by
    simpa [prefixWord, tailWord_3326663, baseEnd_3326663] using wordTrace_append hprefix tailTrace_3326663
  have hstable : (prefixWord ++ tailWord_3326663).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3326663).length < 2 ^ (prefixWord ++ tailWord_3326663).sum := by decide
  have hdescent : baseEnd_3326663 < baseStart_3326663 := by decide
  rcases family_descends (prefixWord ++ tailWord_3326663) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3326717 : List Nat := [1, 4, 1, 1, 1, 1, 4, 2, 4, 1, 3]
def baseStart_3326717 : Nat := 118140960795 + 3326717 * 2 ^ 59
def prefixEnd_3326717 : Nat := 4983230072969 + 3 ^ 40 * 3326717 * 2
def baseEnd_3326717 : Nat := 1708204822483365938138213

theorem tailTrace_3326717 : CollatzResearch.WordTrace tailWord_3326717 prefixEnd_3326717 1708204822483365938138213 := by
  unfold tailWord_3326717
  simp only [CollatzResearch.WordTrace]
  refine ⟨121335337088879941875338405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80890224725919961250225603 121335337088879941875338405)
  ·
    refine ⟨22750375704164989101625951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 121335337088879941875338405 22750375704164989101625951)
    ·
      refine ⟨34125563556247483652438927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22750375704164989101625951 34125563556247483652438927)
      ·
        refine ⟨51188345334371225478658391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34125563556247483652438927 51188345334371225478658391)
        ·
          refine ⟨76782518001556838217987587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51188345334371225478658391 76782518001556838217987587)
          ·
            refine ⟨115173777002335257326981381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 76782518001556838217987587 115173777002335257326981381)
            ·
              refine ⟨21595083187937860748809009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 115173777002335257326981381 21595083187937860748809009)
              ·
                refine ⟨16196312390953395561606757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21595083187937860748809009 16196312390953395561606757)
                ·
                  refine ⟨3036808573303761667801267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 16196312390953395561606757 3036808573303761667801267)
                  ·
                    refine ⟨4555212859955642501701901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3036808573303761667801267 4555212859955642501701901)
                    ·
                      refine ⟨1708204822483365938138213, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4555212859955642501701901 1708204822483365938138213)
                      ·
                        rfl

theorem cell23_3326717_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 4, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 4, 2, 4, 1, 3].length) (baseStart_3326717 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3326717 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3326717 prefixEnd_3326717 := by exact prefixLift 3326717
  have htrace : WordTrace (prefixWord ++ tailWord_3326717) baseStart_3326717 baseEnd_3326717 := by
    simpa [prefixWord, tailWord_3326717, baseEnd_3326717] using wordTrace_append hprefix tailTrace_3326717
  have hstable : (prefixWord ++ tailWord_3326717).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3326717).length < 2 ^ (prefixWord ++ tailWord_3326717).sum := by decide
  have hdescent : baseEnd_3326717 < baseStart_3326717 := by decide
  rcases family_descends (prefixWord ++ tailWord_3326717) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3326718 : List Nat := [4, 2, 2, 1, 2, 1, 1, 5, 1, 2, 2]
def baseStart_3326718 : Nat := 118140960795 + 3326718 * 2 ^ 59
def prefixEnd_3326718 : Nat := 4983230072969 + 3 ^ 40 * 3326718 * 2
def baseEnd_3326718 : Nat := 1708205335964020434225709

theorem tailTrace_3326718 : CollatzResearch.WordTrace tailWord_3326718 prefixEnd_3326718 1708205335964020434225709 := by
  unfold tailWord_3326718
  simp only [CollatzResearch.WordTrace]
  refine ⟨15166921695234539880765601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 80890249041250879364083205 15166921695234539880765601)
  ·
    refine ⟨11375191271425904910574201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15166921695234539880765601 11375191271425904910574201)
    ·
      refine ⟨8531393453569428682930651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11375191271425904910574201 8531393453569428682930651)
      ·
        refine ⟨12797090180354143024395977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8531393453569428682930651 12797090180354143024395977)
        ·
          refine ⟨9597817635265607268296983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12797090180354143024395977 9597817635265607268296983)
          ·
            refine ⟨14396726452898410902445475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9597817635265607268296983 14396726452898410902445475)
            ·
              refine ⟨21595089679347616353668213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14396726452898410902445475 21595089679347616353668213)
              ·
                refine ⟨2024539657438839033156395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 21595089679347616353668213 2024539657438839033156395)
                ·
                  refine ⟨3036809486158258549734593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2024539657438839033156395 3036809486158258549734593)
                  ·
                    refine ⟨2277607114618693912300945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3036809486158258549734593 2277607114618693912300945)
                    ·
                      refine ⟨1708205335964020434225709, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2277607114618693912300945 1708205335964020434225709)
                      ·
                        rfl

theorem cell23_3326718_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 1, 1, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 1, 1, 5, 1, 2, 2].length) (baseStart_3326718 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3326718 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3326718 prefixEnd_3326718 := by exact prefixLift 3326718
  have htrace : WordTrace (prefixWord ++ tailWord_3326718) baseStart_3326718 baseEnd_3326718 := by
    simpa [prefixWord, tailWord_3326718, baseEnd_3326718] using wordTrace_append hprefix tailTrace_3326718
  have hstable : (prefixWord ++ tailWord_3326718).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3326718).length < 2 ^ (prefixWord ++ tailWord_3326718).sum := by decide
  have hdescent : baseEnd_3326718 < baseStart_3326718 := by decide
  rcases family_descends (prefixWord ++ tailWord_3326718) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3326751 : List Nat := [1, 1, 2, 4, 2, 3, 3, 1, 2, 1, 3]
def baseStart_3326751 : Nat := 118140960795 + 3326751 * 2 ^ 59
def prefixEnd_3326751 : Nat := 4983230072969 + 3 ^ 40 * 3326751 * 2
def baseEnd_3326751 : Nat := 1708222280825618805113057

theorem tailTrace_3326751 : CollatzResearch.WordTrace tailWord_3326751 prefixEnd_3326751 1708222280825618805113057 := by
  unfold tailWord_3326751
  simp only [CollatzResearch.WordTrace]
  refine ⟨121336577170756765682076107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80891051447171177121384071 121336577170756765682076107)
  ·
    refine ⟨182004865756135148523114161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121336577170756765682076107 182004865756135148523114161)
    ·
      refine ⟨136503649317101361392335621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 182004865756135148523114161 136503649317101361392335621)
      ·
        refine ⟨25594434246956505261062929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 136503649317101361392335621 25594434246956505261062929)
        ·
          refine ⟨19195825685217378945797197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25594434246956505261062929 19195825685217378945797197)
          ·
            refine ⟨7198434631956517104673949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19195825685217378945797197 7198434631956517104673949)
            ·
              refine ⟨2699412986983693914252731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7198434631956517104673949 2699412986983693914252731)
              ·
                refine ⟨4049119480475540871379097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2699412986983693914252731 4049119480475540871379097)
                ·
                  refine ⟨3036839610356655653534323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4049119480475540871379097 3036839610356655653534323)
                  ·
                    refine ⟨4555259415534983480301485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3036839610356655653534323 4555259415534983480301485)
                    ·
                      refine ⟨1708222280825618805113057, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4555259415534983480301485 1708222280825618805113057)
                      ·
                        rfl

theorem cell23_3326751_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 3, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 3, 3, 1, 2, 1, 3].length) (baseStart_3326751 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3326751 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3326751 prefixEnd_3326751 := by exact prefixLift 3326751
  have htrace : WordTrace (prefixWord ++ tailWord_3326751) baseStart_3326751 baseEnd_3326751 := by
    simpa [prefixWord, tailWord_3326751, baseEnd_3326751] using wordTrace_append hprefix tailTrace_3326751
  have hstable : (prefixWord ++ tailWord_3326751).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3326751).length < 2 ^ (prefixWord ++ tailWord_3326751).sum := by decide
  have hdescent : baseEnd_3326751 < baseStart_3326751 := by decide
  rcases family_descends (prefixWord ++ tailWord_3326751) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3326817 : List Nat := [1, 2, 3, 1, 1, 1, 2, 1, 4, 5, 2]
def baseStart_3326817 : Nat := 118140960795 + 3326817 * 2 ^ 59
def prefixEnd_3326817 : Nat := 4983230072969 + 3 ^ 40 * 3326817 * 2
def baseEnd_3326817 : Nat := 1708256170548815546887753

theorem tailTrace_3326817 : CollatzResearch.WordTrace tailWord_3326817 prefixEnd_3326817 1708256170548815546887753 := by
  unfold tailWord_3326817
  simp only [CollatzResearch.WordTrace]
  refine ⟨121338984388517658953978705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80892656259011772635985803 121338984388517658953978705)
  ·
    refine ⟨91004238291388244215484029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 121338984388517658953978705 91004238291388244215484029)
    ·
      refine ⟨34126589359270591580806511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 91004238291388244215484029 34126589359270591580806511)
      ·
        refine ⟨51189884038905887371209767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34126589359270591580806511 51189884038905887371209767)
        ·
          refine ⟨76784826058358831056814651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51189884038905887371209767 76784826058358831056814651)
          ·
            refine ⟨115177239087538246585221977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 76784826058358831056814651 115177239087538246585221977)
            ·
              refine ⟨86382929315653684938916483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 115177239087538246585221977 86382929315653684938916483)
              ·
                refine ⟨129574393973480527408374725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 86382929315653684938916483 129574393973480527408374725)
                ·
                  refine ⟨24295198870027598889070261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 129574393973480527408374725 24295198870027598889070261)
                  ·
                    refine ⟨2277674894065087395850337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 24295198870027598889070261 2277674894065087395850337)
                    ·
                      refine ⟨1708256170548815546887753, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2277674894065087395850337 1708256170548815546887753)
                      ·
                        rfl

theorem cell23_3326817_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 2, 1, 4, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 2, 1, 4, 5, 2].length) (baseStart_3326817 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3326817 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3326817 prefixEnd_3326817 := by exact prefixLift 3326817
  have htrace : WordTrace (prefixWord ++ tailWord_3326817) baseStart_3326817 baseEnd_3326817 := by
    simpa [prefixWord, tailWord_3326817, baseEnd_3326817] using wordTrace_append hprefix tailTrace_3326817
  have hstable : (prefixWord ++ tailWord_3326817).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3326817).length < 2 ^ (prefixWord ++ tailWord_3326817).sum := by decide
  have hdescent : baseEnd_3326817 < baseStart_3326817 := by decide
  rcases family_descends (prefixWord ++ tailWord_3326817) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3326837 : List Nat := [1, 3, 4, 1, 1, 2, 1, 2, 1, 2, 5]
def baseStart_3326837 : Nat := 118140960795 + 3326837 * 2 ^ 59
def prefixEnd_3326837 : Nat := 4983230072969 + 3 ^ 40 * 3326837 * 2
def baseEnd_3326837 : Nat := 1708266440161905468637661

theorem tailTrace_3326837 : CollatzResearch.WordTrace tailWord_3326837 prefixEnd_3326837 1708266440161905468637661 := by
  unfold tailWord_3326837
  simp only [CollatzResearch.WordTrace]
  refine ⟨121339713848445202369706765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80893142565630134913137843 121339713848445202369706765)
  ·
    refine ⟨45502392693166950888640037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 121339713848445202369706765 45502392693166950888640037)
    ·
      refine ⟨8531698629968803291620007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 45502392693166950888640037 8531698629968803291620007)
      ·
        refine ⟨12797547944953204937430011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8531698629968803291620007 12797547944953204937430011)
        ·
          refine ⟨19196321917429807406145017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12797547944953204937430011 19196321917429807406145017)
          ·
            refine ⟨14397241438072355554608763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19196321917429807406145017 14397241438072355554608763)
            ·
              refine ⟨21595862157108533331913145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14397241438072355554608763 21595862157108533331913145)
              ·
                refine ⟨16196896617831399998934859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21595862157108533331913145 16196896617831399998934859)
                ·
                  refine ⟨24295344926747099998402289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16196896617831399998934859 24295344926747099998402289)
                  ·
                    refine ⟨18221508695060324998801717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 24295344926747099998402289 18221508695060324998801717)
                    ·
                      refine ⟨1708266440161905468637661, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 18221508695060324998801717 1708266440161905468637661)
                      ·
                        rfl

theorem cell23_3326837_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 2, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 2, 1, 2, 1, 2, 5].length) (baseStart_3326837 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3326837 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3326837 prefixEnd_3326837 := by exact prefixLift 3326837
  have htrace : WordTrace (prefixWord ++ tailWord_3326837) baseStart_3326837 baseEnd_3326837 := by
    simpa [prefixWord, tailWord_3326837, baseEnd_3326837] using wordTrace_append hprefix tailTrace_3326837
  have hstable : (prefixWord ++ tailWord_3326837).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3326837).length < 2 ^ (prefixWord ++ tailWord_3326837).sum := by decide
  have hdescent : baseEnd_3326837 < baseStart_3326837 := by decide
  rcases family_descends (prefixWord ++ tailWord_3326837) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3326847 : List Nat := [1, 1, 2, 2, 1, 1, 6, 2, 2, 1, 4]
def baseStart_3326847 : Nat := 118140960795 + 3326847 * 2 ^ 59
def prefixEnd_3326847 : Nat := 4983230072969 + 3 ^ 40 * 3326847 * 2
def baseEnd_3326847 : Nat := 1708271574968450429512615

theorem tailTrace_3326847 : CollatzResearch.WordTrace tailWord_3326847 prefixEnd_3326847 1708271574968450429512615 := by
  unfold tailWord_3326847
  simp only [CollatzResearch.WordTrace]
  refine ⟨121340078578408974077570795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80893385718939316051713863 121340078578408974077570795)
  ·
    refine ⟨182010117867613461116356193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121340078578408974077570795 182010117867613461116356193)
    ·
      refine ⟨136507588400710095837267145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 182010117867613461116356193 136507588400710095837267145)
      ·
        refine ⟨102380691300532571877950359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 136507588400710095837267145 102380691300532571877950359)
        ·
          refine ⟨153571036950798857816925539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 102380691300532571877950359 153571036950798857816925539)
          ·
            refine ⟨230356555426198286725388309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 153571036950798857816925539 230356555426198286725388309)
            ·
              refine ⟨10797963535603044690252577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 230356555426198286725388309 10797963535603044690252577)
              ·
                refine ⟨8098472651702283517689433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10797963535603044690252577 8098472651702283517689433)
                ·
                  refine ⟨6073854488776712638267075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8098472651702283517689433 6073854488776712638267075)
                  ·
                    refine ⟨9110781733165068957400613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6073854488776712638267075 9110781733165068957400613)
                    ·
                      refine ⟨1708271574968450429512615, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9110781733165068957400613 1708271574968450429512615)
                      ·
                        rfl

theorem cell23_3326847_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 6, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 6, 2, 2, 1, 4].length) (baseStart_3326847 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3326847 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3326847 prefixEnd_3326847 := by exact prefixLift 3326847
  have htrace : WordTrace (prefixWord ++ tailWord_3326847) baseStart_3326847 baseEnd_3326847 := by
    simpa [prefixWord, tailWord_3326847, baseEnd_3326847] using wordTrace_append hprefix tailTrace_3326847
  have hstable : (prefixWord ++ tailWord_3326847).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3326847).length < 2 ^ (prefixWord ++ tailWord_3326847).sum := by decide
  have hdescent : baseEnd_3326847 < baseStart_3326847 := by decide
  rcases family_descends (prefixWord ++ tailWord_3326847) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3326881 : List Nat := [1, 2, 3, 4, 1, 3, 1, 1, 2, 1, 4]
def baseStart_3326881 : Nat := 118140960795 + 3326881 * 2 ^ 59
def prefixEnd_3326881 : Nat := 4983230072969 + 3 ^ 40 * 3326881 * 2
def baseEnd_3326881 : Nat := 1708289033310703296487459

theorem tailTrace_3326881 : CollatzResearch.WordTrace tailWord_3326881 prefixEnd_3326881 1708289033310703296487459 := by
  unfold tailWord_3326881
  simp only [CollatzResearch.WordTrace]
  refine ⟨121341318660285797884308497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80894212440190531922872331 121341318660285797884308497)
  ·
    refine ⟨91005988995214348413231373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 121341318660285797884308497 91005988995214348413231373)
    ·
      refine ⟨34127245873205380654961765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 91005988995214348413231373 34127245873205380654961765)
      ·
        refine ⟨6398858601226008872805331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 34127245873205380654961765 6398858601226008872805331)
        ·
          refine ⟨9598287901839013309207997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6398858601226008872805331 9598287901839013309207997)
          ·
            refine ⟨3599357963189629990952999, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9598287901839013309207997 3599357963189629990952999)
            ·
              refine ⟨5399036944784444986429499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3599357963189629990952999 5399036944784444986429499)
              ·
                refine ⟨8098555417176667479644249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5399036944784444986429499 8098555417176667479644249)
                ·
                  refine ⟨6073916562882500609733187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8098555417176667479644249 6073916562882500609733187)
                  ·
                    refine ⟨9110874844323750914599781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6073916562882500609733187 9110874844323750914599781)
                    ·
                      refine ⟨1708289033310703296487459, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9110874844323750914599781 1708289033310703296487459)
                      ·
                        rfl

theorem cell23_3326881_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 3, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 3, 1, 1, 2, 1, 4].length) (baseStart_3326881 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3326881 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3326881 prefixEnd_3326881 := by exact prefixLift 3326881
  have htrace : WordTrace (prefixWord ++ tailWord_3326881) baseStart_3326881 baseEnd_3326881 := by
    simpa [prefixWord, tailWord_3326881, baseEnd_3326881] using wordTrace_append hprefix tailTrace_3326881
  have hstable : (prefixWord ++ tailWord_3326881).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3326881).length < 2 ^ (prefixWord ++ tailWord_3326881).sum := by decide
  have hdescent : baseEnd_3326881 < baseStart_3326881 := by decide
  rcases family_descends (prefixWord ++ tailWord_3326881) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3326904 : List Nat := [2, 1, 2, 1, 2, 6, 1, 2, 6]
def baseStart_3326904 : Nat := 118140960795 + 3326904 * 2 ^ 59
def prefixEnd_3326904 : Nat := 4983230072969 + 3 ^ 40 * 3326904 * 2
def baseEnd_3326904 : Nat := 189811204818417411833317

theorem tailTrace_3326904 : CollatzResearch.WordTrace tailWord_3326904 prefixEnd_3326904 189811204818417411833317 := by
  unfold tailWord_3326904
  simp only [CollatzResearch.WordTrace]
  refine ⟨60671078769601236406197883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80894771692801648541597177 60671078769601236406197883)
  ·
    refine ⟨91006618154401854609296825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60671078769601236406197883 91006618154401854609296825)
    ·
      refine ⟨68254963615801390956972619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 91006618154401854609296825 68254963615801390956972619)
      ·
        refine ⟨102382445423702086435458929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68254963615801390956972619 102382445423702086435458929)
        ·
          refine ⟨76786834067776564826594197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 102382445423702086435458929 76786834067776564826594197)
          ·
            refine ⟨3599382846927026476246603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 76786834067776564826594197 3599382846927026476246603)
            ·
              refine ⟨5399074270390539714369905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3599382846927026476246603 5399074270390539714369905)
              ·
                refine ⟨4049305702792904785777429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5399074270390539714369905 4049305702792904785777429)
                ·
                  refine ⟨189811204818417411833317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4049305702792904785777429 189811204818417411833317)
                  ·
                    rfl

theorem cell23_3326904_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 6, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 6, 1, 2, 6].length) (baseStart_3326904 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3326904 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3326904 prefixEnd_3326904 := by exact prefixLift 3326904
  have htrace : WordTrace (prefixWord ++ tailWord_3326904) baseStart_3326904 baseEnd_3326904 := by
    simpa [prefixWord, tailWord_3326904, baseEnd_3326904] using wordTrace_append hprefix tailTrace_3326904
  have hstable : (prefixWord ++ tailWord_3326904).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3326904).length < 2 ^ (prefixWord ++ tailWord_3326904).sum := by decide
  have hdescent : baseEnd_3326904 < baseStart_3326904 := by decide
  rcases family_descends (prefixWord ++ tailWord_3326904) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3326924 : List Nat := [2, 2, 1, 4, 1, 1, 1, 1, 3, 5, 2]
def baseStart_3326924 : Nat := 118140960795 + 3326924 * 2 ^ 59
def prefixEnd_3326924 : Nat := 4983230072969 + 3 ^ 40 * 3326924 * 2
def baseEnd_3326924 : Nat := 1708311112978846628249761

theorem tailTrace_3326924 : CollatzResearch.WordTrace tailWord_3326924 prefixEnd_3326924 1708311112978846628249761 := by
  unfold tailWord_3326924
  simp only [CollatzResearch.WordTrace]
  refine ⟨60671443499565008114061913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80895257999420010818749217 60671443499565008114061913)
  ·
    refine ⟨45503582624673756085546435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60671443499565008114061913 45503582624673756085546435)
    ·
      refine ⟨68255373937010634128319653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45503582624673756085546435 68255373937010634128319653)
      ·
        refine ⟨12797882613189493899059935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 68255373937010634128319653 12797882613189493899059935)
        ·
          refine ⟨19196823919784240848589903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12797882613189493899059935 19196823919784240848589903)
          ·
            refine ⟨28795235879676361272884855, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19196823919784240848589903 28795235879676361272884855)
            ·
              refine ⟨43192853819514541909327283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28795235879676361272884855 43192853819514541909327283)
              ·
                refine ⟨64789280729271812863990925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43192853819514541909327283 64789280729271812863990925)
                ·
                  refine ⟨24295980273476929823996597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 64789280729271812863990925 24295980273476929823996597)
                  ·
                    refine ⟨2277748150638462170999681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 24295980273476929823996597 2277748150638462170999681)
                    ·
                      refine ⟨1708311112978846628249761, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2277748150638462170999681 1708311112978846628249761)
                      ·
                        rfl

theorem cell23_3326924_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 1, 1, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 1, 1, 3, 5, 2].length) (baseStart_3326924 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3326924 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3326924 prefixEnd_3326924 := by exact prefixLift 3326924
  have htrace : WordTrace (prefixWord ++ tailWord_3326924) baseStart_3326924 baseEnd_3326924 := by
    simpa [prefixWord, tailWord_3326924, baseEnd_3326924] using wordTrace_append hprefix tailTrace_3326924
  have hstable : (prefixWord ++ tailWord_3326924).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3326924).length < 2 ^ (prefixWord ++ tailWord_3326924).sum := by decide
  have hdescent : baseEnd_3326924 < baseStart_3326924 := by decide
  rcases family_descends (prefixWord ++ tailWord_3326924) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3326941 : List Nat := [1, 4, 3, 1, 2, 1, 2, 1, 1, 5, 2]
def baseStart_3326941 : Nat := 118140960795 + 3326941 * 2 ^ 59
def prefixEnd_3326941 : Nat := 4983230072969 + 3 ^ 40 * 3326941 * 2
def baseEnd_3326941 : Nat := 1708319842149973061737183

theorem tailTrace_3326941 : CollatzResearch.WordTrace tailWord_3326941 prefixEnd_3326941 1708319842149973061737183 := by
  unfold tailWord_3326941
  simp only [CollatzResearch.WordTrace]
  refine ⟨121343507040068428131492677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80895671360045618754328451 121343507040068428131492677)
  ·
    refine ⟨22751907570012830274654877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 121343507040068428131492677 22751907570012830274654877)
    ·
      refine ⟨8531965338754811352995579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22751907570012830274654877 8531965338754811352995579)
      ·
        refine ⟨12797948008132217029493369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8531965338754811352995579 12797948008132217029493369)
        ·
          refine ⟨9598461006099162772120027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12797948008132217029493369 9598461006099162772120027)
          ·
            refine ⟨14397691509148744158180041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9598461006099162772120027 14397691509148744158180041)
            ·
              refine ⟨10798268631861558118635031, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14397691509148744158180041 10798268631861558118635031)
              ·
                refine ⟨16197402947792337177952547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10798268631861558118635031 16197402947792337177952547)
                ·
                  refine ⟨24296104421688505766928821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16197402947792337177952547 24296104421688505766928821)
                  ·
                    refine ⟨2277759789533297415649577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 24296104421688505766928821 2277759789533297415649577)
                    ·
                      refine ⟨1708319842149973061737183, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2277759789533297415649577 1708319842149973061737183)
                      ·
                        rfl

theorem cell23_3326941_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 1, 2, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 1, 2, 1, 1, 5, 2].length) (baseStart_3326941 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3326941 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3326941 prefixEnd_3326941 := by exact prefixLift 3326941
  have htrace : WordTrace (prefixWord ++ tailWord_3326941) baseStart_3326941 baseEnd_3326941 := by
    simpa [prefixWord, tailWord_3326941, baseEnd_3326941] using wordTrace_append hprefix tailTrace_3326941
  have hstable : (prefixWord ++ tailWord_3326941).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3326941).length < 2 ^ (prefixWord ++ tailWord_3326941).sum := by decide
  have hdescent : baseEnd_3326941 < baseStart_3326941 := by decide
  rcases family_descends (prefixWord ++ tailWord_3326941) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3326947 : List Nat := [1, 1, 1, 6, 1, 1, 2, 1, 3, 6]
def baseStart_3326947 : Nat := 118140960795 + 3326947 * 2 ^ 59
def prefixEnd_3326947 : Nat := 4983230072969 + 3 ^ 40 * 3326947 * 2
def baseEnd_3326947 : Nat := 569440974344633346087385

theorem tailTrace_3326947 : CollatzResearch.WordTrace tailWord_3326947 prefixEnd_3326947 569440974344633346087385 := by
  unfold tailWord_3326947
  simp only [CollatzResearch.WordTrace]
  refine ⟨121343725878046691156211095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80895817252031127437474063 121343725878046691156211095)
  ·
    refine ⟨182015588817070036734316643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121343725878046691156211095 182015588817070036734316643)
    ·
      refine ⟨273023383225605055101474965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 182015588817070036734316643 273023383225605055101474965)
      ·
        refine ⟨12797971088700236957881639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 273023383225605055101474965 12797971088700236957881639)
        ·
          refine ⟨19196956633050355436822459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12797971088700236957881639 19196956633050355436822459)
          ·
            refine ⟨28795434949575533155233689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19196956633050355436822459 28795434949575533155233689)
            ·
              refine ⟨21596576212181649866425267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28795434949575533155233689 21596576212181649866425267)
              ·
                refine ⟨32394864318272474799637901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21596576212181649866425267 32394864318272474799637901)
                ·
                  refine ⟨12148074119352178049864213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 32394864318272474799637901 12148074119352178049864213)
                  ·
                    refine ⟨569440974344633346087385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 12148074119352178049864213 569440974344633346087385)
                    ·
                      rfl

theorem cell23_3326947_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 2, 1, 3, 6].length) (baseStart_3326947 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3326947 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3326947 prefixEnd_3326947 := by exact prefixLift 3326947
  have htrace : WordTrace (prefixWord ++ tailWord_3326947) baseStart_3326947 baseEnd_3326947 := by
    simpa [prefixWord, tailWord_3326947, baseEnd_3326947] using wordTrace_append hprefix tailTrace_3326947
  have hstable : (prefixWord ++ tailWord_3326947).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3326947).length < 2 ^ (prefixWord ++ tailWord_3326947).sum := by decide
  have hdescent : baseEnd_3326947 < baseStart_3326947 := by decide
  rcases family_descends (prefixWord ++ tailWord_3326947) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3326958 : List Nat := [4, 1, 2, 1, 4, 1, 1, 2, 2, 3, 2]
def baseStart_3326958 : Nat := 118140960795 + 3326958 * 2 ^ 59
def prefixEnd_3326958 : Nat := 4983230072969 + 3 ^ 40 * 3326958 * 2
def baseEnd_3326958 : Nat := 1708328571321099495224605

theorem tailTrace_3326958 : CollatzResearch.WordTrace tailWord_3326958 prefixEnd_3326958 1708328571321099495224605 := by
  unfold tailWord_3326958
  simp only [CollatzResearch.WordTrace]
  refine ⟨15168015885125855004357691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 80896084720671226689907685 15168015885125855004357691)
  ·
    refine ⟨22752023827688782506536537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15168015885125855004357691 22752023827688782506536537)
    ·
      refine ⟨17064017870766586879902403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22752023827688782506536537 17064017870766586879902403)
      ·
        refine ⟨25596026806149880319853605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17064017870766586879902403 25596026806149880319853605)
        ·
          refine ⟨4799255026153102559972551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 25596026806149880319853605 4799255026153102559972551)
          ·
            refine ⟨7198882539229653839958827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4799255026153102559972551 7198882539229653839958827)
            ·
              refine ⟨10798323808844480759938241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7198882539229653839958827 10798323808844480759938241)
              ·
                refine ⟨8098742856633360569953681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10798323808844480759938241 8098742856633360569953681)
                ·
                  refine ⟨6074057142475020427465261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8098742856633360569953681 6074057142475020427465261)
                  ·
                    refine ⟨2277771428428132660299473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6074057142475020427465261 2277771428428132660299473)
                    ·
                      refine ⟨1708328571321099495224605, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2277771428428132660299473 1708328571321099495224605)
                      ·
                        rfl

theorem cell23_3326958_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 4, 1, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 4, 1, 1, 2, 2, 3, 2].length) (baseStart_3326958 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3326958 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3326958 prefixEnd_3326958 := by exact prefixLift 3326958
  have htrace : WordTrace (prefixWord ++ tailWord_3326958) baseStart_3326958 baseEnd_3326958 := by
    simpa [prefixWord, tailWord_3326958, baseEnd_3326958] using wordTrace_append hprefix tailTrace_3326958
  have hstable : (prefixWord ++ tailWord_3326958).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3326958).length < 2 ^ (prefixWord ++ tailWord_3326958).sum := by decide
  have hdescent : baseEnd_3326958 < baseStart_3326958 := by decide
  rcases family_descends (prefixWord ++ tailWord_3326958) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3326977 : List Nat := [1, 2, 4, 1, 2, 2, 1, 10]
def baseStart_3326977 : Nat := 118140960795 + 3326977 * 2 ^ 59
def prefixEnd_3326977 : Nat := 4983230072969 + 3 ^ 40 * 3326977 * 2
def baseEnd_3326977 : Nat := 63271789905686478551371

theorem tailTrace_3326977 : CollatzResearch.WordTrace tailWord_3326977 prefixEnd_3326977 63271789905686478551371 := by
  unfold tailWord_3326977
  simp only [CollatzResearch.WordTrace]
  refine ⟨121344820067938006279803185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80896546711958670853202123 121344820067938006279803185)
  ·
    refine ⟨91008615050953504709852389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 121344820067938006279803185 91008615050953504709852389)
    ·
      refine ⟨17064115322053782133097323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 91008615050953504709852389 17064115322053782133097323)
      ·
        refine ⟨25596172983080673199645985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17064115322053782133097323 25596172983080673199645985)
        ·
          refine ⟨19197129737310504899734489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25596172983080673199645985 19197129737310504899734489)
          ·
            refine ⟨14397847302982878674800867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19197129737310504899734489 14397847302982878674800867)
            ·
              refine ⟨21596770954474318012201301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14397847302982878674800867 21596770954474318012201301)
              ·
                refine ⟨63271789905686478551371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 21596770954474318012201301 63271789905686478551371)
                ·
                  rfl

theorem cell23_3326977_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 2, 1, 10].length) (baseStart_3326977 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3326977 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3326977 prefixEnd_3326977 := by exact prefixLift 3326977
  have htrace : WordTrace (prefixWord ++ tailWord_3326977) baseStart_3326977 baseEnd_3326977 := by
    simpa [prefixWord, tailWord_3326977, baseEnd_3326977] using wordTrace_append hprefix tailTrace_3326977
  have hstable : (prefixWord ++ tailWord_3326977).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3326977).length < 2 ^ (prefixWord ++ tailWord_3326977).sum := by decide
  have hdescent : baseEnd_3326977 < baseStart_3326977 := by decide
  rcases family_descends (prefixWord ++ tailWord_3326977) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3327008 : List Nat := [2, 1, 1, 7, 1, 2, 1, 1, 1, 1, 5]
def baseStart_3327008 : Nat := 118140960795 + 3327008 * 2 ^ 59
def prefixEnd_3327008 : Nat := 4983230072969 + 3 ^ 40 * 3327008 * 2
def baseEnd_3327008 : Nat := 1708354245353824299599375

theorem tailTrace_3327008 : CollatzResearch.WordTrace tailWord_3327008 prefixEnd_3327008 1708354245353824299599375 := by
  unfold tailWord_3327008
  simp only [CollatzResearch.WordTrace]
  refine ⟨60672975365412849287090839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80897300487217132382787785 60672975365412849287090839)
  ·
    refine ⟨91009463048119273930636259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60672975365412849287090839 91009463048119273930636259)
    ·
      refine ⟨136514194572178910895954389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91009463048119273930636259 136514194572178910895954389)
      ·
        refine ⟨3199551435285443224123931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 136514194572178910895954389 3199551435285443224123931)
        ·
          refine ⟨4799327152928164836185897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3199551435285443224123931 4799327152928164836185897)
          ·
            refine ⟨3599495364696123627139423, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4799327152928164836185897 3599495364696123627139423)
            ·
              refine ⟨5399243047044185440709135, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3599495364696123627139423 5399243047044185440709135)
              ·
                refine ⟨8098864570566278161063703, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5399243047044185440709135 8098864570566278161063703)
                ·
                  refine ⟨12148296855849417241595555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8098864570566278161063703 12148296855849417241595555)
                  ·
                    refine ⟨18222445283774125862393333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12148296855849417241595555 18222445283774125862393333)
                    ·
                      refine ⟨1708354245353824299599375, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 18222445283774125862393333 1708354245353824299599375)
                      ·
                        rfl

theorem cell23_3327008_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 7, 1, 2, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 7, 1, 2, 1, 1, 1, 1, 5].length) (baseStart_3327008 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3327008 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3327008 prefixEnd_3327008 := by exact prefixLift 3327008
  have htrace : WordTrace (prefixWord ++ tailWord_3327008) baseStart_3327008 baseEnd_3327008 := by
    simpa [prefixWord, tailWord_3327008, baseEnd_3327008] using wordTrace_append hprefix tailTrace_3327008
  have hstable : (prefixWord ++ tailWord_3327008).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3327008).length < 2 ^ (prefixWord ++ tailWord_3327008).sum := by decide
  have hdescent : baseEnd_3327008 < baseStart_3327008 := by decide
  rcases family_descends (prefixWord ++ tailWord_3327008) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3327038 : List Nat := [4, 2, 1, 3, 1, 2, 2, 1, 1, 3, 3]
def baseStart_3327038 : Nat := 118140960795 + 3327038 * 2 ^ 59
def prefixEnd_3327038 : Nat := 4983230072969 + 3 ^ 40 * 3327038 * 2
def baseEnd_3327038 : Nat := 1708369649773459182224237

theorem tailTrace_3327038 : CollatzResearch.WordTrace tailWord_3327038 prefixEnd_3327038 1708369649773459182224237 := by
  unfold tailWord_3327038
  simp only [CollatzResearch.WordTrace]
  refine ⟨15168380615089626712221721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 80898029947144675798515845 15168380615089626712221721)
  ·
    refine ⟨11376285461317220034166291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15168380615089626712221721 11376285461317220034166291)
    ·
      refine ⟨17064428191975830051249437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11376285461317220034166291 17064428191975830051249437)
      ·
        refine ⟨6399160571990936269218539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17064428191975830051249437 6399160571990936269218539)
        ·
          refine ⟨9598740857986404403827809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6399160571990936269218539 9598740857986404403827809)
          ·
            refine ⟨7199055643489803302870857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9598740857986404403827809 7199055643489803302870857)
            ·
              refine ⟨5399291732617352477153143, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7199055643489803302870857 5399291732617352477153143)
              ·
                refine ⟨8098937598926028715729715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5399291732617352477153143 8098937598926028715729715)
                ·
                  refine ⟨12148406398389043073594573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8098937598926028715729715 12148406398389043073594573)
                  ·
                    refine ⟨4555652399395891152597965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12148406398389043073594573 4555652399395891152597965)
                    ·
                      refine ⟨1708369649773459182224237, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4555652399395891152597965 1708369649773459182224237)
                      ·
                        rfl

theorem cell23_3327038_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 2, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 2, 2, 1, 1, 3, 3].length) (baseStart_3327038 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3327038 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3327038 prefixEnd_3327038 := by exact prefixLift 3327038
  have htrace : WordTrace (prefixWord ++ tailWord_3327038) baseStart_3327038 baseEnd_3327038 := by
    simpa [prefixWord, tailWord_3327038, baseEnd_3327038] using wordTrace_append hprefix tailTrace_3327038
  have hstable : (prefixWord ++ tailWord_3327038).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3327038).length < 2 ^ (prefixWord ++ tailWord_3327038).sum := by decide
  have hdescent : baseEnd_3327038 < baseStart_3327038 := by decide
  rcases family_descends (prefixWord ++ tailWord_3327038) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3327061 : List Nat := [1, 3, 2, 2, 1, 2, 1, 4, 1, 4, 2]
def baseStart_3327061 : Nat := 118140960795 + 3327061 * 2 ^ 59
def prefixEnd_3327061 : Nat := 4983230072969 + 3 ^ 40 * 3327061 * 2
def baseEnd_3327061 : Nat := 1708381459828512592236631

theorem tailTrace_3327061 : CollatzResearch.WordTrace tailWord_3327061 prefixEnd_3327061 1708381459828512592236631 := by
  unfold tailWord_3327061
  simp only [CollatzResearch.WordTrace]
  refine ⟨121347883799633688625861037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80898589199755792417240691 121347883799633688625861037)
  ·
    refine ⟨45505456424862633234697889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 121347883799633688625861037 45505456424862633234697889)
    ·
      refine ⟨34129092318646974926023417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45505456424862633234697889 34129092318646974926023417)
      ·
        refine ⟨25596819238985231194517563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34129092318646974926023417 25596819238985231194517563)
        ·
          refine ⟨38395228858477846791776345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25596819238985231194517563 38395228858477846791776345)
          ·
            refine ⟨28796421643858385093832259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38395228858477846791776345 28796421643858385093832259)
            ·
              refine ⟨43194632465787577640748389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28796421643858385093832259 43194632465787577640748389)
              ·
                refine ⟨8098993587335170807640323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 43194632465787577640748389 8098993587335170807640323)
                ·
                  refine ⟨12148490381002756211460485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8098993587335170807640323 12148490381002756211460485)
                  ·
                    refine ⟨2277841946438016789648841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 12148490381002756211460485 2277841946438016789648841)
                    ·
                      refine ⟨1708381459828512592236631, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2277841946438016789648841 1708381459828512592236631)
                      ·
                        rfl

theorem cell23_3327061_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 1, 4, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 1, 4, 1, 4, 2].length) (baseStart_3327061 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3327061 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3327061 prefixEnd_3327061 := by exact prefixLift 3327061
  have htrace : WordTrace (prefixWord ++ tailWord_3327061) baseStart_3327061 baseEnd_3327061 := by
    simpa [prefixWord, tailWord_3327061, baseEnd_3327061] using wordTrace_append hprefix tailTrace_3327061
  have hstable : (prefixWord ++ tailWord_3327061).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3327061).length < 2 ^ (prefixWord ++ tailWord_3327061).sum := by decide
  have hdescent : baseEnd_3327061 < baseStart_3327061 := by decide
  rcases family_descends (prefixWord ++ tailWord_3327061) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3327084 : List Nat := [2, 2, 1, 1, 3, 2, 4, 1, 7]
def baseStart_3327084 : Nat := 118140960795 + 3327084 * 2 ^ 59
def prefixEnd_3327084 : Nat := 4983230072969 + 3 ^ 40 * 3327084 * 2
def baseEnd_3327084 : Nat := 189821474431507333583225

theorem tailTrace_3327084 : CollatzResearch.WordTrace tailWord_3327084 prefixEnd_3327084 189821474431507333583225 := by
  unfold tailWord_3327084
  simp only [CollatzResearch.WordTrace]
  refine ⟨60674361339275181776974153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80899148452366909035965537 60674361339275181776974153)
  ·
    refine ⟨45505771004456386332730615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60674361339275181776974153 45505771004456386332730615)
    ·
      refine ⟨68258656506684579499095923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45505771004456386332730615 68258656506684579499095923)
      ·
        refine ⟨102387984760026869248643885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68258656506684579499095923 102387984760026869248643885)
        ·
          refine ⟨38395494285010075968241457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 102387984760026869248643885 38395494285010075968241457)
          ·
            refine ⟨28796620713757556976181093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38395494285010075968241457 28796620713757556976181093)
            ·
              refine ⟨5399366383829541933033955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 28796620713757556976181093 5399366383829541933033955)
              ·
                refine ⟨8099049575744312899550933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5399366383829541933033955 8099049575744312899550933)
                ·
                  refine ⟨189821474431507333583225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 8099049575744312899550933 189821474431507333583225)
                  ·
                    rfl

theorem cell23_3327084_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 7].length) (baseStart_3327084 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3327084 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3327084 prefixEnd_3327084 := by exact prefixLift 3327084
  have htrace : WordTrace (prefixWord ++ tailWord_3327084) baseStart_3327084 baseEnd_3327084 := by
    simpa [prefixWord, tailWord_3327084, baseEnd_3327084] using wordTrace_append hprefix tailTrace_3327084
  have hstable : (prefixWord ++ tailWord_3327084).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3327084).length < 2 ^ (prefixWord ++ tailWord_3327084).sum := by decide
  have hdescent : baseEnd_3327084 < baseStart_3327084 := by decide
  rcases family_descends (prefixWord ++ tailWord_3327084) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3327095 : List Nat := [1, 1, 3, 1, 1, 4, 5, 1, 2, 2, 2]
def baseStart_3327095 : Nat := 118140960795 + 3327095 * 2 ^ 59
def prefixEnd_3327095 : Nat := 4983230072969 + 3 ^ 40 * 3327095 * 2
def baseEnd_3327095 : Nat := 1708398918170765459211475

theorem tailTrace_3327095 : CollatzResearch.WordTrace tailWord_3327095 prefixEnd_3327095 1708398918170765459211475 := by
  unfold tailWord_3327095
  simp only [CollatzResearch.WordTrace]
  refine ⟨121349123881510512432598739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80899415921007008288399159 121349123881510512432598739)
  ·
    refine ⟨182023685822265768648898109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121349123881510512432598739 182023685822265768648898109)
    ·
      refine ⟨68258882183349663243336791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 182023685822265768648898109 68258882183349663243336791)
      ·
        refine ⟨102388323275024494865005187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68258882183349663243336791 102388323275024494865005187)
        ·
          refine ⟨153582484912536742297507781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 102388323275024494865005187 153582484912536742297507781)
          ·
            refine ⟨28796715921100639180782709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 153582484912536742297507781 28796715921100639180782709)
            ·
              refine ⟨2699692117603184923198379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 28796715921100639180782709 2699692117603184923198379)
              ·
                refine ⟨4049538176404777384797569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2699692117603184923198379 4049538176404777384797569)
                ·
                  refine ⟨3037153632303583038598177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4049538176404777384797569 3037153632303583038598177)
                  ·
                    refine ⟨2277865224227687278948633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3037153632303583038598177 2277865224227687278948633)
                    ·
                      refine ⟨1708398918170765459211475, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2277865224227687278948633 1708398918170765459211475)
                      ·
                        rfl

theorem cell23_3327095_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 5, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 5, 1, 2, 2, 2].length) (baseStart_3327095 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3327095 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3327095 prefixEnd_3327095 := by exact prefixLift 3327095
  have htrace : WordTrace (prefixWord ++ tailWord_3327095) baseStart_3327095 baseEnd_3327095 := by
    simpa [prefixWord, tailWord_3327095, baseEnd_3327095] using wordTrace_append hprefix tailTrace_3327095
  have hstable : (prefixWord ++ tailWord_3327095).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3327095).length < 2 ^ (prefixWord ++ tailWord_3327095).sum := by decide
  have hdescent : baseEnd_3327095 < baseStart_3327095 := by decide
  rcases family_descends (prefixWord ++ tailWord_3327095) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3327114 : List Nat := [3, 1, 2, 3, 1, 1, 1, 3, 1, 7]
def baseStart_3327114 : Nat := 118140960795 + 3327114 * 2 ^ 59
def prefixEnd_3327114 : Nat := 4983230072969 + 3 ^ 40 * 3327114 * 2
def baseEnd_3327114 : Nat := 569469558101066961624629

theorem tailTrace_3327114 : CollatzResearch.WordTrace tailWord_3327114 prefixEnd_3327114 569469558101066961624629 := by
  unfold tailWord_3327114
  simp only [CollatzResearch.WordTrace]
  refine ⟨30337454217110419669385099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 80899877912294452451693597 30337454217110419669385099)
  ·
    refine ⟨45506181325665629504077649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30337454217110419669385099 45506181325665629504077649)
    ·
      refine ⟨34129635994249222128058237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45506181325665629504077649 34129635994249222128058237)
      ·
        refine ⟨12798613497843458298021839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 34129635994249222128058237 12798613497843458298021839)
        ·
          refine ⟨19197920246765187447032759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12798613497843458298021839 19197920246765187447032759)
          ·
            refine ⟨28796880370147781170549139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19197920246765187447032759 28796880370147781170549139)
            ·
              refine ⟨43195320555221671755823709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28796880370147781170549139 43195320555221671755823709)
              ·
                refine ⟨16198245208208126908433891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 43195320555221671755823709 16198245208208126908433891)
                ·
                  refine ⟨24297367812312190362650837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16198245208208126908433891 24297367812312190362650837)
                  ·
                    refine ⟨569469558101066961624629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 24297367812312190362650837 569469558101066961624629)
                    ·
                      rfl

theorem cell23_3327114_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 1, 3, 1, 7].length) (baseStart_3327114 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3327114 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3327114 prefixEnd_3327114 := by exact prefixLift 3327114
  have htrace : WordTrace (prefixWord ++ tailWord_3327114) baseStart_3327114 baseEnd_3327114 := by
    simpa [prefixWord, tailWord_3327114, baseEnd_3327114] using wordTrace_append hprefix tailTrace_3327114
  have hstable : (prefixWord ++ tailWord_3327114).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3327114).length < 2 ^ (prefixWord ++ tailWord_3327114).sum := by decide
  have hdescent : baseEnd_3327114 < baseStart_3327114 := by decide
  rcases family_descends (prefixWord ++ tailWord_3327114) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3327118 : List Nat := [4, 1, 1, 3, 2, 1, 3, 3, 5]
def baseStart_3327118 : Nat := 118140960795 + 3327118 * 2 ^ 59
def prefixEnd_3327118 : Nat := 4983230072969 + 3 ^ 40 * 3327118 * 2
def baseEnd_3327118 : Nat := 189823414247313207691541

theorem tailTrace_3327118 : CollatzResearch.WordTrace tailWord_3327118 prefixEnd_3327118 189823414247313207691541 := by
  unfold tailWord_3327118
  simp only [CollatzResearch.WordTrace]
  refine ⟨15168745345053398420085751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 80899975173618124907124005 15168745345053398420085751)
  ·
    refine ⟨22753118017580097630128627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15168745345053398420085751 22753118017580097630128627)
    ·
      refine ⟨34129677026370146445192941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22753118017580097630128627 34129677026370146445192941)
      ·
        refine ⟨12798628884888804916947353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 34129677026370146445192941 12798628884888804916947353)
        ·
          refine ⟨9598971663666603687710515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12798628884888804916947353 9598971663666603687710515)
          ·
            refine ⟨14398457495499905531565773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9598971663666603687710515 14398457495499905531565773)
            ·
              refine ⟨5399421560812464574337165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14398457495499905531565773 5399421560812464574337165)
              ·
                refine ⟨2024783085304674215376437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5399421560812464574337165 2024783085304674215376437)
                ·
                  refine ⟨189823414247313207691541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2024783085304674215376437 189823414247313207691541)
                  ·
                    rfl

theorem cell23_3327118_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 1, 3, 3, 5].length) (baseStart_3327118 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3327118 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3327118 prefixEnd_3327118 := by exact prefixLift 3327118
  have htrace : WordTrace (prefixWord ++ tailWord_3327118) baseStart_3327118 baseEnd_3327118 := by
    simpa [prefixWord, tailWord_3327118, baseEnd_3327118] using wordTrace_append hprefix tailTrace_3327118
  have hstable : (prefixWord ++ tailWord_3327118).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3327118).length < 2 ^ (prefixWord ++ tailWord_3327118).sum := by decide
  have hdescent : baseEnd_3327118 < baseStart_3327118 := by decide
  rcases family_descends (prefixWord ++ tailWord_3327118) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3327135 : List Nat := [1, 1, 2, 6, 2, 1, 3, 2, 5]
def baseStart_3327135 : Nat := 118140960795 + 3327135 * 2 ^ 59
def prefixEnd_3327135 : Nat := 4983230072969 + 3 ^ 40 * 3327135 * 2
def baseEnd_3327135 : Nat := 189824384155216144745699

theorem tailTrace_3327135 : CollatzResearch.WordTrace tailWord_3327135 prefixEnd_3327135 189824384155216144745699 := by
  unfold tailWord_3327135
  simp only [CollatzResearch.WordTrace]
  refine ⟨121350582801365599264054859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80900388534243732842703239 121350582801365599264054859)
  ·
    refine ⟨182025874202048398896082289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121350582801365599264054859 182025874202048398896082289)
    ·
      refine ⟨136519405651536299172061717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 182025874202048398896082289 136519405651536299172061717)
      ·
        refine ⟨6399347139915764023690393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 136519405651536299172061717 6399347139915764023690393)
        ·
          refine ⟨4799510354936823017767795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6399347139915764023690393 4799510354936823017767795)
          ·
            refine ⟨7199265532405234526651693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4799510354936823017767795 7199265532405234526651693)
            ·
              refine ⟨2699724574651962947494385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7199265532405234526651693 2699724574651962947494385)
              ·
                refine ⟨2024793430988972210620789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2699724574651962947494385 2024793430988972210620789)
                ·
                  refine ⟨189824384155216144745699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2024793430988972210620789 189824384155216144745699)
                  ·
                    rfl

theorem cell23_3327135_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 2, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 2, 1, 3, 2, 5].length) (baseStart_3327135 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3327135 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3327135 prefixEnd_3327135 := by exact prefixLift 3327135
  have htrace : WordTrace (prefixWord ++ tailWord_3327135) baseStart_3327135 baseEnd_3327135 := by
    simpa [prefixWord, tailWord_3327135, baseEnd_3327135] using wordTrace_append hprefix tailTrace_3327135
  have hstable : (prefixWord ++ tailWord_3327135).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3327135).length < 2 ^ (prefixWord ++ tailWord_3327135).sum := by decide
  have hdescent : baseEnd_3327135 < baseStart_3327135 := by decide
  rcases family_descends (prefixWord ++ tailWord_3327135) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3327151 : List Nat := [1, 1, 2, 1, 2, 3, 2, 3, 2, 4, 2]
def baseStart_3327151 : Nat := 118140960795 + 3327151 * 2 ^ 59
def prefixEnd_3327151 : Nat := 4983230072969 + 3 ^ 40 * 3327151 * 2
def baseEnd_3327151 : Nat := 1708427673087417240111217

theorem tailTrace_3327151 : CollatzResearch.WordTrace tailWord_3327151 prefixEnd_3327151 1708427673087417240111217 := by
  unfold tailWord_3327151
  simp only [CollatzResearch.WordTrace]
  refine ⟨121351166369307633996637307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80900777579538422664424871 121351166369307633996637307)
  ·
    refine ⟨182026749553961450994955961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121351166369307633996637307 182026749553961450994955961)
    ·
      refine ⟨136520062165471088246216971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 182026749553961450994955961 136520062165471088246216971)
      ·
        refine ⟨204780093248206632369325457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 136520062165471088246216971 204780093248206632369325457)
        ·
          refine ⟨153585069936154974276994093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 204780093248206632369325457 153585069936154974276994093)
          ·
            refine ⟨57594401226058115353872785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 153585069936154974276994093 57594401226058115353872785)
            ·
              refine ⟨43195800919543586515404589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 57594401226058115353872785 43195800919543586515404589)
              ·
                refine ⟨16198425344828844943276721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 43195800919543586515404589 16198425344828844943276721)
                ·
                  refine ⟨12148819008621633707457541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16198425344828844943276721 12148819008621633707457541)
                  ·
                    refine ⟨2277903564116556320148289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 12148819008621633707457541 2277903564116556320148289)
                    ·
                      refine ⟨1708427673087417240111217, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2277903564116556320148289 1708427673087417240111217)
                      ·
                        rfl

theorem cell23_3327151_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 2, 3, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 2, 3, 2, 4, 2].length) (baseStart_3327151 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3327151 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3327151 prefixEnd_3327151 := by exact prefixLift 3327151
  have htrace : WordTrace (prefixWord ++ tailWord_3327151) baseStart_3327151 baseEnd_3327151 := by
    simpa [prefixWord, tailWord_3327151, baseEnd_3327151] using wordTrace_append hprefix tailTrace_3327151
  have hstable : (prefixWord ++ tailWord_3327151).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3327151).length < 2 ^ (prefixWord ++ tailWord_3327151).sum := by decide
  have hdescent : baseEnd_3327151 < baseStart_3327151 := by decide
  rcases family_descends (prefixWord ++ tailWord_3327151) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3327168 : List Nat := [2, 1, 1, 2, 6, 1, 2, 1, 2, 1, 4]
def baseStart_3327168 : Nat := 118140960795 + 3327168 * 2 ^ 59
def prefixEnd_3327168 : Nat := 4983230072969 + 3 ^ 40 * 3327168 * 2
def baseEnd_3327168 : Nat := 1708436402258543673598639

theorem tailTrace_3327168 : CollatzResearch.WordTrace tailWord_3327168 prefixEnd_3327168 1708436402258543673598639 := by
  unfold tailWord_3327168
  simp only [CollatzResearch.WordTrace]
  refine ⟨60675893205123022950003079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80901190940164030600004105 60675893205123022950003079)
  ·
    refine ⟨91013839807684534425004619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60675893205123022950003079 91013839807684534425004619)
    ·
      refine ⟨136520759711526801637506929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91013839807684534425004619 136520759711526801637506929)
      ·
        refine ⟨102390569783645101228130197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 136520759711526801637506929 102390569783645101228130197)
        ·
          refine ⟨4799557958608364120068603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 102390569783645101228130197 4799557958608364120068603)
          ·
            refine ⟨7199336937912546180102905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4799557958608364120068603 7199336937912546180102905)
            ·
              refine ⟨5399502703434409635077179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7199336937912546180102905 5399502703434409635077179)
              ·
                refine ⟨8099254055151614452615769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5399502703434409635077179 8099254055151614452615769)
                ·
                  refine ⟨6074440541363710839461827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8099254055151614452615769 6074440541363710839461827)
                  ·
                    refine ⟨9111660812045566259192741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6074440541363710839461827 9111660812045566259192741)
                    ·
                      refine ⟨1708436402258543673598639, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9111660812045566259192741 1708436402258543673598639)
                      ·
                        rfl

theorem cell23_3327168_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 6, 1, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 6, 1, 2, 1, 2, 1, 4].length) (baseStart_3327168 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3327168 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3327168 prefixEnd_3327168 := by exact prefixLift 3327168
  have htrace : WordTrace (prefixWord ++ tailWord_3327168) baseStart_3327168 baseEnd_3327168 := by
    simpa [prefixWord, tailWord_3327168, baseEnd_3327168] using wordTrace_append hprefix tailTrace_3327168
  have hstable : (prefixWord ++ tailWord_3327168).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3327168).length < 2 ^ (prefixWord ++ tailWord_3327168).sum := by decide
  have hdescent : baseEnd_3327168 < baseStart_3327168 := by decide
  rcases family_descends (prefixWord ++ tailWord_3327168) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3327194 : List Nat := [3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 6]
def baseStart_3327194 : Nat := 118140960795 + 3327194 * 2 ^ 59
def prefixEnd_3327194 : Nat := 4983230072969 + 3 ^ 40 * 3327194 * 2
def baseEnd_3327194 : Nat := 1708449752755560571873519

theorem tailTrace_3327194 : CollatzResearch.WordTrace tailWord_3327194 prefixEnd_3327194 1708449752755560571873519 := by
  unfold tailWord_3327194
  simp only [CollatzResearch.WordTrace]
  refine ⟨30338183677037963085113159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 80901823138767901560301757 30338183677037963085113159)
  ·
    refine ⟨45507275515556944627669739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30338183677037963085113159 45507275515556944627669739)
    ·
      refine ⟨68260913273335416941504609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45507275515556944627669739 68260913273335416941504609)
      ·
        refine ⟨51195684955001562706128457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 68260913273335416941504609 51195684955001562706128457)
        ·
          refine ⟨38396763716251172029596343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51195684955001562706128457 38396763716251172029596343)
          ·
            refine ⟨57595145574376758044394515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38396763716251172029596343 57595145574376758044394515)
            ·
              refine ⟨86392718361565137066591773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 57595145574376758044394515 86392718361565137066591773)
              ·
                refine ⟨32397269385586926399971915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 86392718361565137066591773 32397269385586926399971915)
                ·
                  refine ⟨48595904078380389599957873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32397269385586926399971915 48595904078380389599957873)
                  ·
                    refine ⟨36446928058785292199968405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 48595904078380389599957873 36446928058785292199968405)
                    ·
                      refine ⟨1708449752755560571873519, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 36446928058785292199968405 1708449752755560571873519)
                      ·
                        rfl

theorem cell23_3327194_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 6].length) (baseStart_3327194 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3327194 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3327194 prefixEnd_3327194 := by exact prefixLift 3327194
  have htrace : WordTrace (prefixWord ++ tailWord_3327194) baseStart_3327194 baseEnd_3327194 := by
    simpa [prefixWord, tailWord_3327194, baseEnd_3327194] using wordTrace_append hprefix tailTrace_3327194
  have hstable : (prefixWord ++ tailWord_3327194).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3327194).length < 2 ^ (prefixWord ++ tailWord_3327194).sum := by decide
  have hdescent : baseEnd_3327194 < baseStart_3327194 := by decide
  rcases family_descends (prefixWord ++ tailWord_3327194) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3327235 : List Nat := [1, 1, 1, 3, 2, 4, 1, 5, 1, 1, 3]
def baseStart_3327235 : Nat := 118140960795 + 3327235 * 2 ^ 59
def prefixEnd_3327235 : Nat := 4983230072969 + 3 ^ 40 * 3327235 * 2
def baseEnd_3327235 : Nat := 1708470805462394911460831

theorem tailTrace_3327235 : CollatzResearch.WordTrace tailWord_3327235 prefixEnd_3327235 1708470805462394911460831 := by
  unfold tailWord_3327235
  simp only [CollatzResearch.WordTrace]
  refine ⟨121354230101003316342695159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80902820067335544228463439 121354230101003316342695159)
  ·
    refine ⟨182031345151504974514042739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121354230101003316342695159 182031345151504974514042739)
    ·
      refine ⟨273047017727257461771064109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 182031345151504974514042739 273047017727257461771064109)
      ·
        refine ⟨102392631647721548164149041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 273047017727257461771064109 102392631647721548164149041)
        ·
          refine ⟨76794473735791161123111781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 102392631647721548164149041 76794473735791161123111781)
          ·
            refine ⟨14398963825460842710583459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 76794473735791161123111781 14398963825460842710583459)
            ·
              refine ⟨21598445738191264065875189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14398963825460842710583459 21598445738191264065875189)
              ·
                refine ⟨2024854287955431006175799, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 21598445738191264065875189 2024854287955431006175799)
                ·
                  refine ⟨3037281431933146509263699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2024854287955431006175799 3037281431933146509263699)
                  ·
                    refine ⟨4555922147899719763895549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3037281431933146509263699 4555922147899719763895549)
                    ·
                      refine ⟨1708470805462394911460831, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4555922147899719763895549 1708470805462394911460831)
                      ·
                        rfl

theorem cell23_3327235_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 4, 1, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 4, 1, 5, 1, 1, 3].length) (baseStart_3327235 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3327235 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3327235 prefixEnd_3327235 := by exact prefixLift 3327235
  have htrace : WordTrace (prefixWord ++ tailWord_3327235) baseStart_3327235 baseEnd_3327235 := by
    simpa [prefixWord, tailWord_3327235, baseEnd_3327235] using wordTrace_append hprefix tailTrace_3327235
  have hstable : (prefixWord ++ tailWord_3327235).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3327235).length < 2 ^ (prefixWord ++ tailWord_3327235).sum := by decide
  have hdescent : baseEnd_3327235 < baseStart_3327235 := by decide
  rcases family_descends (prefixWord ++ tailWord_3327235) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3327281 : List Nat := [1, 2, 2, 3, 3, 2, 1, 9]
def baseStart_3327281 : Nat := 118140960795 + 3327281 * 2 ^ 59
def prefixEnd_3327281 : Nat := 4983230072969 + 3 ^ 40 * 3327281 * 2
def baseEnd_3327281 : Nat := 63277571317500064129097

theorem tailTrace_3327281 : CollatzResearch.WordTrace tailWord_3327281 prefixEnd_3327281 63277571317500064129097 := by
  unfold tailWord_3327281
  simp only [CollatzResearch.WordTrace]
  refine ⟨121355907858836666198869697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80903938572557777465913131 121355907858836666198869697)
  ·
    refine ⟨91016930894127499649152273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 121355907858836666198869697 91016930894127499649152273)
    ·
      refine ⟨68262698170595624736864205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 91016930894127499649152273 68262698170595624736864205)
      ·
        refine ⟨25598511813973359276324077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 68262698170595624736864205 25598511813973359276324077)
        ·
          refine ⟨9599441930240009728621529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25598511813973359276324077 9599441930240009728621529)
          ·
            refine ⟨7199581447680007296466147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9599441930240009728621529 7199581447680007296466147)
            ·
              refine ⟨10799372171520010944699221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7199581447680007296466147 10799372171520010944699221)
              ·
                refine ⟨63277571317500064129097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 10799372171520010944699221 63277571317500064129097)
                ·
                  rfl

theorem cell23_3327281_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 2, 1, 9].length) (baseStart_3327281 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3327281 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3327281 prefixEnd_3327281 := by exact prefixLift 3327281
  have htrace : WordTrace (prefixWord ++ tailWord_3327281) baseStart_3327281 baseEnd_3327281 := by
    simpa [prefixWord, tailWord_3327281, baseEnd_3327281] using wordTrace_append hprefix tailTrace_3327281
  have hstable : (prefixWord ++ tailWord_3327281).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3327281).length < 2 ^ (prefixWord ++ tailWord_3327281).sum := by decide
  have hdescent : baseEnd_3327281 < baseStart_3327281 := by decide
  rcases family_descends (prefixWord ++ tailWord_3327281) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3327342 : List Nat := [4, 1, 2, 4, 1, 1, 1, 2, 1, 3, 3]
def baseStart_3327342 : Nat := 118140960795 + 3327342 * 2 ^ 59
def prefixEnd_3327342 : Nat := 4983230072969 + 3 ^ 40 * 3327342 * 2
def baseEnd_3327342 : Nat := 1708525747892425992822839

theorem tailTrace_3327342 : CollatzResearch.WordTrace tailWord_3327342 prefixEnd_3327342 1708525747892425992822839 := by
  unfold tailWord_3327342
  simp only [CollatzResearch.WordTrace]
  refine ⟨15169766588951959202105035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 80905421807743782411226853 15169766588951959202105035)
  ·
    refine ⟨22754649883427938803157553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15169766588951959202105035 22754649883427938803157553)
    ·
      refine ⟨17065987412570954102368165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22754649883427938803157553 17065987412570954102368165)
      ·
        refine ⟨3199872639857053894194031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 17065987412570954102368165 3199872639857053894194031)
        ·
          refine ⟨4799808959785580841291047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3199872639857053894194031 4799808959785580841291047)
          ·
            refine ⟨7199713439678371261936571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4799808959785580841291047 7199713439678371261936571)
            ·
              refine ⟨10799570159517556892904857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7199713439678371261936571 10799570159517556892904857)
              ·
                refine ⟨8099677619638167669678643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10799570159517556892904857 8099677619638167669678643)
                ·
                  refine ⟨12149516429457251504517965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8099677619638167669678643 12149516429457251504517965)
                  ·
                    refine ⟨4556068661046469314194237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12149516429457251504517965 4556068661046469314194237)
                    ·
                      refine ⟨1708525747892425992822839, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4556068661046469314194237 1708525747892425992822839)
                      ·
                        rfl

theorem cell23_3327342_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 4, 1, 1, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 4, 1, 1, 1, 2, 1, 3, 3].length) (baseStart_3327342 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3327342 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3327342 prefixEnd_3327342 := by exact prefixLift 3327342
  have htrace : WordTrace (prefixWord ++ tailWord_3327342) baseStart_3327342 baseEnd_3327342 := by
    simpa [prefixWord, tailWord_3327342, baseEnd_3327342] using wordTrace_append hprefix tailTrace_3327342
  have hstable : (prefixWord ++ tailWord_3327342).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3327342).length < 2 ^ (prefixWord ++ tailWord_3327342).sum := by decide
  have hdescent : baseEnd_3327342 < baseStart_3327342 := by decide
  rcases family_descends (prefixWord ++ tailWord_3327342) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3327351 : List Nat := [1, 1, 3, 1, 1, 2, 3, 3, 2, 1, 5]
def baseStart_3327351 : Nat := 118140960795 + 3327351 * 2 ^ 59
def prefixEnd_3327351 : Nat := 4983230072969 + 3 ^ 40 * 3327351 * 2
def baseEnd_3327351 : Nat := 1708530369218316457610297

theorem tailTrace_3327351 : CollatzResearch.WordTrace tailWord_3327351 prefixEnd_3327351 1708530369218316457610297 := by
  unfold tailWord_3327351
  simp only [CollatzResearch.WordTrace]
  refine ⟨121358460968583068153917907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80905640645722045435945271 121358460968583068153917907)
  ·
    refine ⟨182037691452874602230876861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121358460968583068153917907 182037691452874602230876861)
    ·
      refine ⟨68264134294827975836578823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 182037691452874602230876861 68264134294827975836578823)
      ·
        refine ⟨102396201442241963754868235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68264134294827975836578823 102396201442241963754868235)
        ·
          refine ⟨153594302163362945632302353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 102396201442241963754868235 153594302163362945632302353)
          ·
            refine ⟨115195726622522209224226765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 153594302163362945632302353 115195726622522209224226765)
            ·
              refine ⟨43198397483445828459085037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 115195726622522209224226765 43198397483445828459085037)
              ·
                refine ⟨16199399056292185672156889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 43198397483445828459085037 16199399056292185672156889)
                ·
                  refine ⟨12149549292219139254117667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16199399056292185672156889 12149549292219139254117667)
                  ·
                    refine ⟨18224323938328708881176501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12149549292219139254117667 18224323938328708881176501)
                    ·
                      refine ⟨1708530369218316457610297, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 18224323938328708881176501 1708530369218316457610297)
                      ·
                        rfl

theorem cell23_3327351_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 3, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 3, 3, 2, 1, 5].length) (baseStart_3327351 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3327351 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3327351 prefixEnd_3327351 := by exact prefixLift 3327351
  have htrace : WordTrace (prefixWord ++ tailWord_3327351) baseStart_3327351 baseEnd_3327351 := by
    simpa [prefixWord, tailWord_3327351, baseEnd_3327351] using wordTrace_append hprefix tailTrace_3327351
  have hstable : (prefixWord ++ tailWord_3327351).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3327351).length < 2 ^ (prefixWord ++ tailWord_3327351).sum := by decide
  have hdescent : baseEnd_3327351 < baseStart_3327351 := by decide
  rcases family_descends (prefixWord ++ tailWord_3327351) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3327365 : List Nat := [1, 3, 1, 1, 3, 1, 2, 3, 4, 2, 2]
def baseStart_3327365 : Nat := 118140960795 + 3327365 * 2 ^ 59
def prefixEnd_3327365 : Nat := 4983230072969 + 3 ^ 40 * 3327365 * 2
def baseEnd_3327365 : Nat := 1708537557947479402835233

theorem tailTrace_3327365 : CollatzResearch.WordTrace tailWord_3327365 prefixEnd_3327365 1708537557947479402835233 := by
  unfold tailWord_3327365
  simp only [CollatzResearch.WordTrace]
  refine ⟨121358971590532348544927549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80905981060354899029951699 121358971590532348544927549)
  ·
    refine ⟨45509614346449630704347831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 121358971590532348544927549 45509614346449630704347831)
    ·
      refine ⟨68264421519674446056521747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45509614346449630704347831 68264421519674446056521747)
      ·
        refine ⟨102396632279511669084782621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68264421519674446056521747 102396632279511669084782621)
        ·
          refine ⟨38398737104816875906793483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 102396632279511669084782621 38398737104816875906793483)
          ·
            refine ⟨57598105657225313860190225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38398737104816875906793483 57598105657225313860190225)
            ·
              refine ⟨43198579242918985395142669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 57598105657225313860190225 43198579242918985395142669)
              ·
                refine ⟨16199467216094619523178501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 43198579242918985395142669 16199467216094619523178501)
                ·
                  refine ⟨3037400103017741160595969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 16199467216094619523178501 3037400103017741160595969)
                  ·
                    refine ⟨2278050077263305870446977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3037400103017741160595969 2278050077263305870446977)
                    ·
                      refine ⟨1708537557947479402835233, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2278050077263305870446977 1708537557947479402835233)
                      ·
                        rfl

theorem cell23_3327365_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 2, 3, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 2, 3, 4, 2, 2].length) (baseStart_3327365 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3327365 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3327365 prefixEnd_3327365 := by exact prefixLift 3327365
  have htrace : WordTrace (prefixWord ++ tailWord_3327365) baseStart_3327365 baseEnd_3327365 := by
    simpa [prefixWord, tailWord_3327365, baseEnd_3327365] using wordTrace_append hprefix tailTrace_3327365
  have hstable : (prefixWord ++ tailWord_3327365).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3327365).length < 2 ^ (prefixWord ++ tailWord_3327365).sum := by decide
  have hdescent : baseEnd_3327365 < baseStart_3327365 := by decide
  rcases family_descends (prefixWord ++ tailWord_3327365) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3327368 : List Nat := [2, 1, 3, 3, 1, 2, 1, 1, 2, 4, 3]
def baseStart_3327368 : Nat := 118140960795 + 3327368 * 2 ^ 59
def prefixEnd_3327368 : Nat := 4983230072969 + 3 ^ 40 * 3327368 * 2
def baseEnd_3327368 : Nat := 1708539098389442891097719

theorem tailTrace_3327368 : CollatzResearch.WordTrace tailWord_3327368 prefixEnd_3327368 1708539098389442891097719 := by
  unfold tailWord_3327368
  simp only [CollatzResearch.WordTrace]
  refine ⟨60679540504760740028643379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80906054006347653371524505 60679540504760740028643379)
  ·
    refine ⟨91019310757141110042965069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60679540504760740028643379 91019310757141110042965069)
    ·
      refine ⟨34132241533927916266111901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 91019310757141110042965069 34132241533927916266111901)
      ·
        refine ⟨12799590575222968599791963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 34132241533927916266111901 12799590575222968599791963)
        ·
          refine ⟨19199385862834452899687945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12799590575222968599791963 19199385862834452899687945)
          ·
            refine ⟨14399539397125839674765959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19199385862834452899687945 14399539397125839674765959)
            ·
              refine ⟨21599309095688759512148939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14399539397125839674765959 21599309095688759512148939)
              ·
                refine ⟨32398963643533139268223409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21599309095688759512148939 32398963643533139268223409)
                ·
                  refine ⟨24299222732649854451167557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32398963643533139268223409 24299222732649854451167557)
                  ·
                    refine ⟨4556104262371847709593917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 24299222732649854451167557 4556104262371847709593917)
                    ·
                      refine ⟨1708539098389442891097719, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4556104262371847709593917 1708539098389442891097719)
                      ·
                        rfl

theorem cell23_3327368_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 2, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 2, 1, 1, 2, 4, 3].length) (baseStart_3327368 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3327368 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3327368 prefixEnd_3327368 := by exact prefixLift 3327368
  have htrace : WordTrace (prefixWord ++ tailWord_3327368) baseStart_3327368 baseEnd_3327368 := by
    simpa [prefixWord, tailWord_3327368, baseEnd_3327368] using wordTrace_append hprefix tailTrace_3327368
  have hstable : (prefixWord ++ tailWord_3327368).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3327368).length < 2 ^ (prefixWord ++ tailWord_3327368).sum := by decide
  have hdescent : baseEnd_3327368 < baseStart_3327368 := by decide
  rcases family_descends (prefixWord ++ tailWord_3327368) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3327371 : List Nat := [1, 1, 1, 1, 4, 3, 2, 3, 7]
def baseStart_3327371 : Nat := 118140960795 + 3327371 * 2 ^ 59
def prefixEnd_3327371 : Nat := 4983230072969 + 3 ^ 40 * 3327371 * 2
def baseEnd_3327371 : Nat := 189837848759045153262245

theorem tailTrace_3327371 : CollatzResearch.WordTrace tailWord_3327371 prefixEnd_3327371 189837848759045153262245 := by
  unfold tailWord_3327371
  simp only [CollatzResearch.WordTrace]
  refine ⟨121359190428510611569645967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80906126952340407713097311 121359190428510611569645967)
  ·
    refine ⟨182038785642765917354468951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121359190428510611569645967 182038785642765917354468951)
    ·
      refine ⟨273058178464148876031703427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 182038785642765917354468951 273058178464148876031703427)
      ·
        refine ⟨409587267696223314047555141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 273058178464148876031703427 409587267696223314047555141)
        ·
          refine ⟨76797612693041871383916589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 409587267696223314047555141 76797612693041871383916589)
          ·
            refine ⟨28799104759890701768968721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 76797612693041871383916589 28799104759890701768968721)
            ·
              refine ⟨21599328569918026326726541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28799104759890701768968721 21599328569918026326726541)
              ·
                refine ⟨8099748213719259872522453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21599328569918026326726541 8099748213719259872522453)
                ·
                  refine ⟨189837848759045153262245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 8099748213719259872522453 189837848759045153262245)
                  ·
                    rfl

theorem cell23_3327371_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 2, 3, 7].length) (baseStart_3327371 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3327371 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3327371 prefixEnd_3327371 := by exact prefixLift 3327371
  have htrace : WordTrace (prefixWord ++ tailWord_3327371) baseStart_3327371 baseEnd_3327371 := by
    simpa [prefixWord, tailWord_3327371, baseEnd_3327371] using wordTrace_append hprefix tailTrace_3327371
  have hstable : (prefixWord ++ tailWord_3327371).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3327371).length < 2 ^ (prefixWord ++ tailWord_3327371).sum := by decide
  have hdescent : baseEnd_3327371 < baseStart_3327371 := by decide
  rcases family_descends (prefixWord ++ tailWord_3327371) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3327408 : List Nat := [2, 1, 1, 1, 2, 1, 1, 4, 1, 7, 2]
def baseStart_3327408 : Nat := 118140960795 + 3327408 * 2 ^ 59
def prefixEnd_3327408 : Nat := 4983230072969 + 3 ^ 40 * 3327408 * 2
def baseEnd_3327408 : Nat := 1708559637615622734597535

theorem tailTrace_3327408 : CollatzResearch.WordTrace tailWord_3327408 prefixEnd_3327408 1708559637615622734597535 := by
  unfold tailWord_3327408
  simp only [CollatzResearch.WordTrace]
  refine ⟨60680269964688283444371439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80907026619584377925828585 60680269964688283444371439)
  ·
    refine ⟨91020404947032425166557159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60680269964688283444371439 91020404947032425166557159)
    ·
      refine ⟨136530607420548637749835739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91020404947032425166557159 136530607420548637749835739)
      ·
        refine ⟨204795911130822956624753609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 136530607420548637749835739 204795911130822956624753609)
        ·
          refine ⟨153596933348117217468565207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 204795911130822956624753609 153596933348117217468565207)
          ·
            refine ⟨230395400022175826202847811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 153596933348117217468565207 230395400022175826202847811)
            ·
              refine ⟨345593100033263739304271717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 230395400022175826202847811 345593100033263739304271717)
              ·
                refine ⟨64798706256236951119550947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 345593100033263739304271717 64798706256236951119550947)
                ·
                  refine ⟨97198059384355426679326421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 64798706256236951119550947 97198059384355426679326421)
                  ·
                    refine ⟨2278079516820830312796713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 97198059384355426679326421 2278079516820830312796713)
                    ·
                      refine ⟨1708559637615622734597535, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2278079516820830312796713 1708559637615622734597535)
                      ·
                        rfl

theorem cell23_3327408_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 4, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 4, 1, 7, 2].length) (baseStart_3327408 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3327408 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3327408 prefixEnd_3327408 := by exact prefixLift 3327408
  have htrace : WordTrace (prefixWord ++ tailWord_3327408) baseStart_3327408 baseEnd_3327408 := by
    simpa [prefixWord, tailWord_3327408, baseEnd_3327408] using wordTrace_append hprefix tailTrace_3327408
  have hstable : (prefixWord ++ tailWord_3327408).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3327408).length < 2 ^ (prefixWord ++ tailWord_3327408).sum := by decide
  have hdescent : baseEnd_3327408 < baseStart_3327408 := by decide
  rcases family_descends (prefixWord ++ tailWord_3327408) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3327411 : List Nat := [1, 1, 1, 2, 3, 1, 1, 3, 3, 2, 5]
def baseStart_3327411 : Nat := 118140960795 + 3327411 * 2 ^ 59
def prefixEnd_3327411 : Nat := 4983230072969 + 3 ^ 40 * 3327411 * 2
def baseEnd_3327411 : Nat := 1708561178057586222860021

theorem tailTrace_3327411 : CollatzResearch.WordTrace tailWord_3327411 prefixEnd_3327411 1708561178057586222860021 := by
  unfold tailWord_3327411
  simp only [CollatzResearch.WordTrace]
  refine ⟨121360649348365698401102087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80907099565577132267401391 121360649348365698401102087)
  ·
    refine ⟨182040974022548547601653131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121360649348365698401102087 182040974022548547601653131)
    ·
      refine ⟨273061461033822821402479697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 182040974022548547601653131 273061461033822821402479697)
      ·
        refine ⟨204796095775367116051859773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 273061461033822821402479697 204796095775367116051859773)
        ·
          refine ⟨76798535915762668519447415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 204796095775367116051859773 76798535915762668519447415)
          ·
            refine ⟨115197803873644002779171123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 76798535915762668519447415 115197803873644002779171123)
            ·
              refine ⟨172796705810466004168756685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 115197803873644002779171123 172796705810466004168756685)
              ·
                refine ⟨64798764678924751563283757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 172796705810466004168756685 64798764678924751563283757)
                ·
                  refine ⟨24299536754596781836231409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 64798764678924751563283757 24299536754596781836231409)
                  ·
                    refine ⟨18224652565947586377173557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 24299536754596781836231409 18224652565947586377173557)
                    ·
                      refine ⟨1708561178057586222860021, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 18224652565947586377173557 1708561178057586222860021)
                      ·
                        rfl

theorem cell23_3327411_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 1, 3, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 1, 3, 3, 2, 5].length) (baseStart_3327411 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3327411 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3327411 prefixEnd_3327411 := by exact prefixLift 3327411
  have htrace : WordTrace (prefixWord ++ tailWord_3327411) baseStart_3327411 baseEnd_3327411 := by
    simpa [prefixWord, tailWord_3327411, baseEnd_3327411] using wordTrace_append hprefix tailTrace_3327411
  have hstable : (prefixWord ++ tailWord_3327411).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3327411).length < 2 ^ (prefixWord ++ tailWord_3327411).sum := by decide
  have hdescent : baseEnd_3327411 < baseStart_3327411 := by decide
  rcases family_descends (prefixWord ++ tailWord_3327411) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3327438 : List Nat := [4, 1, 1, 1, 2, 1, 3, 2, 1, 3, 4]
def baseStart_3327438 : Nat := 118140960795 + 3327438 * 2 ^ 59
def prefixEnd_3327438 : Nat := 4983230072969 + 3 ^ 40 * 3327438 * 2
def baseEnd_3327438 : Nat := 1708575042035257617222397

theorem tailTrace_3327438 : CollatzResearch.WordTrace tailWord_3327438 prefixEnd_3327438 1708575042035257617222397 := by
  unfold tailWord_3327438
  simp only [CollatzResearch.WordTrace]
  refine ⟨15170204264908485251541871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 80907756079511921341556645 15170204264908485251541871)
  ·
    refine ⟨22755306397362727877312807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15170204264908485251541871 22755306397362727877312807)
    ·
      refine ⟨34132959596044091815969211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22755306397362727877312807 34132959596044091815969211)
      ·
        refine ⟨51199439394066137723953817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34132959596044091815969211 51199439394066137723953817)
        ·
          refine ⟨38399579545549603292965363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51199439394066137723953817 38399579545549603292965363)
          ·
            refine ⟨57599369318324404939448045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38399579545549603292965363 57599369318324404939448045)
            ·
              refine ⟨21599763494371651852293017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 57599369318324404939448045 21599763494371651852293017)
              ·
                refine ⟨16199822620778738889219763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21599763494371651852293017 16199822620778738889219763)
                ·
                  refine ⟨24299733931168108333829645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16199822620778738889219763 24299733931168108333829645)
                  ·
                    refine ⟨9112400224188040625186117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 24299733931168108333829645 9112400224188040625186117)
                    ·
                      refine ⟨1708575042035257617222397, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9112400224188040625186117 1708575042035257617222397)
                      ·
                        rfl

theorem cell23_3327438_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 3, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 3, 2, 1, 3, 4].length) (baseStart_3327438 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3327438 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3327438 prefixEnd_3327438 := by exact prefixLift 3327438
  have htrace : WordTrace (prefixWord ++ tailWord_3327438) baseStart_3327438 baseEnd_3327438 := by
    simpa [prefixWord, tailWord_3327438, baseEnd_3327438] using wordTrace_append hprefix tailTrace_3327438
  have hstable : (prefixWord ++ tailWord_3327438).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3327438).length < 2 ^ (prefixWord ++ tailWord_3327438).sum := by decide
  have hdescent : baseEnd_3327438 < baseStart_3327438 := by decide
  rcases family_descends (prefixWord ++ tailWord_3327438) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3327495 : List Nat := [1, 1, 4, 3, 2, 2, 1, 3, 6]
def baseStart_3327495 : Nat := 118140960795 + 3327495 * 2 ^ 59
def prefixEnd_3327495 : Nat := 4983230072969 + 3 ^ 40 * 3327495 * 2
def baseEnd_3327495 : Nat := 189844923381395988245515

theorem tailTrace_3327495 : CollatzResearch.WordTrace tailWord_3327495 prefixEnd_3327495 189844923381395988245515 := by
  unfold tailWord_3327495
  simp only [CollatzResearch.WordTrace]
  refine ⟨121363713080061380747159939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80909142053374253831439959 121363713080061380747159939)
  ·
    refine ⟨182045569620092071120739909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121363713080061380747159939 182045569620092071120739909)
    ·
      refine ⟨34133544303767263335138733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 182045569620092071120739909 34133544303767263335138733)
      ·
        refine ⟨12800079113912723750677025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 34133544303767263335138733 12800079113912723750677025)
        ·
          refine ⟨9600059335434542813007769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12800079113912723750677025 9600059335434542813007769)
          ·
            refine ⟨7200044501575907109755827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9600059335434542813007769 7200044501575907109755827)
            ·
              refine ⟨10800066752363860664633741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7200044501575907109755827 10800066752363860664633741)
              ·
                refine ⟨4050025032136447749237653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10800066752363860664633741 4050025032136447749237653)
                ·
                  refine ⟨189844923381395988245515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4050025032136447749237653 189844923381395988245515)
                  ·
                    rfl

theorem cell23_3327495_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 2, 1, 3, 6].length) (baseStart_3327495 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3327495 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3327495 prefixEnd_3327495 := by exact prefixLift 3327495
  have htrace : WordTrace (prefixWord ++ tailWord_3327495) baseStart_3327495 baseEnd_3327495 := by
    simpa [prefixWord, tailWord_3327495, baseEnd_3327495] using wordTrace_append hprefix tailTrace_3327495
  have hstable : (prefixWord ++ tailWord_3327495).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3327495).length < 2 ^ (prefixWord ++ tailWord_3327495).sum := by decide
  have hdescent : baseEnd_3327495 < baseStart_3327495 := by decide
  rcases family_descends (prefixWord ++ tailWord_3327495) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3327505 : List Nat := [1, 2, 2, 1, 1, 2, 4, 1, 5, 1, 3]
def baseStart_3327505 : Nat := 118140960795 + 3327505 * 2 ^ 59
def prefixEnd_3327505 : Nat := 4983230072969 + 3 ^ 40 * 3327505 * 2
def baseEnd_3327505 : Nat := 1708609445239108855084589

theorem tailTrace_3327505 : CollatzResearch.WordTrace tailWord_3327505 prefixEnd_3327505 1708609445239108855084589 := by
  unfold tailWord_3327505
  simp only [CollatzResearch.WordTrace]
  refine ⟨121364077810025152455023969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80909385206683434970015979 121364077810025152455023969)
  ·
    refine ⟨91023058357518864341267977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 121364077810025152455023969 91023058357518864341267977)
    ·
      refine ⟨68267293768139148255950983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 91023058357518864341267977 68267293768139148255950983)
      ·
        refine ⟨102400940652208722383926475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68267293768139148255950983 102400940652208722383926475)
        ·
          refine ⟨153601410978313083575889713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 102400940652208722383926475 153601410978313083575889713)
          ·
            refine ⟨115201058233734812681917285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 153601410978313083575889713 115201058233734812681917285)
            ·
              refine ⟨21600198418825277377859491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 115201058233734812681917285 21600198418825277377859491)
              ·
                refine ⟨32400297628237916066789237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21600198418825277377859491 32400297628237916066789237)
                ·
                  refine ⟨3037527902647304631261491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 32400297628237916066789237 3037527902647304631261491)
                  ·
                    refine ⟨4556291853970956946892237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3037527902647304631261491 4556291853970956946892237)
                    ·
                      refine ⟨1708609445239108855084589, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4556291853970956946892237 1708609445239108855084589)
                      ·
                        rfl

theorem cell23_3327505_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 4, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 4, 1, 5, 1, 3].length) (baseStart_3327505 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3327505 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3327505 prefixEnd_3327505 := by exact prefixLift 3327505
  have htrace : WordTrace (prefixWord ++ tailWord_3327505) baseStart_3327505 baseEnd_3327505 := by
    simpa [prefixWord, tailWord_3327505, baseEnd_3327505] using wordTrace_append hprefix tailTrace_3327505
  have hstable : (prefixWord ++ tailWord_3327505).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3327505).length < 2 ^ (prefixWord ++ tailWord_3327505).sum := by decide
  have hdescent : baseEnd_3327505 < baseStart_3327505 := by decide
  rcases family_descends (prefixWord ++ tailWord_3327505) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3327538 : List Nat := [3, 2, 1, 1, 2, 1, 1, 1, 5, 6]
def baseStart_3327538 : Nat := 118140960795 + 3327538 * 2 ^ 59
def prefixEnd_3327538 : Nat := 4983230072969 + 3 ^ 40 * 3327538 * 2
def baseEnd_3327538 : Nat := 569542130033569075323979

theorem tailTrace_3327538 : CollatzResearch.WordTrace tailWord_3327538 prefixEnd_3327538 569542130033569075323979 := by
  unfold tailWord_3327538
  simp only [CollatzResearch.WordTrace]
  refine ⟨30341320354726399772743817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 80910187612603732727316845 30341320354726399772743817)
  ·
    refine ⟨22755990266044799829557863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30341320354726399772743817 22755990266044799829557863)
    ·
      refine ⟨34133985399067199744336795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22755990266044799829557863 34133985399067199744336795)
      ·
        refine ⟨51200978098600799616505193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34133985399067199744336795 51200978098600799616505193)
        ·
          refine ⟨38400733573950599712378895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51200978098600799616505193 38400733573950599712378895)
          ·
            refine ⟨57601100360925899568568343, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38400733573950599712378895 57601100360925899568568343)
            ·
              refine ⟨86401650541388849352852515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 57601100360925899568568343 86401650541388849352852515)
              ·
                refine ⟨129602475812083274029278773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 86401650541388849352852515 129602475812083274029278773)
                ·
                  refine ⟨12150232107382806940244885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 129602475812083274029278773 12150232107382806940244885)
                  ·
                    refine ⟨569542130033569075323979, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 12150232107382806940244885 569542130033569075323979)
                    ·
                      rfl

theorem cell23_3327538_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 1, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 1, 1, 5, 6].length) (baseStart_3327538 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3327538 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3327538 prefixEnd_3327538 := by exact prefixLift 3327538
  have htrace : WordTrace (prefixWord ++ tailWord_3327538) baseStart_3327538 baseEnd_3327538 := by
    simpa [prefixWord, tailWord_3327538, baseEnd_3327538] using wordTrace_append hprefix tailTrace_3327538
  have hstable : (prefixWord ++ tailWord_3327538).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3327538).length < 2 ^ (prefixWord ++ tailWord_3327538).sum := by decide
  have hdescent : baseEnd_3327538 < baseStart_3327538 := by decide
  rcases family_descends (prefixWord ++ tailWord_3327538) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3327539 : List Nat := [1, 1, 1, 2, 4, 4, 1, 4, 1, 1, 3]
def baseStart_3327539 : Nat := 118140960795 + 3327539 * 2 ^ 59
def prefixEnd_3327539 : Nat := 4983230072969 + 3 ^ 40 * 3327539 * 2
def baseEnd_3327539 : Nat := 1708626903581361722059433

theorem tailTrace_3327539 : CollatzResearch.WordTrace tailWord_3327539 prefixEnd_3327539 1708626903581361722059433 := by
  unfold tailWord_3327539
  simp only [CollatzResearch.WordTrace]
  refine ⟨121365317891901976261761671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80910211927934650841174447 121365317891901976261761671)
  ·
    refine ⟨182047976837852964392642507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121365317891901976261761671 182047976837852964392642507)
    ·
      refine ⟨273071965256779446588963761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 182047976837852964392642507 273071965256779446588963761)
      ·
        refine ⟨204803973942584584941722821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 273071965256779446588963761 204803973942584584941722821)
        ·
          refine ⟨38400745114234609676573029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 204803973942584584941722821 38400745114234609676573029)
          ·
            refine ⟨7200139708918989314357443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 38400745114234609676573029 7200139708918989314357443)
            ·
              refine ⟨10800209563378483971536165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7200139708918989314357443 10800209563378483971536165)
              ·
                refine ⟨2025039293133465744663031, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10800209563378483971536165 2025039293133465744663031)
                ·
                  refine ⟨3037558939700198616994547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2025039293133465744663031 3037558939700198616994547)
                  ·
                    refine ⟨4556338409550297925491821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3037558939700198616994547 4556338409550297925491821)
                    ·
                      refine ⟨1708626903581361722059433, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4556338409550297925491821 1708626903581361722059433)
                      ·
                        rfl

theorem cell23_3327539_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 4, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 4, 1, 4, 1, 1, 3].length) (baseStart_3327539 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3327539 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3327539 prefixEnd_3327539 := by exact prefixLift 3327539
  have htrace : WordTrace (prefixWord ++ tailWord_3327539) baseStart_3327539 baseEnd_3327539 := by
    simpa [prefixWord, tailWord_3327539, baseEnd_3327539] using wordTrace_append hprefix tailTrace_3327539
  have hstable : (prefixWord ++ tailWord_3327539).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3327539).length < 2 ^ (prefixWord ++ tailWord_3327539).sum := by decide
  have hdescent : baseEnd_3327539 < baseStart_3327539 := by decide
  rcases family_descends (prefixWord ++ tailWord_3327539) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3327545 : List Nat := [1, 2, 1, 5, 1, 2, 1, 2, 3, 1, 4]
def baseStart_3327545 : Nat := 118140960795 + 3327545 * 2 ^ 59
def prefixEnd_3327545 : Nat := 4983230072969 + 3 ^ 40 * 3327545 * 2
def baseEnd_3327545 : Nat := 1708629984465288698584405

theorem tailTrace_3327545 : CollatzResearch.WordTrace tailWord_3327545 prefixEnd_3327545 1708629984465288698584405 := by
  unfold tailWord_3327545
  simp only [CollatzResearch.WordTrace]
  refine ⟨121365536729880239286480089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80910357819920159524320059 121365536729880239286480089)
  ·
    refine ⟨91024152547410179464860067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 121365536729880239286480089 91024152547410179464860067)
    ·
      refine ⟨136536228821115269197290101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91024152547410179464860067 136536228821115269197290101)
      ·
        refine ⟨12800271451979556487245947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 136536228821115269197290101 12800271451979556487245947)
        ·
          refine ⟨19200407177969334730868921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12800271451979556487245947 19200407177969334730868921)
          ·
            refine ⟨14400305383477001048151691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19200407177969334730868921 14400305383477001048151691)
            ·
              refine ⟨21600458075215501572227537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14400305383477001048151691 21600458075215501572227537)
              ·
                refine ⟨16200343556411626179170653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21600458075215501572227537 16200343556411626179170653)
                ·
                  refine ⟨6075128833654359817188995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16200343556411626179170653 6075128833654359817188995)
                  ·
                    refine ⟨9112693250481539725783493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6075128833654359817188995 9112693250481539725783493)
                    ·
                      refine ⟨1708629984465288698584405, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9112693250481539725783493 1708629984465288698584405)
                      ·
                        rfl

theorem cell23_3327545_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 2, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 2, 1, 2, 3, 1, 4].length) (baseStart_3327545 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3327545 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3327545 prefixEnd_3327545 := by exact prefixLift 3327545
  have htrace : WordTrace (prefixWord ++ tailWord_3327545) baseStart_3327545 baseEnd_3327545 := by
    simpa [prefixWord, tailWord_3327545, baseEnd_3327545] using wordTrace_append hprefix tailTrace_3327545
  have hstable : (prefixWord ++ tailWord_3327545).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3327545).length < 2 ^ (prefixWord ++ tailWord_3327545).sum := by decide
  have hdescent : baseEnd_3327545 < baseStart_3327545 := by decide
  rcases family_descends (prefixWord ++ tailWord_3327545) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3327575 : List Nat := [1, 1, 3, 2, 2, 3, 2, 2, 1, 2, 4]
def baseStart_3327575 : Nat := 118140960795 + 3327575 * 2 ^ 59
def prefixEnd_3327575 : Nat := 4983230072969 + 3 ^ 40 * 3327575 * 2
def baseEnd_3327575 : Nat := 1708645388884923581209267

theorem tailTrace_3327575 : CollatzResearch.WordTrace tailWord_3327575 prefixEnd_3327575 1708645388884923581209267 := by
  unfold tailWord_3327575
  simp only [CollatzResearch.WordTrace]
  refine ⟨121366630919771554410072179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80911087279847702940048119 121366630919771554410072179)
  ·
    refine ⟨182049946379657331615108269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121366630919771554410072179 182049946379657331615108269)
    ·
      refine ⟨68268729892371499355665601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 182049946379657331615108269 68268729892371499355665601)
      ·
        refine ⟨51201547419278624516749201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 68268729892371499355665601 51201547419278624516749201)
        ·
          refine ⟨38401160564458968387561901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51201547419278624516749201 38401160564458968387561901)
          ·
            refine ⟨14400435211672113145335713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 38401160564458968387561901 14400435211672113145335713)
            ·
              refine ⟨10800326408754084859001785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14400435211672113145335713 10800326408754084859001785)
              ·
                refine ⟨8100244806565563644251339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10800326408754084859001785 8100244806565563644251339)
                ·
                  refine ⟨12150367209848345466377009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8100244806565563644251339 12150367209848345466377009)
                  ·
                    refine ⟨9112775407386259099782757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12150367209848345466377009 9112775407386259099782757)
                    ·
                      refine ⟨1708645388884923581209267, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9112775407386259099782757 1708645388884923581209267)
                      ·
                        rfl

theorem cell23_3327575_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 3, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 3, 2, 2, 1, 2, 4].length) (baseStart_3327575 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3327575 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3327575 prefixEnd_3327575 := by exact prefixLift 3327575
  have htrace : WordTrace (prefixWord ++ tailWord_3327575) baseStart_3327575 baseEnd_3327575 := by
    simpa [prefixWord, tailWord_3327575, baseEnd_3327575] using wordTrace_append hprefix tailTrace_3327575
  have hstable : (prefixWord ++ tailWord_3327575).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3327575).length < 2 ^ (prefixWord ++ tailWord_3327575).sum := by decide
  have hdescent : baseEnd_3327575 < baseStart_3327575 := by decide
  rcases family_descends (prefixWord ++ tailWord_3327575) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3327589 : List Nat := [1, 3, 1, 3, 3, 3, 1, 2, 2, 4]
def baseStart_3327589 : Nat := 118140960795 + 3327589 * 2 ^ 59
def prefixEnd_3327589 : Nat := 4983230072969 + 3 ^ 40 * 3327589 * 2
def baseEnd_3327589 : Nat := 569550859204695508811401

theorem tailTrace_3327589 : CollatzResearch.WordTrace tailWord_3327589 prefixEnd_3327589 569550859204695508811401 := by
  unfold tailWord_3327589
  simp only [CollatzResearch.WordTrace]
  refine ⟨121367141541720834801081821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80911427694480556534054547 121367141541720834801081821)
  ·
    refine ⟨45512678078145313050405683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 121367141541720834801081821 45512678078145313050405683)
    ·
      refine ⟨68269017117217969575608525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45512678078145313050405683 68269017117217969575608525)
      ·
        refine ⟨25600881418956738590853197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 68269017117217969575608525 25600881418956738590853197)
        ·
          refine ⟨9600330532108776971569949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25600881418956738590853197 9600330532108776971569949)
          ·
            refine ⟨3600123949540791364338731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9600330532108776971569949 3600123949540791364338731)
            ·
              refine ⟨5400185924311187046508097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3600123949540791364338731 5400185924311187046508097)
              ·
                refine ⟨4050139443233390284881073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5400185924311187046508097 4050139443233390284881073)
                ·
                  refine ⟨3037604582425042713660805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4050139443233390284881073 3037604582425042713660805)
                  ·
                    refine ⟨569550859204695508811401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3037604582425042713660805 569550859204695508811401)
                    ·
                      rfl

theorem cell23_3327589_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 3, 1, 2, 2, 4].length) (baseStart_3327589 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3327589 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3327589 prefixEnd_3327589 := by exact prefixLift 3327589
  have htrace : WordTrace (prefixWord ++ tailWord_3327589) baseStart_3327589 baseEnd_3327589 := by
    simpa [prefixWord, tailWord_3327589, baseEnd_3327589] using wordTrace_append hprefix tailTrace_3327589
  have hstable : (prefixWord ++ tailWord_3327589).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3327589).length < 2 ^ (prefixWord ++ tailWord_3327589).sum := by decide
  have hdescent : baseEnd_3327589 < baseStart_3327589 := by decide
  rcases family_descends (prefixWord ++ tailWord_3327589) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3327606 : List Nat := [5, 1, 1, 2, 2, 2, 3, 1, 2, 4]
def baseStart_3327606 : Nat := 118140960795 + 3327606 * 2 ^ 59
def prefixEnd_3327606 : Nat := 4983230072969 + 3 ^ 40 * 3327606 * 2
def baseEnd_3327606 : Nat := 569553768928404319973875

theorem tailTrace_3327606 : CollatzResearch.WordTrace tailWord_3327606 prefixEnd_3327606 569553768928404319973875 := by
  unfold tailWord_3327606
  simp only [CollatzResearch.WordTrace]
  refine ⟨7585485098916202919028167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 80911841055106164469633781 7585485098916202919028167)
  ·
    refine ⟨11378227648374304378542251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7585485098916202919028167 11378227648374304378542251)
    ·
      refine ⟨17067341472561456567813377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11378227648374304378542251 17067341472561456567813377)
      ·
        refine ⟨12800506104421092425860033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17067341472561456567813377 12800506104421092425860033)
        ·
          refine ⟨9600379578315819319395025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12800506104421092425860033 9600379578315819319395025)
          ·
            refine ⟨7200284683736864489546269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9600379578315819319395025 7200284683736864489546269)
            ·
              refine ⟨2700106756401324183579851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7200284683736864489546269 2700106756401324183579851)
              ·
                refine ⟨4050160134601986275369777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2700106756401324183579851 4050160134601986275369777)
                ·
                  refine ⟨3037620100951489706527333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4050160134601986275369777 3037620100951489706527333)
                  ·
                    refine ⟨569553768928404319973875, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3037620100951489706527333 569553768928404319973875)
                    ·
                      rfl

theorem cell23_3327606_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 2, 3, 1, 2, 4].length) (baseStart_3327606 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3327606 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3327606 prefixEnd_3327606 := by exact prefixLift 3327606
  have htrace : WordTrace (prefixWord ++ tailWord_3327606) baseStart_3327606 baseEnd_3327606 := by
    simpa [prefixWord, tailWord_3327606, baseEnd_3327606] using wordTrace_append hprefix tailTrace_3327606
  have hstable : (prefixWord ++ tailWord_3327606).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3327606).length < 2 ^ (prefixWord ++ tailWord_3327606).sum := by decide
  have hdescent : baseEnd_3327606 < baseStart_3327606 := by decide
  rcases family_descends (prefixWord ++ tailWord_3327606) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3327608 : List Nat := [2, 1, 2, 1, 1, 1, 2, 1, 3, 4, 5]
def baseStart_3327608 : Nat := 118140960795 + 3327608 * 2 ^ 59
def prefixEnd_3327608 : Nat := 4983230072969 + 3 ^ 40 * 3327608 * 2
def baseEnd_3327608 : Nat := 1708662333746521952096615

theorem tailTrace_3327608 : CollatzResearch.WordTrace tailWord_3327608 prefixEnd_3327608 1708662333746521952096615 := by
  unfold tailWord_3327608
  simp only [CollatzResearch.WordTrace]
  refine ⟨60683917264326000523011739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80911889685768000697348985 60683917264326000523011739)
  ·
    refine ⟨91025875896489000784517609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60683917264326000523011739 91025875896489000784517609)
    ·
      refine ⟨68269406922366750588388207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 91025875896489000784517609 68269406922366750588388207)
      ·
        refine ⟨102404110383550125882582311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68269406922366750588388207 102404110383550125882582311)
        ·
          refine ⟨153606165575325188823873467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 102404110383550125882582311 153606165575325188823873467)
          ·
            refine ⟨230409248362987783235810201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 153606165575325188823873467 230409248362987783235810201)
            ·
              refine ⟨172806936272240837426857651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 230409248362987783235810201 172806936272240837426857651)
              ·
                refine ⟨259210404408361256140286477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 172806936272240837426857651 259210404408361256140286477)
                ·
                  refine ⟨97203901653135471052607429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 259210404408361256140286477 97203901653135471052607429)
                  ·
                    refine ⟨18225731559962900822363893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 97203901653135471052607429 18225731559962900822363893)
                    ·
                      refine ⟨1708662333746521952096615, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 18225731559962900822363893 1708662333746521952096615)
                      ·
                        rfl

theorem cell23_3327608_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 2, 1, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 2, 1, 3, 4, 5].length) (baseStart_3327608 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3327608 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3327608 prefixEnd_3327608 := by exact prefixLift 3327608
  have htrace : WordTrace (prefixWord ++ tailWord_3327608) baseStart_3327608 baseEnd_3327608 := by
    simpa [prefixWord, tailWord_3327608, baseEnd_3327608] using wordTrace_append hprefix tailTrace_3327608
  have hstable : (prefixWord ++ tailWord_3327608).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3327608).length < 2 ^ (prefixWord ++ tailWord_3327608).sum := by decide
  have hdescent : baseEnd_3327608 < baseStart_3327608 := by decide
  rcases family_descends (prefixWord ++ tailWord_3327608) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3327639 : List Nat := [1, 1, 3, 3, 2, 2, 2, 3, 1, 3, 2]
def baseStart_3327639 : Nat := 118140960795 + 3327639 * 2 ^ 59
def prefixEnd_3327639 : Nat := 4983230072969 + 3 ^ 40 * 3327639 * 2
def baseEnd_3327639 : Nat := 1708678251646811330808973

theorem tailTrace_3327639 : CollatzResearch.WordTrace tailWord_3327639 prefixEnd_3327639 1708678251646811330808973 := by
  unfold tailWord_3327639
  simp only [CollatzResearch.WordTrace]
  refine ⟨121368965191539693340401971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80912643461026462226934647 121368965191539693340401971)
  ·
    refine ⟨182053447787309540010602957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121368965191539693340401971 182053447787309540010602957)
    ·
      refine ⟨68270042920241077503976109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 182053447787309540010602957 68270042920241077503976109)
      ·
        refine ⟨25601266095090404063991041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 68270042920241077503976109 25601266095090404063991041)
        ·
          refine ⟨19200949571317803047993281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25601266095090404063991041 19200949571317803047993281)
          ·
            refine ⟨14400712178488352285994961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19200949571317803047993281 14400712178488352285994961)
            ·
              refine ⟨10800534133866264214496221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14400712178488352285994961 10800534133866264214496221)
              ·
                refine ⟨4050200300199849080436083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10800534133866264214496221 4050200300199849080436083)
                ·
                  refine ⟨6075300450299773620654125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4050200300199849080436083 6075300450299773620654125)
                  ·
                    refine ⟨2278237668862415107745297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6075300450299773620654125 2278237668862415107745297)
                    ·
                      refine ⟨1708678251646811330808973, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2278237668862415107745297 1708678251646811330808973)
                      ·
                        rfl

theorem cell23_3327639_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 2, 2, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 2, 2, 3, 1, 3, 2].length) (baseStart_3327639 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3327639 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3327639 prefixEnd_3327639 := by exact prefixLift 3327639
  have htrace : WordTrace (prefixWord ++ tailWord_3327639) baseStart_3327639 baseEnd_3327639 := by
    simpa [prefixWord, tailWord_3327639, baseEnd_3327639] using wordTrace_append hprefix tailTrace_3327639
  have hstable : (prefixWord ++ tailWord_3327639).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3327639).length < 2 ^ (prefixWord ++ tailWord_3327639).sum := by decide
  have hdescent : baseEnd_3327639 < baseStart_3327639 := by decide
  rcases family_descends (prefixWord ++ tailWord_3327639) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3327685 : List Nat := [1, 3, 1, 1, 1, 1, 2, 4, 1, 5, 3]
def baseStart_3327685 : Nat := 118140960795 + 3327685 * 2 ^ 59
def prefixEnd_3327685 : Nat := 4983230072969 + 3 ^ 40 * 3327685 * 2
def baseEnd_3327685 : Nat := 1708701871756918150833761

theorem tailTrace_3327685 : CollatzResearch.WordTrace tailWord_3327685 prefixEnd_3327685 1708701871756918150833761 := by
  unfold tailWord_3327685
  simp only [CollatzResearch.WordTrace]
  refine ⟨121370642949373043196576509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80913761966248695464384339 121370642949373043196576509)
  ·
    refine ⟨45513991106014891198716191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 121370642949373043196576509 45513991106014891198716191)
    ·
      refine ⟨68270986659022336798074287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45513991106014891198716191 68270986659022336798074287)
      ·
        refine ⟨102406479988533505197111431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68270986659022336798074287 102406479988533505197111431)
        ·
          refine ⟨153609719982800257795667147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 102406479988533505197111431 153609719982800257795667147)
          ·
            refine ⟨230414579974200386693500721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 153609719982800257795667147 230414579974200386693500721)
            ·
              refine ⟨172810934980650290020125541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 230414579974200386693500721 172810934980650290020125541)
              ·
                refine ⟨32402050308871929378773539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 172810934980650290020125541 32402050308871929378773539)
                ·
                  refine ⟨48603075463307894068160309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32402050308871929378773539 48603075463307894068160309)
                  ·
                    refine ⟨4556538324685115068890029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 48603075463307894068160309 4556538324685115068890029)
                    ·
                      refine ⟨1708701871756918150833761, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4556538324685115068890029 1708701871756918150833761)
                      ·
                        rfl

theorem cell23_3327685_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 2, 4, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 2, 4, 1, 5, 3].length) (baseStart_3327685 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3327685 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3327685 prefixEnd_3327685 := by exact prefixLift 3327685
  have htrace : WordTrace (prefixWord ++ tailWord_3327685) baseStart_3327685 baseEnd_3327685 := by
    simpa [prefixWord, tailWord_3327685, baseEnd_3327685] using wordTrace_append hprefix tailTrace_3327685
  have hstable : (prefixWord ++ tailWord_3327685).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3327685).length < 2 ^ (prefixWord ++ tailWord_3327685).sum := by decide
  have hdescent : baseEnd_3327685 < baseStart_3327685 := by decide
  rcases family_descends (prefixWord ++ tailWord_3327685) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3327712 : List Nat := [2, 1, 1, 3, 1, 2, 3, 1, 2, 5, 2]
def baseStart_3327712 : Nat := 118140960795 + 3327712 * 2 ^ 59
def prefixEnd_3327712 : Nat := 4983230072969 + 3 ^ 40 * 3327712 * 2
def baseEnd_3327712 : Nat := 1708715735734589545196137

theorem tailTrace_3327712 : CollatzResearch.WordTrace tailWord_3327712 prefixEnd_3327712 1708715735734589545196137 := by
  unfold tailWord_3327712
  simp only [CollatzResearch.WordTrace]
  refine ⟨60685813860137613403904695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80914418480183484538539593 60685813860137613403904695)
  ·
    refine ⟨91028720790206420105857043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60685813860137613403904695 91028720790206420105857043)
    ·
      refine ⟨136543081185309630158785565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91028720790206420105857043 136543081185309630158785565)
      ·
        refine ⟨51203655444491111309544587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 136543081185309630158785565 51203655444491111309544587)
        ·
          refine ⟨76805483166736666964316881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51203655444491111309544587 76805483166736666964316881)
          ·
            refine ⟨57604112375052500223237661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 76805483166736666964316881 57604112375052500223237661)
            ·
              refine ⟨21601542140644687583714123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 57604112375052500223237661 21601542140644687583714123)
              ·
                refine ⟨32402313210967031375571185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21601542140644687583714123 32402313210967031375571185)
                ·
                  refine ⟨24301734908225273531678389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32402313210967031375571185 24301734908225273531678389)
                  ·
                    refine ⟨2278287647646119393594849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 24301734908225273531678389 2278287647646119393594849)
                    ·
                      refine ⟨1708715735734589545196137, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2278287647646119393594849 1708715735734589545196137)
                      ·
                        rfl

theorem cell23_3327712_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 3, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 3, 1, 2, 5, 2].length) (baseStart_3327712 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3327712 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3327712 prefixEnd_3327712 := by exact prefixLift 3327712
  have htrace : WordTrace (prefixWord ++ tailWord_3327712) baseStart_3327712 baseEnd_3327712 := by
    simpa [prefixWord, tailWord_3327712, baseEnd_3327712] using wordTrace_append hprefix tailTrace_3327712
  have hstable : (prefixWord ++ tailWord_3327712).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3327712).length < 2 ^ (prefixWord ++ tailWord_3327712).sum := by decide
  have hdescent : baseEnd_3327712 < baseStart_3327712 := by decide
  rcases family_descends (prefixWord ++ tailWord_3327712) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3327752 : List Nat := [2, 1, 3, 2, 2, 1, 1, 2, 5, 4]
def baseStart_3327752 : Nat := 118140960795 + 3327752 * 2 ^ 59
def prefixEnd_3327752 : Nat := 4983230072969 + 3 ^ 40 * 3327752 * 2
def baseEnd_3327752 : Nat := 569578758320256462898651

theorem tailTrace_3327752 : CollatzResearch.WordTrace tailWord_3327752 prefixEnd_3327752 569578758320256462898651 := by
  unfold tailWord_3327752
  simp only [CollatzResearch.WordTrace]
  refine ⟨60686543320065156819632755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80915391093420209092843673 60686543320065156819632755)
  ·
    refine ⟨91029814980097735229449133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60686543320065156819632755 91029814980097735229449133)
    ·
      refine ⟨34136180617536650711043425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 91029814980097735229449133 34136180617536650711043425)
      ·
        refine ⟨25602135463152488033282569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34136180617536650711043425 25602135463152488033282569)
        ·
          refine ⟨19201601597364366024961927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25602135463152488033282569 19201601597364366024961927)
          ·
            refine ⟨28802402396046549037442891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19201601597364366024961927 28802402396046549037442891)
            ·
              refine ⟨43203603594069823556164337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28802402396046549037442891 43203603594069823556164337)
              ·
                refine ⟨32402702695552367667123253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 43203603594069823556164337 32402702695552367667123253)
                ·
                  refine ⟨3037753377708034468792805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 32402702695552367667123253 3037753377708034468792805)
                  ·
                    refine ⟨569578758320256462898651, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3037753377708034468792805 569578758320256462898651)
                    ·
                      rfl

theorem cell23_3327752_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 1, 2, 5, 4].length) (baseStart_3327752 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3327752 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3327752 prefixEnd_3327752 := by exact prefixLift 3327752
  have htrace : WordTrace (prefixWord ++ tailWord_3327752) baseStart_3327752 baseEnd_3327752 := by
    simpa [prefixWord, tailWord_3327752, baseEnd_3327752] using wordTrace_append hprefix tailTrace_3327752
  have hstable : (prefixWord ++ tailWord_3327752).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3327752).length < 2 ^ (prefixWord ++ tailWord_3327752).sum := by decide
  have hdescent : baseEnd_3327752 < baseStart_3327752 := by decide
  rcases family_descends (prefixWord ++ tailWord_3327752) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3327755 : List Nat := [1, 1, 1, 1, 5, 1, 3, 1, 2, 1, 6]
def baseStart_3327755 : Nat := 118140960795 + 3327755 * 2 ^ 59
def prefixEnd_3327755 : Nat := 4983230072969 + 3 ^ 40 * 3327755 * 2
def baseEnd_3327755 : Nat := 1708737815402732876958439

theorem tailTrace_3327755 : CollatzResearch.WordTrace tailWord_3327755 prefixEnd_3327755 1708737815402732876958439 := by
  unfold tailWord_3327755
  simp only [CollatzResearch.WordTrace]
  refine ⟨121373196059119445151624719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80915464039412963434416479 121373196059119445151624719)
  ·
    refine ⟨182059794088679167727437079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121373196059119445151624719 182059794088679167727437079)
    ·
      refine ⟨273089691133018751591155619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 182059794088679167727437079 273089691133018751591155619)
      ·
        refine ⟨409634536699528127386733429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 273089691133018751591155619 409634536699528127386733429)
        ·
          refine ⟨38403237815580761942506259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 409634536699528127386733429 38403237815580761942506259)
          ·
            refine ⟨57604856723371142913759389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38403237815580761942506259 57604856723371142913759389)
            ·
              refine ⟨21601821271264178592659771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 57604856723371142913759389 21601821271264178592659771)
              ·
                refine ⟨32402731906896267888989657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21601821271264178592659771 32402731906896267888989657)
                ·
                  refine ⟨24302048930172200916742243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32402731906896267888989657 24302048930172200916742243)
                  ·
                    refine ⟨36453073395258301375113365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 24302048930172200916742243 36453073395258301375113365)
                    ·
                      refine ⟨1708737815402732876958439, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 36453073395258301375113365 1708737815402732876958439)
                      ·
                        rfl

theorem cell23_3327755_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 3, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 3, 1, 2, 1, 6].length) (baseStart_3327755 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3327755 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3327755 prefixEnd_3327755 := by exact prefixLift 3327755
  have htrace : WordTrace (prefixWord ++ tailWord_3327755) baseStart_3327755 baseEnd_3327755 := by
    simpa [prefixWord, tailWord_3327755, baseEnd_3327755] using wordTrace_append hprefix tailTrace_3327755
  have hstable : (prefixWord ++ tailWord_3327755).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3327755).length < 2 ^ (prefixWord ++ tailWord_3327755).sum := by decide
  have hdescent : baseEnd_3327755 < baseStart_3327755 := by decide
  rcases family_descends (prefixWord ++ tailWord_3327755) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3327826 : List Nat := [3, 2, 2, 1, 1, 3, 3, 1, 3, 1, 3]
def baseStart_3327826 : Nat := 118140960795 + 3327826 * 2 ^ 59
def prefixEnd_3327826 : Nat := 4983230072969 + 3 ^ 40 * 3327826 * 2
def baseEnd_3327826 : Nat := 1708774272529202099170613

theorem tailTrace_3327826 : CollatzResearch.WordTrace tailWord_3327826 prefixEnd_3327826 1708774272529202099170613 := by
  unfold tailWord_3327826
  simp only [CollatzResearch.WordTrace]
  refine ⟨30343946410465556069364833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 80917190427908149518306221 30343946410465556069364833)
  ·
    refine ⟨22757959807849167052023625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30343946410465556069364833 22757959807849167052023625)
    ·
      refine ⟨17068469855886875289017719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22757959807849167052023625 17068469855886875289017719)
      ·
        refine ⟨25602704783830312933526579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17068469855886875289017719 25602704783830312933526579)
        ·
          refine ⟨38404057175745469400289869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25602704783830312933526579 38404057175745469400289869)
          ·
            refine ⟨14401521440904551025108701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 38404057175745469400289869 14401521440904551025108701)
            ·
              refine ⟨5400570540339206634415763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14401521440904551025108701 5400570540339206634415763)
              ·
                refine ⟨8100855810508809951623645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5400570540339206634415763 8100855810508809951623645)
                ·
                  refine ⟨3037820928940803731858867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8100855810508809951623645 3037820928940803731858867)
                  ·
                    refine ⟨4556731393411205597788301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3037820928940803731858867 4556731393411205597788301)
                    ·
                      refine ⟨1708774272529202099170613, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4556731393411205597788301 1708774272529202099170613)
                      ·
                        rfl

theorem cell23_3327826_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 3, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 3, 3, 1, 3, 1, 3].length) (baseStart_3327826 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3327826 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3327826 prefixEnd_3327826 := by exact prefixLift 3327826
  have htrace : WordTrace (prefixWord ++ tailWord_3327826) baseStart_3327826 baseEnd_3327826 := by
    simpa [prefixWord, tailWord_3327826, baseEnd_3327826] using wordTrace_append hprefix tailTrace_3327826
  have hstable : (prefixWord ++ tailWord_3327826).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3327826).length < 2 ^ (prefixWord ++ tailWord_3327826).sum := by decide
  have hdescent : baseEnd_3327826 < baseStart_3327826 := by decide
  rcases family_descends (prefixWord ++ tailWord_3327826) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3327906 : List Nat := [3, 3, 1, 2, 3, 1, 3, 7]
def baseStart_3327906 : Nat := 118140960795 + 3327906 * 2 ^ 59
def prefixEnd_3327906 : Nat := 4983230072969 + 3 ^ 40 * 3327906 * 2
def baseEnd_3327906 : Nat := 63289457443761547635935

theorem tailTrace_3327906 : CollatzResearch.WordTrace tailWord_3327906 prefixEnd_3327906 63289457443761547635935 := by
  unfold tailWord_3327906
  simp only [CollatzResearch.WordTrace]
  refine ⟨30344675870393099485092893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 80919135654381598626914381 30344675870393099485092893)
  ·
    refine ⟨11379253451397412306909835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 30344675870393099485092893 11379253451397412306909835)
    ·
      refine ⟨17068880177096118460364753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11379253451397412306909835 17068880177096118460364753)
      ·
        refine ⟨12801660132822088845273565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17068880177096118460364753 12801660132822088845273565)
        ·
          refine ⟨4800622549808283316977587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12801660132822088845273565 4800622549808283316977587)
          ·
            refine ⟨7200933824712424975466381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4800622549808283316977587 7200933824712424975466381)
            ·
              refine ⟨2700350184267159365799893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7200933824712424975466381 2700350184267159365799893)
              ·
                refine ⟨63289457443761547635935, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2700350184267159365799893 63289457443761547635935)
                ·
                  rfl

theorem cell23_3327906_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 3, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 3, 1, 3, 7].length) (baseStart_3327906 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3327906 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3327906 prefixEnd_3327906 := by exact prefixLift 3327906
  have htrace : WordTrace (prefixWord ++ tailWord_3327906) baseStart_3327906 baseEnd_3327906 := by
    simpa [prefixWord, tailWord_3327906, baseEnd_3327906] using wordTrace_append hprefix tailTrace_3327906
  have hstable : (prefixWord ++ tailWord_3327906).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3327906).length < 2 ^ (prefixWord ++ tailWord_3327906).sum := by decide
  have hdescent : baseEnd_3327906 < baseStart_3327906 := by decide
  rcases family_descends (prefixWord ++ tailWord_3327906) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3327933 : List Nat := [1, 4, 1, 2, 3, 1, 3, 2, 2, 1, 3]
def baseStart_3327933 : Nat := 118140960795 + 3327933 * 2 ^ 59
def prefixEnd_3327933 : Nat := 4983230072969 + 3 ^ 40 * 3327933 * 2
def baseEnd_3327933 : Nat := 1708829214959233180532621

theorem tailTrace_3327933 : CollatzResearch.WordTrace tailWord_3327933 prefixEnd_3327933 1708829214959233180532621 := by
  unfold tailWord_3327933
  simp only [CollatzResearch.WordTrace]
  refine ⟨121379688252474581551604453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80919792168316387701069635 121379688252474581551604453)
  ·
    refine ⟨22758691547338984040925835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 121379688252474581551604453 22758691547338984040925835)
    ·
      refine ⟨34138037321008476061388753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22758691547338984040925835 34138037321008476061388753)
      ·
        refine ⟨25603527990756357046041565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34138037321008476061388753 25603527990756357046041565)
        ·
          refine ⟨9601322996533633892265587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25603527990756357046041565 9601322996533633892265587)
          ·
            refine ⟨14401984494800450838398381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9601322996533633892265587 14401984494800450838398381)
            ·
              refine ⟨5400744185550169064399393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14401984494800450838398381 5400744185550169064399393)
              ·
                refine ⟨4050558139162626798299545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5400744185550169064399393 4050558139162626798299545)
                ·
                  refine ⟨3037918604371970098724659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4050558139162626798299545 3037918604371970098724659)
                  ·
                    refine ⟨4556877906557955148086989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3037918604371970098724659 4556877906557955148086989)
                    ·
                      refine ⟨1708829214959233180532621, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4556877906557955148086989 1708829214959233180532621)
                      ·
                        rfl

theorem cell23_3327933_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 1, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 1, 3, 2, 2, 1, 3].length) (baseStart_3327933 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3327933 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3327933 prefixEnd_3327933 := by exact prefixLift 3327933
  have htrace : WordTrace (prefixWord ++ tailWord_3327933) baseStart_3327933 baseEnd_3327933 := by
    simpa [prefixWord, tailWord_3327933, baseEnd_3327933] using wordTrace_append hprefix tailTrace_3327933
  have hstable : (prefixWord ++ tailWord_3327933).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3327933).length < 2 ^ (prefixWord ++ tailWord_3327933).sum := by decide
  have hdescent : baseEnd_3327933 < baseStart_3327933 := by decide
  rcases family_descends (prefixWord ++ tailWord_3327933) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3328007 : List Nat := [1, 1, 4, 3, 1, 4, 2, 1, 2, 2, 2]
def baseStart_3328007 : Nat := 118140960795 + 3328007 * 2 ^ 59
def prefixEnd_3328007 : Nat := 4983230072969 + 3 ^ 40 * 3328007 * 2
def baseEnd_3328007 : Nat := 1708867212527665891007281

theorem tailTrace_3328007 : CollatzResearch.WordTrace tailWord_3328007 prefixEnd_3328007 1708867212527665891007281 := by
  unfold tailWord_3328007
  simp only [CollatzResearch.WordTrace]
  refine ⟨121382387254206492189798275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80921591502804328126532183 121382387254206492189798275)
  ·
    refine ⟨182073580881309738284697413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121382387254206492189798275 182073580881309738284697413)
    ·
      refine ⟨34138796415245575928380765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 182073580881309738284697413 34138796415245575928380765)
      ·
        refine ⟨12802048655717090973142787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 34138796415245575928380765 12802048655717090973142787)
        ·
          refine ⟨19203072983575636459714181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12802048655717090973142787 19203072983575636459714181)
          ·
            refine ⟨3600576184420431836196409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 19203072983575636459714181 3600576184420431836196409)
            ·
              refine ⟨2700432138315323877147307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3600576184420431836196409 2700432138315323877147307)
              ·
                refine ⟨4050648207472985815720961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2700432138315323877147307 4050648207472985815720961)
                ·
                  refine ⟨3037986155604739361790721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4050648207472985815720961 3037986155604739361790721)
                  ·
                    refine ⟨2278489616703554521343041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3037986155604739361790721 2278489616703554521343041)
                    ·
                      refine ⟨1708867212527665891007281, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2278489616703554521343041 1708867212527665891007281)
                      ·
                        rfl

theorem cell23_3328007_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 4, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 4, 2, 1, 2, 2, 2].length) (baseStart_3328007 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3328007 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3328007 prefixEnd_3328007 := by exact prefixLift 3328007
  have htrace : WordTrace (prefixWord ++ tailWord_3328007) baseStart_3328007 baseEnd_3328007 := by
    simpa [prefixWord, tailWord_3328007, baseEnd_3328007] using wordTrace_append hprefix tailTrace_3328007
  have hstable : (prefixWord ++ tailWord_3328007).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3328007).length < 2 ^ (prefixWord ++ tailWord_3328007).sum := by decide
  have hdescent : baseEnd_3328007 < baseStart_3328007 := by decide
  rcases family_descends (prefixWord ++ tailWord_3328007) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3328026 : List Nat := [3, 1, 1, 3, 1, 4, 2, 1, 2, 5]
def baseStart_3328026 : Nat := 118140960795 + 3328026 * 2 ^ 59
def prefixEnd_3328026 : Nat := 4983230072969 + 3 ^ 40 * 3328026 * 2
def baseEnd_3328026 : Nat := 569625656220033772223231

theorem tailTrace_3328026 : CollatzResearch.WordTrace tailWord_3328026 prefixEnd_3328026 569625656220033772223231 := by
  unfold tailWord_3328026
  simp only [CollatzResearch.WordTrace]
  refine ⟨30345770060284414608684983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 80922053494091772289826621 30345770060284414608684983)
  ·
    refine ⟨45518655090426621913027475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30345770060284414608684983 45518655090426621913027475)
    ·
      refine ⟨68277982635639932869541213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45518655090426621913027475 68277982635639932869541213)
      ·
        refine ⟨25604243488364974826077955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 68277982635639932869541213 25604243488364974826077955)
        ·
          refine ⟨38406365232547462239116933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25604243488364974826077955 38406365232547462239116933)
          ·
            refine ⟨7201193481102649169834425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 38406365232547462239116933 7201193481102649169834425)
            ·
              refine ⟨5400895110826986877375819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7201193481102649169834425 5400895110826986877375819)
              ·
                refine ⟨8101342666240480316063729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5400895110826986877375819 8101342666240480316063729)
                ·
                  refine ⟨6076006999680360237047797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8101342666240480316063729 6076006999680360237047797)
                  ·
                    refine ⟨569625656220033772223231, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6076006999680360237047797 569625656220033772223231)
                    ·
                      rfl

theorem cell23_3328026_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 4, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 4, 2, 1, 2, 5].length) (baseStart_3328026 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3328026 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3328026 prefixEnd_3328026 := by exact prefixLift 3328026
  have htrace : WordTrace (prefixWord ++ tailWord_3328026) baseStart_3328026 baseEnd_3328026 := by
    simpa [prefixWord, tailWord_3328026, baseEnd_3328026] using wordTrace_append hprefix tailTrace_3328026
  have hstable : (prefixWord ++ tailWord_3328026).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3328026).length < 2 ^ (prefixWord ++ tailWord_3328026).sum := by decide
  have hdescent : baseEnd_3328026 < baseStart_3328026 := by decide
  rcases family_descends (prefixWord ++ tailWord_3328026) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3328079 : List Nat := [1, 1, 2, 1, 1, 2, 2, 3, 2, 5, 3]
def baseStart_3328079 : Nat := 118140960795 + 3328079 * 2 ^ 59
def prefixEnd_3328079 : Nat := 4983230072969 + 3 ^ 40 * 3328079 * 2
def baseEnd_3328079 : Nat := 1708904183134789609306949

theorem tailTrace_3328079 : CollatzResearch.WordTrace tailWord_3328079 prefixEnd_3328079 1708904183134789609306949 := by
  unfold tailWord_3328079
  simp only [CollatzResearch.WordTrace]
  refine ⟨121385013309945648486419291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80923342206630432324279527 121385013309945648486419291)
  ·
    refine ⟨182077519964918472729628937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121385013309945648486419291 182077519964918472729628937)
    ·
      refine ⟨136558139973688854547221703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 182077519964918472729628937 136558139973688854547221703)
      ·
        refine ⟨204837209960533281820832555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 136558139973688854547221703 204837209960533281820832555)
        ·
          refine ⟨307255814940799922731248833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 204837209960533281820832555 307255814940799922731248833)
          ·
            refine ⟨230441861205599942048436625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 307255814940799922731248833 230441861205599942048436625)
            ·
              refine ⟨172831395904199956536327469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 230441861205599942048436625 172831395904199956536327469)
              ·
                refine ⟨64811773464074983701122801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 172831395904199956536327469 64811773464074983701122801)
                ·
                  refine ⟨48608830098056237775842101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 64811773464074983701122801 48608830098056237775842101)
                  ·
                    refine ⟨4557077821692772291485197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 48608830098056237775842101 4557077821692772291485197)
                    ·
                      refine ⟨1708904183134789609306949, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4557077821692772291485197 1708904183134789609306949)
                      ·
                        rfl

theorem cell23_3328079_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 2, 3, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 2, 3, 2, 5, 3].length) (baseStart_3328079 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3328079 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3328079 prefixEnd_3328079 := by exact prefixLift 3328079
  have htrace : WordTrace (prefixWord ++ tailWord_3328079) baseStart_3328079 baseEnd_3328079 := by
    simpa [prefixWord, tailWord_3328079, baseEnd_3328079] using wordTrace_append hprefix tailTrace_3328079
  have hstable : (prefixWord ++ tailWord_3328079).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3328079).length < 2 ^ (prefixWord ++ tailWord_3328079).sum := by decide
  have hdescent : baseEnd_3328079 < baseStart_3328079 := by decide
  rcases family_descends (prefixWord ++ tailWord_3328079) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3328113 : List Nat := [1, 2, 2, 2, 1, 1, 6, 1, 3, 1, 3]
def baseStart_3328113 : Nat := 118140960795 + 3328113 * 2 ^ 59
def prefixEnd_3328113 : Nat := 4983230072969 + 3 ^ 40 * 3328113 * 2
def baseEnd_3328113 : Nat := 1708921641477042476281793

theorem tailTrace_3328113 : CollatzResearch.WordTrace tailWord_3328113 prefixEnd_3328113 1708921641477042476281793 := by
  unfold tailWord_3328113
  simp only [CollatzResearch.WordTrace]
  refine ⟨121386253391822472293156993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80924168927881648195437995 121386253391822472293156993)
  ·
    refine ⟨91039690043866854219867745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 121386253391822472293156993 91039690043866854219867745)
    ·
      refine ⟨68279767532900140664900809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 91039690043866854219867745 68279767532900140664900809)
      ·
        refine ⟨51209825649675105498675607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 68279767532900140664900809 51209825649675105498675607)
        ·
          refine ⟨76814738474512658248013411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51209825649675105498675607 76814738474512658248013411)
          ·
            refine ⟨115222107711768987372020117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 76814738474512658248013411 115222107711768987372020117)
            ·
              refine ⟨5401036298989171283063443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 115222107711768987372020117 5401036298989171283063443)
              ·
                refine ⟨8101554448483756924595165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5401036298989171283063443 8101554448483756924595165)
                ·
                  refine ⟨3038082918181408846723187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8101554448483756924595165 3038082918181408846723187)
                  ·
                    refine ⟨4557124377272113270084781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3038082918181408846723187 4557124377272113270084781)
                    ·
                      refine ⟨1708921641477042476281793, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4557124377272113270084781 1708921641477042476281793)
                      ·
                        rfl

theorem cell23_3328113_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 6, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 6, 1, 3, 1, 3].length) (baseStart_3328113 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3328113 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3328113 prefixEnd_3328113 := by exact prefixLift 3328113
  have htrace : WordTrace (prefixWord ++ tailWord_3328113) baseStart_3328113 baseEnd_3328113 := by
    simpa [prefixWord, tailWord_3328113, baseEnd_3328113] using wordTrace_append hprefix tailTrace_3328113
  have hstable : (prefixWord ++ tailWord_3328113).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3328113).length < 2 ^ (prefixWord ++ tailWord_3328113).sum := by decide
  have hdescent : baseEnd_3328113 < baseStart_3328113 := by decide
  rcases family_descends (prefixWord ++ tailWord_3328113) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
