import V185TrunkScan21Chunk150

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental

namespace V185TrunkScan21Incremental

def tailWord_1841245 : List Nat := [1, 4, 4, 1, 1, 10]
def baseStart_1841245 : Nat := 118140960795 + 1841245 * 2 ^ 59
def prefixEnd_1841245 : Nat := 4983230072969 + 3 ^ 40 * 1841245 * 2
def baseEnd_1841245 : Nat := 15562859056588540809379

theorem tailTrace_1841245 : CollatzResearch.WordTrace tailWord_1841245 prefixEnd_1841245 15562859056588540809379 := by
  unfold tailWord_1841245
  simp only [CollatzResearch.WordTrace]
  refine ⟨67155722214491299455701189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44770481476327532970467459 67155722214491299455701189)
  ·
    refine ⟨12591697915217118647943973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 67155722214491299455701189 12591697915217118647943973)
    ·
      refine ⟨2360943359103209746489495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 12591697915217118647943973 2360943359103209746489495)
      ·
        refine ⟨3541415038654814619734243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2360943359103209746489495 3541415038654814619734243)
        ·
          refine ⟨5312122557982221929601365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3541415038654814619734243 5312122557982221929601365)
          ·
            refine ⟨15562859056588540809379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 5312122557982221929601365 15562859056588540809379)
            ·
              rfl

theorem cell21_1841245_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 10].length) (baseStart_1841245 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1841245 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1841245 prefixEnd_1841245 := by exact prefixLift 1841245
  have htrace : WordTrace (prefixWord ++ tailWord_1841245) baseStart_1841245 baseEnd_1841245 := by
    simpa [prefixWord, tailWord_1841245, baseEnd_1841245] using wordTrace_append hprefix tailTrace_1841245
  have hstable : (prefixWord ++ tailWord_1841245).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1841245).length < 2 ^ (prefixWord ++ tailWord_1841245).sum := by decide
  have hdescent : baseEnd_1841245 < baseStart_1841245 := by decide
  rcases family_descends (prefixWord ++ tailWord_1841245) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1841335 : List Nat := [1, 1, 3, 1, 4, 2, 2, 2, 5]
def baseStart_1841335 : Nat := 118140960795 + 1841335 * 2 ^ 59
def prefixEnd_1841335 : Nat := 4983230072969 + 3 ^ 40 * 1841335 * 2
def baseEnd_1841335 : Nat := 420217733754070445353049

theorem tailTrace_1841335 : CollatzResearch.WordTrace tailWord_1841335 prefixEnd_1841335 420217733754070445353049 := by
  unfold tailWord_1841335
  simp only [CollatzResearch.WordTrace]
  refine ⟨67159004784165244826477459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44772669856110163217651639 67159004784165244826477459)
  ·
    refine ⟨100738507176247867239716189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67159004784165244826477459 100738507176247867239716189)
    ·
      refine ⟨37776940191092950214893571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 100738507176247867239716189 37776940191092950214893571)
      ·
        refine ⟨56665410286639425322340357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37776940191092950214893571 56665410286639425322340357)
        ·
          refine ⟨10624764428744892247938817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 56665410286639425322340357 10624764428744892247938817)
          ·
            refine ⟨7968573321558669185954113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10624764428744892247938817 7968573321558669185954113)
            ·
              refine ⟨5976429991169001889465585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7968573321558669185954113 5976429991169001889465585)
              ·
                refine ⟨4482322493376751417099189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5976429991169001889465585 4482322493376751417099189)
                ·
                  refine ⟨420217733754070445353049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4482322493376751417099189 420217733754070445353049)
                  ·
                    rfl

theorem cell21_1841335_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 2, 2, 2, 5].length) (baseStart_1841335 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1841335 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1841335 prefixEnd_1841335 := by exact prefixLift 1841335
  have htrace : WordTrace (prefixWord ++ tailWord_1841335) baseStart_1841335 baseEnd_1841335 := by
    simpa [prefixWord, tailWord_1841335, baseEnd_1841335] using wordTrace_append hprefix tailTrace_1841335
  have hstable : (prefixWord ++ tailWord_1841335).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1841335).length < 2 ^ (prefixWord ++ tailWord_1841335).sum := by decide
  have hdescent : baseEnd_1841335 < baseStart_1841335 := by decide
  rcases family_descends (prefixWord ++ tailWord_1841335) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1841349 : List Nat := [1, 3, 1, 1, 1, 1, 5, 2, 6]
def baseStart_1841349 : Nat := 118140960795 + 1841349 * 2 ^ 59
def prefixEnd_1841349 : Nat := 4983230072969 + 3 ^ 40 * 1841349 * 2
def baseEnd_1841349 : Nat := 420220928744809532119687

theorem tailTrace_1841349 : CollatzResearch.WordTrace tailWord_1841349 prefixEnd_1841349 420220928744809532119687 := by
  unfold tailWord_1841349
  simp only [CollatzResearch.WordTrace]
  refine ⟨67159515406114525217487101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44773010270743016811658067 67159515406114525217487101)
  ·
    refine ⟨25184818277292946956557663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 67159515406114525217487101 25184818277292946956557663)
    ·
      refine ⟨37777227415939420434836495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25184818277292946956557663 37777227415939420434836495)
      ·
        refine ⟨56665841123909130652254743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37777227415939420434836495 56665841123909130652254743)
        ·
          refine ⟨84998761685863695978382115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56665841123909130652254743 84998761685863695978382115)
          ·
            refine ⟨127498142528795543967573173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 84998761685863695978382115 127498142528795543967573173)
            ·
              refine ⟨11952950862074582246959985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 127498142528795543967573173 11952950862074582246959985)
              ·
                refine ⟨8964713146555936685219989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11952950862074582246959985 8964713146555936685219989)
                ·
                  refine ⟨420220928744809532119687, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8964713146555936685219989 420220928744809532119687)
                  ·
                    rfl

theorem cell21_1841349_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 5, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 5, 2, 6].length) (baseStart_1841349 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1841349 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1841349 prefixEnd_1841349 := by exact prefixLift 1841349
  have htrace : WordTrace (prefixWord ++ tailWord_1841349) baseStart_1841349 baseEnd_1841349 := by
    simpa [prefixWord, tailWord_1841349, baseEnd_1841349] using wordTrace_append hprefix tailTrace_1841349
  have hstable : (prefixWord ++ tailWord_1841349).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1841349).length < 2 ^ (prefixWord ++ tailWord_1841349).sum := by decide
  have hdescent : baseEnd_1841349 < baseStart_1841349 := by decide
  rcases family_descends (prefixWord ++ tailWord_1841349) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1841383 : List Nat := [1, 1, 5, 3, 1, 2, 1, 3, 4]
def baseStart_1841383 : Nat := 118140960795 + 1841383 * 2 ^ 59
def prefixEnd_1841383 : Nat := 4983230072969 + 3 ^ 40 * 1841383 * 2
def baseEnd_1841383 : Nat := 420228688008033028552951

theorem tailTrace_1841383 : CollatzResearch.WordTrace tailWord_1841383 prefixEnd_1841383 420228688008033028552951 := by
  unfold tailWord_1841383
  simp only [CollatzResearch.WordTrace]
  refine ⟨67160755487991349024224803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44773836991994232682816535 67160755487991349024224803)
  ·
    refine ⟨100741133231987023536337205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67160755487991349024224803 100741133231987023536337205)
    ·
      refine ⟨9444481240498783456531613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 100741133231987023536337205 9444481240498783456531613)
      ·
        refine ⟨3541680465187043796199355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9444481240498783456531613 3541680465187043796199355)
        ·
          refine ⟨5312520697780565694299033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3541680465187043796199355 5312520697780565694299033)
          ·
            refine ⟨3984390523335424270724275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5312520697780565694299033 3984390523335424270724275)
            ·
              refine ⟨5976585785003136406086413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3984390523335424270724275 5976585785003136406086413)
              ·
                refine ⟨2241219669376176152282405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5976585785003136406086413 2241219669376176152282405)
                ·
                  refine ⟨420228688008033028552951, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2241219669376176152282405 420228688008033028552951)
                  ·
                    rfl

theorem cell21_1841383_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 2, 1, 3, 4].length) (baseStart_1841383 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1841383 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1841383 prefixEnd_1841383 := by exact prefixLift 1841383
  have htrace : WordTrace (prefixWord ++ tailWord_1841383) baseStart_1841383 baseEnd_1841383 := by
    simpa [prefixWord, tailWord_1841383, baseEnd_1841383] using wordTrace_append hprefix tailTrace_1841383
  have hstable : (prefixWord ++ tailWord_1841383).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1841383).length < 2 ^ (prefixWord ++ tailWord_1841383).sum := by decide
  have hdescent : baseEnd_1841383 < baseStart_1841383 := by decide
  rcases family_descends (prefixWord ++ tailWord_1841383) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1841473 : List Nat := [1, 2, 5, 2, 2, 1, 8]
def baseStart_1841473 : Nat := 118140960795 + 1841473 * 2 ^ 59
def prefixEnd_1841473 : Nat := 4983230072969 + 3 ^ 40 * 1841473 * 2
def baseEnd_1841473 : Nat := 46694358581579208005863

theorem tailTrace_1841473 : CollatzResearch.WordTrace tailWord_1841473 prefixEnd_1841473 46694358581579208005863 := by
  unfold tailWord_1841473
  simp only [CollatzResearch.WordTrace]
  refine ⟨67164038057665294395001073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44776025371776862930000715 67164038057665294395001073)
  ·
    refine ⟨50373028543248970796250805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67164038057665294395001073 50373028543248970796250805)
    ·
      refine ⟨4722471425929591012148513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 50373028543248970796250805 4722471425929591012148513)
      ·
        refine ⟨3541853569447193259111385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4722471425929591012148513 3541853569447193259111385)
        ·
          refine ⟨2656390177085394944333539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3541853569447193259111385 2656390177085394944333539)
          ·
            refine ⟨3984585265628092416500309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2656390177085394944333539 3984585265628092416500309)
            ·
              refine ⟨46694358581579208005863, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 3984585265628092416500309 46694358581579208005863)
              ·
                rfl

theorem cell21_1841473_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 2, 1, 8].length) (baseStart_1841473 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1841473 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1841473 prefixEnd_1841473 := by exact prefixLift 1841473
  have htrace : WordTrace (prefixWord ++ tailWord_1841473) baseStart_1841473 baseEnd_1841473 := by
    simpa [prefixWord, tailWord_1841473, baseEnd_1841473] using wordTrace_append hprefix tailTrace_1841473
  have hstable : (prefixWord ++ tailWord_1841473).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1841473).length < 2 ^ (prefixWord ++ tailWord_1841473).sum := by decide
  have hdescent : baseEnd_1841473 < baseStart_1841473 := by decide
  rcases family_descends (prefixWord ++ tailWord_1841473) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1841515 : List Nat := [1, 1, 1, 1, 2, 2, 2, 11]
def baseStart_1841515 : Nat := 118140960795 + 1841515 * 2 ^ 59
def prefixEnd_1841515 : Nat := 4983230072969 + 3 ^ 40 * 1841515 * 2
def baseEnd_1841515 : Nat := 140086270735476710784227

theorem tailTrace_1841515 : CollatzResearch.WordTrace tailWord_1841515 prefixEnd_1841515 140086270735476710784227 := by
  unfold tailWord_1841515
  simp only [CollatzResearch.WordTrace]
  refine ⟨67165569923513135568029999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44777046615675423712019999 67165569923513135568029999)
  ·
    refine ⟨100748354885269703352044999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67165569923513135568029999 100748354885269703352044999)
    ·
      refine ⟨151122532327904555028067499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100748354885269703352044999 151122532327904555028067499)
      ·
        refine ⟨226683798491856832542101249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 151122532327904555028067499 226683798491856832542101249)
        ·
          refine ⟨170012848868892624406575937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 226683798491856832542101249 170012848868892624406575937)
          ·
            refine ⟨127509636651669468304931953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 170012848868892624406575937 127509636651669468304931953)
            ·
              refine ⟨95632227488752101228698965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 127509636651669468304931953 95632227488752101228698965)
              ·
                refine ⟨140086270735476710784227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 95632227488752101228698965 140086270735476710784227)
                ·
                  rfl

theorem cell21_1841515_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 2, 11].length) (baseStart_1841515 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1841515 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1841515 prefixEnd_1841515 := by exact prefixLift 1841515
  have htrace : WordTrace (prefixWord ++ tailWord_1841515) baseStart_1841515 baseEnd_1841515 := by
    simpa [prefixWord, tailWord_1841515, baseEnd_1841515] using wordTrace_append hprefix tailTrace_1841515
  have hstable : (prefixWord ++ tailWord_1841515).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1841515).length < 2 ^ (prefixWord ++ tailWord_1841515).sum := by decide
  have hdescent : baseEnd_1841515 < baseStart_1841515 := by decide
  rcases family_descends (prefixWord ++ tailWord_1841515) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1841538 : List Nat := [3, 4, 2, 1, 2, 2, 1, 1, 5]
def baseStart_1841538 : Nat := 118140960795 + 1841538 * 2 ^ 59
def prefixEnd_1841538 : Nat := 4983230072969 + 3 ^ 40 * 1841538 * 2
def baseEnd_1841538 : Nat := 420264061119787203469301

theorem tailTrace_1841538 : CollatzResearch.WordTrace tailWord_1841538 prefixEnd_1841538 420264061119787203469301 := by
  unfold tailWord_1841538
  simp only [CollatzResearch.WordTrace]
  refine ⟨16791602200607452624029317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 44777605868286540330744845 16791602200607452624029317)
  ·
    refine ⟨3148425412613897367005497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 16791602200607452624029317 3148425412613897367005497)
    ·
      refine ⟨2361319059460423025254123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3148425412613897367005497 2361319059460423025254123)
      ·
        refine ⟨3541978589190634537881185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2361319059460423025254123 3541978589190634537881185)
        ·
          refine ⟨2656483941892975903410889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3541978589190634537881185 2656483941892975903410889)
          ·
            refine ⟨1992362956419731927558167, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2656483941892975903410889 1992362956419731927558167)
            ·
              refine ⟨2988544434629597891337251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1992362956419731927558167 2988544434629597891337251)
              ·
                refine ⟨4482816651944396837005877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2988544434629597891337251 4482816651944396837005877)
                ·
                  refine ⟨420264061119787203469301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4482816651944396837005877 420264061119787203469301)
                  ·
                    rfl

theorem cell21_1841538_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 2, 2, 1, 1, 5].length) (baseStart_1841538 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1841538 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1841538 prefixEnd_1841538 := by exact prefixLift 1841538
  have htrace : WordTrace (prefixWord ++ tailWord_1841538) baseStart_1841538 baseEnd_1841538 := by
    simpa [prefixWord, tailWord_1841538, baseEnd_1841538] using wordTrace_append hprefix tailTrace_1841538
  have hstable : (prefixWord ++ tailWord_1841538).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1841538).length < 2 ^ (prefixWord ++ tailWord_1841538).sum := by decide
  have hdescent : baseEnd_1841538 < baseStart_1841538 := by decide
  rcases family_descends (prefixWord ++ tailWord_1841538) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1841591 : List Nat := [1, 1, 3, 1, 3, 12]
def baseStart_1841591 : Nat := 118140960795 + 1841591 * 2 ^ 59
def prefixEnd_1841591 : Nat := 4983230072969 + 3 ^ 40 * 1841591 * 2
def baseEnd_1841591 : Nat := 15565783571921144040217

theorem tailTrace_1841591 : CollatzResearch.WordTrace tailWord_1841591 prefixEnd_1841591 15565783571921144040217 := by
  unfold tailWord_1841591
  simp only [CollatzResearch.WordTrace]
  refine ⟨67168341871237800547796627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44778894580825200365197751 67168341871237800547796627)
  ·
    refine ⟨100752512806856700821694941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67168341871237800547796627 100752512806856700821694941)
    ·
      refine ⟨37782192302571262808135603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 100752512806856700821694941 37782192302571262808135603)
      ·
        refine ⟨56673288453856894212203405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37782192302571262808135603 56673288453856894212203405)
        ·
          refine ⟨21252483170196335329576277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 56673288453856894212203405 21252483170196335329576277)
          ·
            refine ⟨15565783571921144040217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 12 21252483170196335329576277 15565783571921144040217)
            ·
              rfl

theorem cell21_1841591_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 12].length) (baseStart_1841591 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1841591 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1841591 prefixEnd_1841591 := by exact prefixLift 1841591
  have htrace : WordTrace (prefixWord ++ tailWord_1841591) baseStart_1841591 baseEnd_1841591 := by
    simpa [prefixWord, tailWord_1841591, baseEnd_1841591] using wordTrace_append hprefix tailTrace_1841591
  have hstable : (prefixWord ++ tailWord_1841591).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1841591).length < 2 ^ (prefixWord ++ tailWord_1841591).sum := by decide
  have hdescent : baseEnd_1841591 < baseStart_1841591 := by decide
  rcases family_descends (prefixWord ++ tailWord_1841591) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1841597 : List Nat := [1, 4, 1, 2, 2, 2, 4, 2, 3]
def baseStart_1841597 : Nat := 118140960795 + 1841597 * 2 ^ 59
def prefixEnd_1841597 : Nat := 4983230072969 + 3 ^ 40 * 1841597 * 2
def baseEnd_1841597 : Nat := 420277525723616211985847

theorem tailTrace_1841597 : CollatzResearch.WordTrace tailWord_1841597 prefixEnd_1841597 420277525723616211985847 := by
  unfold tailWord_1841597
  simp only [CollatzResearch.WordTrace]
  refine ⟨67168560709216063572515045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44779040472810709048343363 67168560709216063572515045)
  ·
    refine ⟨12594105132978011919846571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 67168560709216063572515045 12594105132978011919846571)
    ·
      refine ⟨18891157699467017879769857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12594105132978011919846571 18891157699467017879769857)
      ·
        refine ⟨14168368274600263409827393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18891157699467017879769857 14168368274600263409827393)
        ·
          refine ⟨10626276205950197557370545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14168368274600263409827393 10626276205950197557370545)
          ·
            refine ⟨7969707154462648168027909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10626276205950197557370545 7969707154462648168027909)
            ·
              refine ⟨1494320091461746531505233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7969707154462648168027909 1494320091461746531505233)
              ·
                refine ⟨1120740068596309898628925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1494320091461746531505233 1120740068596309898628925)
                ·
                  refine ⟨420277525723616211985847, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1120740068596309898628925 420277525723616211985847)
                  ·
                    rfl

theorem cell21_1841597_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 2, 4, 2, 3].length) (baseStart_1841597 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1841597 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1841597 prefixEnd_1841597 := by exact prefixLift 1841597
  have htrace : WordTrace (prefixWord ++ tailWord_1841597) baseStart_1841597 baseEnd_1841597 := by
    simpa [prefixWord, tailWord_1841597, baseEnd_1841597] using wordTrace_append hprefix tailTrace_1841597
  have hstable : (prefixWord ++ tailWord_1841597).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1841597).length < 2 ^ (prefixWord ++ tailWord_1841597).sum := by decide
  have hdescent : baseEnd_1841597 < baseStart_1841597 := by decide
  rcases family_descends (prefixWord ++ tailWord_1841597) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1841608 : List Nat := [2, 1, 3, 1, 3, 2, 3, 6]
def baseStart_1841608 : Nat := 118140960795 + 1841608 * 2 ^ 59
def prefixEnd_1841608 : Nat := 4983230072969 + 3 ^ 40 * 1841608 * 2
def baseEnd_1841608 : Nat := 140093345357827545767497

theorem tailTrace_1841608 : CollatzResearch.WordTrace tailWord_1841608 prefixEnd_1841608 140093345357827545767497 := by
  unfold tailWord_1841608
  simp only [CollatzResearch.WordTrace]
  refine ⟨33584480956088106225582739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44779307941450808300776985 33584480956088106225582739)
  ·
    refine ⟨50376721434132159338374109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33584480956088106225582739 50376721434132159338374109)
    ·
      refine ⟨18891270537799559751890291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 50376721434132159338374109 18891270537799559751890291)
      ·
        refine ⟨28336905806699339627835437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18891270537799559751890291 28336905806699339627835437)
        ·
          refine ⟨10626339677512252360438289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28336905806699339627835437 10626339677512252360438289)
          ·
            refine ⟨7969754758134189270328717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10626339677512252360438289 7969754758134189270328717)
            ·
              refine ⟨2988658034300320976373269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7969754758134189270328717 2988658034300320976373269)
              ·
                refine ⟨140093345357827545767497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2988658034300320976373269 140093345357827545767497)
                ·
                  rfl

theorem cell21_1841608_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 2, 3, 6].length) (baseStart_1841608 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1841608 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1841608 prefixEnd_1841608 := by exact prefixLift 1841608
  have htrace : WordTrace (prefixWord ++ tailWord_1841608) baseStart_1841608 baseEnd_1841608 := by
    simpa [prefixWord, tailWord_1841608, baseEnd_1841608] using wordTrace_append hprefix tailTrace_1841608
  have hstable : (prefixWord ++ tailWord_1841608).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1841608).length < 2 ^ (prefixWord ++ tailWord_1841608).sum := by decide
  have hdescent : baseEnd_1841608 < baseStart_1841608 := by decide
  rcases family_descends (prefixWord ++ tailWord_1841608) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1841667 : List Nat := [1, 1, 1, 3, 2, 1, 4, 8]
def baseStart_1841667 : Nat := 118140960795 + 1841667 * 2 ^ 59
def prefixEnd_1841667 : Nat := 4983230072969 + 3 ^ 40 * 1841667 * 2
def baseEnd_1841667 : Nat := 140097833559103881939679

theorem tailTrace_1841667 : CollatzResearch.WordTrace tailWord_1841667 prefixEnd_1841667 140097833559103881939679 := by
  unfold tailWord_1841667
  simp only [CollatzResearch.WordTrace]
  refine ⟨67171113818962465527563255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44780742545974977018375503 67171113818962465527563255)
  ·
    refine ⟨100756670728443698291344883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67171113818962465527563255 100756670728443698291344883)
    ·
      refine ⟨151135006092665547437017325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100756670728443698291344883 151135006092665547437017325)
      ·
        refine ⟨56675627284749580288881497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 151135006092665547437017325 56675627284749580288881497)
        ·
          refine ⟨42506720463562185216661123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56675627284749580288881497 42506720463562185216661123)
          ·
            refine ⟨63760080695343277824991685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42506720463562185216661123 63760080695343277824991685)
            ·
              refine ⟨11955015130376864592185941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 63760080695343277824991685 11955015130376864592185941)
              ·
                refine ⟨140097833559103881939679, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 11955015130376864592185941 140097833559103881939679)
                ·
                  rfl

theorem cell21_1841667_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 4, 8].length) (baseStart_1841667 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1841667 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1841667 prefixEnd_1841667 := by exact prefixLift 1841667
  have htrace : WordTrace (prefixWord ++ tailWord_1841667) baseStart_1841667 baseEnd_1841667 := by
    simpa [prefixWord, tailWord_1841667, baseEnd_1841667] using wordTrace_append hprefix tailTrace_1841667
  have hstable : (prefixWord ++ tailWord_1841667).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1841667).length < 2 ^ (prefixWord ++ tailWord_1841667).sum := by decide
  have hdescent : baseEnd_1841667 < baseStart_1841667 := by decide
  rcases family_descends (prefixWord ++ tailWord_1841667) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1841743 : List Nat := [1, 1, 2, 1, 1, 2, 6, 7]
def baseStart_1841743 : Nat := 118140960795 + 1841743 * 2 ^ 59
def prefixEnd_1841743 : Nat := 4983230072969 + 3 ^ 40 * 1841743 * 2
def baseEnd_1841743 : Nat := 140103614970917467517405

theorem tailTrace_1841743 : CollatzResearch.WordTrace tailWord_1841743 prefixEnd_1841743 140103614970917467517405 := by
  unfold tailWord_1841743
  simp only [CollatzResearch.WordTrace]
  refine ⟨67173885766687130507329883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44782590511124753671553255 67173885766687130507329883)
  ·
    refine ⟨100760828650030695760994825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67173885766687130507329883 100760828650030695760994825)
    ·
      refine ⟨75570621487523021820746119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 100760828650030695760994825 75570621487523021820746119)
      ·
        refine ⟨113355932231284532731119179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75570621487523021820746119 113355932231284532731119179)
        ·
          refine ⟨170033898346926799096678769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 113355932231284532731119179 170033898346926799096678769)
          ·
            refine ⟨127525423760195099322509077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 170033898346926799096678769 127525423760195099322509077)
            ·
              refine ⟨5977754238759145280742613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 127525423760195099322509077 5977754238759145280742613)
              ·
                refine ⟨140103614970917467517405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5977754238759145280742613 140103614970917467517405)
                ·
                  rfl

theorem cell21_1841743_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 6, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 6, 7].length) (baseStart_1841743 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1841743 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1841743 prefixEnd_1841743 := by exact prefixLift 1841743
  have htrace : WordTrace (prefixWord ++ tailWord_1841743) baseStart_1841743 baseEnd_1841743 := by
    simpa [prefixWord, tailWord_1841743, baseEnd_1841743] using wordTrace_append hprefix tailTrace_1841743
  have hstable : (prefixWord ++ tailWord_1841743).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1841743).length < 2 ^ (prefixWord ++ tailWord_1841743).sum := by decide
  have hdescent : baseEnd_1841743 < baseStart_1841743 := by decide
  rcases family_descends (prefixWord ++ tailWord_1841743) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1841822 : List Nat := [4, 3, 1, 1, 1, 1, 3, 1, 6]
def baseStart_1841822 : Nat := 118140960795 + 1841822 * 2 ^ 59
def prefixEnd_1841822 : Nat := 4983230072969 + 3 ^ 40 * 1841822 * 2
def baseEnd_1841822 : Nat := 420328873789065820735387

theorem tailTrace_1841822 : CollatzResearch.WordTrace tailWord_1841822 prefixEnd_1841822 420328873789065820735387 := by
  unfold tailWord_1841822
  simp only [CollatzResearch.WordTrace]
  refine ⟨8397095891675115874931965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 44784511422267284666303813 8397095891675115874931965)
  ·
    refine ⟨3148910959378168453099487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8397095891675115874931965 3148910959378168453099487)
    ·
      refine ⟨4723366439067252679649231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3148910959378168453099487 4723366439067252679649231)
      ·
        refine ⟨7085049658600879019473847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4723366439067252679649231 7085049658600879019473847)
        ·
          refine ⟨10627574487901318529210771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7085049658600879019473847 10627574487901318529210771)
          ·
            refine ⟨15941361731851977793816157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10627574487901318529210771 15941361731851977793816157)
            ·
              refine ⟨5978010649444491672681059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15941361731851977793816157 5978010649444491672681059)
              ·
                refine ⟨8967015974166737509021589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5978010649444491672681059 8967015974166737509021589)
                ·
                  refine ⟨420328873789065820735387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8967015974166737509021589 420328873789065820735387)
                  ·
                    rfl

theorem cell21_1841822_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 3, 1, 6].length) (baseStart_1841822 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1841822 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1841822 prefixEnd_1841822 := by exact prefixLift 1841822
  have htrace : WordTrace (prefixWord ++ tailWord_1841822) baseStart_1841822 baseEnd_1841822 := by
    simpa [prefixWord, tailWord_1841822, baseEnd_1841822] using wordTrace_append hprefix tailTrace_1841822
  have hstable : (prefixWord ++ tailWord_1841822).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1841822).length < 2 ^ (prefixWord ++ tailWord_1841822).sum := by decide
  have hdescent : baseEnd_1841822 < baseStart_1841822 := by decide
  rcases family_descends (prefixWord ++ tailWord_1841822) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1841850 : List Nat := [3, 1, 1, 1, 2, 3, 1, 4, 5]
def baseStart_1841850 : Nat := 118140960795 + 1841850 * 2 ^ 59
def prefixEnd_1841850 : Nat := 4983230072969 + 3 ^ 40 * 1841850 * 2
def baseEnd_1841850 : Nat := 420335263770543994268663

theorem tailTrace_1841850 : CollatzResearch.WordTrace tailWord_1841850 prefixEnd_1841850 420335263770543994268663 := by
  unfold tailWord_1841850
  simp only [CollatzResearch.WordTrace]
  refine ⟨16794447094324871945368751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 44785192251532991854316669 16794447094324871945368751)
  ·
    refine ⟨25191670641487307918053127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16794447094324871945368751 25191670641487307918053127)
    ·
      refine ⟨37787505962230961877079691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25191670641487307918053127 37787505962230961877079691)
      ·
        refine ⟨56681258943346442815619537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37787505962230961877079691 56681258943346442815619537)
        ·
          refine ⟨42510944207509832111714653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56681258943346442815619537 42510944207509832111714653)
          ·
            refine ⟨15941604077816187041892995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 42510944207509832111714653 15941604077816187041892995)
            ·
              refine ⟨23912406116724280562839493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15941604077816187041892995 23912406116724280562839493)
              ·
                refine ⟨4483576146885802605532405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 23912406116724280562839493 4483576146885802605532405)
                ·
                  refine ⟨420335263770543994268663, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4483576146885802605532405 420335263770543994268663)
                  ·
                    rfl

theorem cell21_1841850_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 1, 4, 5].length) (baseStart_1841850 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1841850 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1841850 prefixEnd_1841850 := by exact prefixLift 1841850
  have htrace : WordTrace (prefixWord ++ tailWord_1841850) baseStart_1841850 baseEnd_1841850 := by
    simpa [prefixWord, tailWord_1841850, baseEnd_1841850] using wordTrace_append hprefix tailTrace_1841850
  have hstable : (prefixWord ++ tailWord_1841850).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1841850).length < 2 ^ (prefixWord ++ tailWord_1841850).sum := by decide
  have hdescent : baseEnd_1841850 < baseStart_1841850 := by decide
  rcases family_descends (prefixWord ++ tailWord_1841850) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1841853 : List Nat := [1, 4, 1, 2, 1, 5, 2, 5]
def baseStart_1841853 : Nat := 118140960795 + 1841853 * 2 ^ 59
def prefixEnd_1841853 : Nat := 4983230072969 + 3 ^ 40 * 1841853 * 2
def baseEnd_1841853 : Nat := 140111982803805551906219

theorem tailTrace_1841853 : CollatzResearch.WordTrace tailWord_1841853 prefixEnd_1841853 140111982803805551906219 := by
  unfold tailWord_1841853
  simp only [CollatzResearch.WordTrace]
  refine ⟨67177897796288619293834213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44785265197525746195889475 67177897796288619293834213)
  ·
    refine ⟨12595855836804116117593915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 67177897796288619293834213 12595855836804116117593915)
    ·
      refine ⟨18893783755206174176390873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12595855836804116117593915 18893783755206174176390873)
      ·
        refine ⟨14170337816404630632293155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18893783755206174176390873 14170337816404630632293155)
        ·
          refine ⟨21255506724606945948439733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14170337816404630632293155 21255506724606945948439733)
          ·
            refine ⟨1992703755431901182666225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 21255506724606945948439733 1992703755431901182666225)
            ·
              refine ⟨1494527816573925886999669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1992703755431901182666225 1494527816573925886999669)
              ·
                refine ⟨140111982803805551906219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1494527816573925886999669 140111982803805551906219)
                ·
                  rfl

theorem cell21_1841853_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 5, 2, 5].length) (baseStart_1841853 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1841853 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1841853 prefixEnd_1841853 := by exact prefixLift 1841853
  have htrace : WordTrace (prefixWord ++ tailWord_1841853) baseStart_1841853 baseEnd_1841853 := by
    simpa [prefixWord, tailWord_1841853, baseEnd_1841853] using wordTrace_append hprefix tailTrace_1841853
  have hstable : (prefixWord ++ tailWord_1841853).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1841853).length < 2 ^ (prefixWord ++ tailWord_1841853).sum := by decide
  have hdescent : baseEnd_1841853 < baseStart_1841853 := by decide
  rcases family_descends (prefixWord ++ tailWord_1841853) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1841881 : List Nat := [1, 2, 1, 2, 3, 2, 2, 4, 4]
def baseStart_1841881 : Nat := 118140960795 + 1841881 * 2 ^ 59
def prefixEnd_1841881 : Nat := 4983230072969 + 3 ^ 40 * 1841881 * 2
def baseEnd_1841881 : Nat := 420342338392894829251933

theorem tailTrace_1841881 : CollatzResearch.WordTrace tailWord_1841881 prefixEnd_1841881 420342338392894829251933 := by
  unfold tailWord_1841881
  simp only [CollatzResearch.WordTrace]
  refine ⟨67178919040187180075853497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44785946026791453383902331 67178919040187180075853497)
  ·
    refine ⟨50384189280140385056890123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67178919040187180075853497 50384189280140385056890123)
    ·
      refine ⟨75576283920210577585335185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50384189280140385056890123 75576283920210577585335185)
      ·
        refine ⟨56682212940157933189001389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 75576283920210577585335185 56682212940157933189001389)
        ·
          refine ⟨21255829852559224945875521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 56682212940157933189001389 21255829852559224945875521)
          ·
            refine ⟨15941872389419418709406641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21255829852559224945875521 15941872389419418709406641)
            ·
              refine ⟨11956404292064564032054981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15941872389419418709406641 11956404292064564032054981)
              ·
                refine ⟨2241825804762105756010309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11956404292064564032054981 2241825804762105756010309)
                ·
                  refine ⟨420342338392894829251933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2241825804762105756010309 420342338392894829251933)
                  ·
                    rfl

theorem cell21_1841881_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 2, 4, 4].length) (baseStart_1841881 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1841881 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1841881 prefixEnd_1841881 := by exact prefixLift 1841881
  have htrace : WordTrace (prefixWord ++ tailWord_1841881) baseStart_1841881 baseEnd_1841881 := by
    simpa [prefixWord, tailWord_1841881, baseEnd_1841881] using wordTrace_append hprefix tailTrace_1841881
  have hstable : (prefixWord ++ tailWord_1841881).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1841881).length < 2 ^ (prefixWord ++ tailWord_1841881).sum := by decide
  have hdescent : baseEnd_1841881 < baseStart_1841881 := by decide
  rcases family_descends (prefixWord ++ tailWord_1841881) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1841884 : List Nat := [2, 2, 5, 1, 1, 1, 3, 1, 5]
def baseStart_1841884 : Nat := 118140960795 + 1841884 * 2 ^ 59
def prefixEnd_1841884 : Nat := 4983230072969 + 3 ^ 40 * 1841884 * 2
def baseEnd_1841884 : Nat := 420343023033767490701927

theorem tailTrace_1841884 : CollatzResearch.WordTrace tailWord_1841884 prefixEnd_1841884 420343023033767490701927 := by
  unfold tailWord_1841884
  simp only [CollatzResearch.WordTrace]
  refine ⟨33589514229588155794106353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44786018972784207725475137 33589514229588155794106353)
  ·
    refine ⟨25192135672191116845579765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33589514229588155794106353 25192135672191116845579765)
    ·
      refine ⟨2361762719267917204273103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 25192135672191116845579765 2361762719267917204273103)
      ·
        refine ⟨3542644078901875806409655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2361762719267917204273103 3542644078901875806409655)
        ·
          refine ⟨5313966118352813709614483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3542644078901875806409655 5313966118352813709614483)
          ·
            refine ⟨7970949177529220564421725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5313966118352813709614483 7970949177529220564421725)
            ·
              refine ⟨2989105941573457711658147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7970949177529220564421725 2989105941573457711658147)
              ·
                refine ⟨4483658912360186567487221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2989105941573457711658147 4483658912360186567487221)
                ·
                  refine ⟨420343023033767490701927, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4483658912360186567487221 420343023033767490701927)
                  ·
                    rfl

theorem cell21_1841884_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 1, 3, 1, 5].length) (baseStart_1841884 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1841884 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1841884 prefixEnd_1841884 := by exact prefixLift 1841884
  have htrace : WordTrace (prefixWord ++ tailWord_1841884) baseStart_1841884 baseEnd_1841884 := by
    simpa [prefixWord, tailWord_1841884, baseEnd_1841884] using wordTrace_append hprefix tailTrace_1841884
  have hstable : (prefixWord ++ tailWord_1841884).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1841884).length < 2 ^ (prefixWord ++ tailWord_1841884).sum := by decide
  have hdescent : baseEnd_1841884 < baseStart_1841884 := by decide
  rcases family_descends (prefixWord ++ tailWord_1841884) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1841957 : List Nat := [1, 3, 1, 2, 3, 1, 1, 5, 4]
def baseStart_1841957 : Nat := 118140960795 + 1841957 * 2 ^ 59
def prefixEnd_1841957 : Nat := 4983230072969 + 3 ^ 40 * 1841957 * 2
def baseEnd_1841957 : Nat := 420359682628335585985111

theorem tailTrace_1841957 : CollatzResearch.WordTrace tailWord_1841957 prefixEnd_1841957 420359682628335585985111 := by
  unfold tailWord_1841957
  simp only [CollatzResearch.WordTrace]
  refine ⟨67181690987911845055620125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44787793991941230037080083 67181690987911845055620125)
  ·
    refine ⟨25193134120466941895857547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 67181690987911845055620125 25193134120466941895857547)
    ·
      refine ⟨37789701180700412843786321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25193134120466941895857547 37789701180700412843786321)
      ·
        refine ⟨28342275885525309632839741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37789701180700412843786321 28342275885525309632839741)
        ·
          refine ⟨10628353457071991112314903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28342275885525309632839741 10628353457071991112314903)
          ·
            refine ⟨15942530185607986668472355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10628353457071991112314903 15942530185607986668472355)
            ·
              refine ⟨23913795278411980002708533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15942530185607986668472355 23913795278411980002708533)
              ·
                refine ⟨2241918307351123125253925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 23913795278411980002708533 2241918307351123125253925)
                ·
                  refine ⟨420359682628335585985111, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2241918307351123125253925 420359682628335585985111)
                  ·
                    rfl

theorem cell21_1841957_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 1, 5, 4].length) (baseStart_1841957 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1841957 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1841957 prefixEnd_1841957 := by exact prefixLift 1841957
  have htrace : WordTrace (prefixWord ++ tailWord_1841957) baseStart_1841957 baseEnd_1841957 := by
    simpa [prefixWord, tailWord_1841957, baseEnd_1841957] using wordTrace_append hprefix tailTrace_1841957
  have hstable : (prefixWord ++ tailWord_1841957).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1841957).length < 2 ^ (prefixWord ++ tailWord_1841957).sum := by decide
  have hdescent : baseEnd_1841957 < baseStart_1841957 := by decide
  rcases family_descends (prefixWord ++ tailWord_1841957) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1842112 : List Nat := [2, 1, 1, 2, 3, 3, 4, 2, 3]
def baseStart_1842112 : Nat := 118140960795 + 1842112 * 2 ^ 59
def prefixEnd_1842112 : Nat := 4983230072969 + 3 ^ 40 * 1842112 * 2
def baseEnd_1842112 : Nat := 420395055740089760901461

theorem tailTrace_1842112 : CollatzResearch.WordTrace tailWord_1842112 prefixEnd_1842112 420395055740089760901461 := by
  unfold tailWord_1842112
  simp only [CollatzResearch.WordTrace]
  refine ⟨33593672151175153263756295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44791562868233537685008393 33593672151175153263756295)
  ·
    refine ⟨50390508226762729895634443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33593672151175153263756295 50390508226762729895634443)
    ·
      refine ⟨75585762340144094843451665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50390508226762729895634443 75585762340144094843451665)
      ·
        refine ⟨56689321755108071132588749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 75585762340144094843451665 56689321755108071132588749)
        ·
          refine ⟨21258495658165526674720781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 56689321755108071132588749 21258495658165526674720781)
          ·
            refine ⟨7971935871812072503020293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21258495658165526674720781 7971935871812072503020293)
            ·
              refine ⟨1494737975964763594316305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7971935871812072503020293 1494737975964763594316305)
              ·
                refine ⟨1121053481973572695737229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1494737975964763594316305 1121053481973572695737229)
                ·
                  refine ⟨420395055740089760901461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1121053481973572695737229 420395055740089760901461)
                  ·
                    rfl

theorem cell21_1842112_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 3, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 3, 4, 2, 3].length) (baseStart_1842112 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1842112 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1842112 prefixEnd_1842112 := by exact prefixLift 1842112
  have htrace : WordTrace (prefixWord ++ tailWord_1842112) baseStart_1842112 baseEnd_1842112 := by
    simpa [prefixWord, tailWord_1842112, baseEnd_1842112] using wordTrace_append hprefix tailTrace_1842112
  have hstable : (prefixWord ++ tailWord_1842112).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1842112).length < 2 ^ (prefixWord ++ tailWord_1842112).sum := by decide
  have hdescent : baseEnd_1842112 < baseStart_1842112 := by decide
  rcases family_descends (prefixWord ++ tailWord_1842112) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1842123 : List Nat := [1, 1, 1, 1, 3, 5, 3, 6]
def baseStart_1842123 : Nat := 118140960795 + 1842123 * 2 ^ 59
def prefixEnd_1842123 : Nat := 4983230072969 + 3 ^ 40 * 1842123 * 2
def baseEnd_1842123 : Nat := 140132522029985395406035

theorem tailTrace_1842123 : CollatzResearch.WordTrace tailWord_1842123 prefixEnd_1842123 140132522029985395406035 := by
  unfold tailWord_1842123
  simp only [CollatzResearch.WordTrace]
  refine ⟨67187745505310455406163023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44791830336873636937442015 67187745505310455406163023)
  ·
    refine ⟨100781618257965683109244535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67187745505310455406163023 100781618257965683109244535)
    ·
      refine ⟨151172427386948524663866803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100781618257965683109244535 151172427386948524663866803)
      ·
        refine ⟨226758641080422786995800205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 151172427386948524663866803 226758641080422786995800205)
        ·
          refine ⟨85034490405158545123425077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 226758641080422786995800205 85034490405158545123425077)
          ·
            refine ⟨7971983475483613605321101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 85034490405158545123425077 7971983475483613605321101)
            ·
              refine ⟨2989493803306355101995413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7971983475483613605321101 2989493803306355101995413)
              ·
                refine ⟨140132522029985395406035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2989493803306355101995413 140132522029985395406035)
                ·
                  rfl

theorem cell21_1842123_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 5, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 5, 3, 6].length) (baseStart_1842123 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1842123 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1842123 prefixEnd_1842123 := by exact prefixLift 1842123
  have htrace : WordTrace (prefixWord ++ tailWord_1842123) baseStart_1842123 baseEnd_1842123 := by
    simpa [prefixWord, tailWord_1842123, baseEnd_1842123] using wordTrace_append hprefix tailTrace_1842123
  have hstable : (prefixWord ++ tailWord_1842123).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1842123).length < 2 ^ (prefixWord ++ tailWord_1842123).sum := by decide
  have hdescent : baseEnd_1842123 < baseStart_1842123 := by decide
  rcases family_descends (prefixWord ++ tailWord_1842123) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1842205 : List Nat := [1, 4, 2, 2, 3, 2, 1, 3, 3]
def baseStart_1842205 : Nat := 118140960795 + 1842205 * 2 ^ 59
def prefixEnd_1842205 : Nat := 4983230072969 + 3 ^ 40 * 1842205 * 2
def baseEnd_1842205 : Nat := 420416279607142265851271

theorem tailTrace_1842205 : CollatzResearch.WordTrace tailWord_1842205 prefixEnd_1842205 420416279607142265851271 := by
  unfold tailWord_1842205
  simp only [CollatzResearch.WordTrace]
  refine ⟨67190736291013383410648069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44793824194008922273765379 67190736291013383410648069)
  ·
    refine ⟨12598263054565009389496513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 67190736291013383410648069 12598263054565009389496513)
    ·
      refine ⟨9448697290923757042122385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12598263054565009389496513 9448697290923757042122385)
      ·
        refine ⟨7086522968192817781591789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9448697290923757042122385 7086522968192817781591789)
        ·
          refine ⟨2657446113072306668096921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7086522968192817781591789 2657446113072306668096921)
          ·
            refine ⟨1993084584804230001072691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2657446113072306668096921 1993084584804230001072691)
            ·
              refine ⟨2989626877206345001609037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1993084584804230001072691 2989626877206345001609037)
              ·
                refine ⟨1121110078952379375603389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2989626877206345001609037 1121110078952379375603389)
                ·
                  refine ⟨420416279607142265851271, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1121110078952379375603389 420416279607142265851271)
                  ·
                    rfl

theorem cell21_1842205_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 3, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 3, 2, 1, 3, 3].length) (baseStart_1842205 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1842205 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1842205 prefixEnd_1842205 := by exact prefixLift 1842205
  have htrace : WordTrace (prefixWord ++ tailWord_1842205) baseStart_1842205 baseEnd_1842205 := by
    simpa [prefixWord, tailWord_1842205, baseEnd_1842205] using wordTrace_append hprefix tailTrace_1842205
  have hstable : (prefixWord ++ tailWord_1842205).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1842205).length < 2 ^ (prefixWord ++ tailWord_1842205).sum := by decide
  have hdescent : baseEnd_1842205 < baseStart_1842205 := by decide
  rcases family_descends (prefixWord ++ tailWord_1842205) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1842354 : List Nat := [3, 2, 1, 1, 1, 5, 3, 1, 4]
def baseStart_1842354 : Nat := 118140960795 + 1842354 * 2 ^ 59
def prefixEnd_1842354 : Nat := 4983230072969 + 3 ^ 40 * 1842354 * 2
def baseEnd_1842354 : Nat := 420450283437151117867633

theorem tailTrace_1842354 : CollatzResearch.WordTrace tailWord_1842354 prefixEnd_1842354 420450283437151117867633 := by
  unfold tailWord_1842354
  simp only [CollatzResearch.WordTrace]
  refine ⟨16799042691868395464455529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 44797447178315721238548077 16799042691868395464455529)
  ·
    refine ⟨12599282018901296598341647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16799042691868395464455529 12599282018901296598341647)
    ·
      refine ⟨18898923028351944897512471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12599282018901296598341647 18898923028351944897512471)
      ·
        refine ⟨28348384542527917346268707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18898923028351944897512471 28348384542527917346268707)
        ·
          refine ⟨42522576813791876019403061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28348384542527917346268707 42522576813791876019403061)
          ·
            refine ⟨3986491576292988376819037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 42522576813791876019403061 3986491576292988376819037)
            ·
              refine ⟨1494934341109870641307139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3986491576292988376819037 1494934341109870641307139)
              ·
                refine ⟨2242401511664805961960709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1494934341109870641307139 2242401511664805961960709)
                ·
                  refine ⟨420450283437151117867633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2242401511664805961960709 420450283437151117867633)
                  ·
                    rfl

theorem cell21_1842354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 5, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 5, 3, 1, 4].length) (baseStart_1842354 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1842354 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1842354 prefixEnd_1842354 := by exact prefixLift 1842354
  have htrace : WordTrace (prefixWord ++ tailWord_1842354) baseStart_1842354 baseEnd_1842354 := by
    simpa [prefixWord, tailWord_1842354, baseEnd_1842354] using wordTrace_append hprefix tailTrace_1842354
  have hstable : (prefixWord ++ tailWord_1842354).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1842354).length < 2 ^ (prefixWord ++ tailWord_1842354).sum := by decide
  have hdescent : baseEnd_1842354 < baseStart_1842354 := by decide
  rcases family_descends (prefixWord ++ tailWord_1842354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1842568 : List Nat := [2, 1, 3, 3, 1, 3, 3, 2, 3]
def baseStart_1842568 : Nat := 118140960795 + 1842568 * 2 ^ 59
def prefixEnd_1842568 : Nat := 4983230072969 + 3 ^ 40 * 1842568 * 2
def baseEnd_1842568 : Nat := 420499121152734301300529

theorem tailTrace_1842568 : CollatzResearch.WordTrace tailWord_1842568 prefixEnd_1842568 420499121152734301300529 := by
  unfold tailWord_1842568
  simp only [CollatzResearch.WordTrace]
  refine ⟨33601987994349148203056179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44802650659132197604074905 33601987994349148203056179)
  ·
    refine ⟨50402981991523722304584269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33601987994349148203056179 50402981991523722304584269)
    ·
      refine ⟨18901118246821395864219101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 50402981991523722304584269 18901118246821395864219101)
      ·
        refine ⟨7087919342558023449082163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18901118246821395864219101 7087919342558023449082163)
        ·
          refine ⟨10631879013837035173623245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7087919342558023449082163 10631879013837035173623245)
          ·
            refine ⟨3986954630188888190108717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10631879013837035173623245 3986954630188888190108717)
            ·
              refine ⟨1495107986320833071290769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3986954630188888190108717 1495107986320833071290769)
              ·
                refine ⟨1121330989740624803468077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1495107986320833071290769 1121330989740624803468077)
                ·
                  refine ⟨420499121152734301300529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1121330989740624803468077 420499121152734301300529)
                  ·
                    rfl

theorem cell21_1842568_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 3, 3, 2, 3].length) (baseStart_1842568 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1842568 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1842568 prefixEnd_1842568 := by exact prefixLift 1842568
  have htrace : WordTrace (prefixWord ++ tailWord_1842568) baseStart_1842568 baseEnd_1842568 := by
    simpa [prefixWord, tailWord_1842568, baseEnd_1842568] using wordTrace_append hprefix tailTrace_1842568
  have hstable : (prefixWord ++ tailWord_1842568).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1842568).length < 2 ^ (prefixWord ++ tailWord_1842568).sum := by decide
  have hdescent : baseEnd_1842568 < baseStart_1842568 := by decide
  rcases family_descends (prefixWord ++ tailWord_1842568) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1842607 : List Nat := [1, 1, 2, 1, 2, 2, 1, 3, 8]
def baseStart_1842607 : Nat := 118140960795 + 1842607 * 2 ^ 59
def prefixEnd_1842607 : Nat := 4983230072969 + 3 ^ 40 * 1842607 * 2
def baseEnd_1842607 : Nat := 420508021484078900150449

theorem tailTrace_1842607 : CollatzResearch.WordTrace tailWord_1842607 prefixEnd_1842607 420508021484078900150449 := by
  unfold tailWord_1842607
  simp only [CollatzResearch.WordTrace]
  refine ⟨67205398435557006066782075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44803598957038004044521383 67205398435557006066782075)
  ·
    refine ⟨100808097653335509100173113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67205398435557006066782075 100808097653335509100173113)
    ·
      refine ⟨75606073240001631825129835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 100808097653335509100173113 75606073240001631825129835)
      ·
        refine ⟨113409109860002447737694753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75606073240001631825129835 113409109860002447737694753)
        ·
          refine ⟨85056832395001835803271065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 113409109860002447737694753 85056832395001835803271065)
          ·
            refine ⟨63792624296251376852453299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 85056832395001835803271065 63792624296251376852453299)
            ·
              refine ⟨95688936444377065278679949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63792624296251376852453299 95688936444377065278679949)
              ·
                refine ⟨35883351166641399479504981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 95688936444377065278679949 35883351166641399479504981)
                ·
                  refine ⟨420508021484078900150449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 35883351166641399479504981 420508021484078900150449)
                  ·
                    rfl

theorem cell21_1842607_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 1, 3, 8].length) (baseStart_1842607 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1842607 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1842607 prefixEnd_1842607 := by exact prefixLift 1842607
  have htrace : WordTrace (prefixWord ++ tailWord_1842607) baseStart_1842607 baseEnd_1842607 := by
    simpa [prefixWord, tailWord_1842607, baseEnd_1842607] using wordTrace_append hprefix tailTrace_1842607
  have hstable : (prefixWord ++ tailWord_1842607).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1842607).length < 2 ^ (prefixWord ++ tailWord_1842607).sum := by decide
  have hdescent : baseEnd_1842607 < baseStart_1842607 := by decide
  rcases family_descends (prefixWord ++ tailWord_1842607) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1842624 : List Nat := [2, 1, 1, 2, 3, 1, 3, 4, 4]
def baseStart_1842624 : Nat := 118140960795 + 1842624 * 2 ^ 59
def prefixEnd_1842624 : Nat := 4983230072969 + 3 ^ 40 * 1842624 * 2
def baseEnd_1842624 : Nat := 420511901115690648367081

theorem tailTrace_1842624 : CollatzResearch.WordTrace tailWord_1842624 prefixEnd_1842624 420511901115690648367081 := by
  unfold tailWord_1842624
  simp only [CollatzResearch.WordTrace]
  refine ⟨33603009238247708985075463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44804012317663611980100617 33603009238247708985075463)
  ·
    refine ⟨50404513857371563477613195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33603009238247708985075463 50404513857371563477613195)
    ·
      refine ⟨75606770786057345216419793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50404513857371563477613195 75606770786057345216419793)
      ·
        refine ⟨56705078089543008912314845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 75606770786057345216419793 56705078089543008912314845)
        ·
          refine ⟨21264404283578628342118067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 56705078089543008912314845 21264404283578628342118067)
          ·
            refine ⟨31896606425367942513177101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21264404283578628342118067 31896606425367942513177101)
            ·
              refine ⟨11961227409512978442441413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31896606425367942513177101 11961227409512978442441413)
              ·
                refine ⟨2242730139283683457957765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11961227409512978442441413 2242730139283683457957765)
                ·
                  refine ⟨420511901115690648367081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2242730139283683457957765 420511901115690648367081)
                  ·
                    rfl

theorem cell21_1842624_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 3, 4, 4].length) (baseStart_1842624 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1842624 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1842624 prefixEnd_1842624 := by exact prefixLift 1842624
  have htrace : WordTrace (prefixWord ++ tailWord_1842624) baseStart_1842624 baseEnd_1842624 := by
    simpa [prefixWord, tailWord_1842624, baseEnd_1842624] using wordTrace_append hprefix tailTrace_1842624
  have hstable : (prefixWord ++ tailWord_1842624).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1842624).length < 2 ^ (prefixWord ++ tailWord_1842624).sum := by decide
  have hdescent : baseEnd_1842624 < baseStart_1842624 := by decide
  rcases family_descends (prefixWord ++ tailWord_1842624) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1842627 : List Nat := [1, 1, 1, 3, 1, 1, 8, 2, 3]
def baseStart_1842627 : Nat := 118140960795 + 1842627 * 2 ^ 59
def prefixEnd_1842627 : Nat := 4983230072969 + 3 ^ 40 * 1842627 * 2
def baseEnd_1842627 : Nat := 420512585756563309817075

theorem tailTrace_1842627 : CollatzResearch.WordTrace tailWord_1842627 prefixEnd_1842627 420512585756563309817075 := by
  unfold tailWord_1842627
  simp only [CollatzResearch.WordTrace]
  refine ⟨67206127895484549482510135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44804085263656366321673423 67206127895484549482510135)
  ·
    refine ⟨100809191843226824223765203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67206127895484549482510135 100809191843226824223765203)
    ·
      refine ⟨151213787764840236335647805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100809191843226824223765203 151213787764840236335647805)
      ·
        refine ⟨56705170411815088625867927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 151213787764840236335647805 56705170411815088625867927)
        ·
          refine ⟨85057755617722632938801891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56705170411815088625867927 85057755617722632938801891)
          ·
            refine ⟨127586633426583949408202837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 85057755617722632938801891 127586633426583949408202837)
            ·
              refine ⟨1495155860467780657127377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 127586633426583949408202837 1495155860467780657127377)
              ·
                refine ⟨1121366895350835492845533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1495155860467780657127377 1121366895350835492845533)
                ·
                  refine ⟨420512585756563309817075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1121366895350835492845533 420512585756563309817075)
                  ·
                    rfl

theorem cell21_1842627_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 8, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 8, 2, 3].length) (baseStart_1842627 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1842627 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1842627 prefixEnd_1842627 := by exact prefixLift 1842627
  have htrace : WordTrace (prefixWord ++ tailWord_1842627) baseStart_1842627 baseEnd_1842627 := by
    simpa [prefixWord, tailWord_1842627, baseEnd_1842627] using wordTrace_append hprefix tailTrace_1842627
  have hstable : (prefixWord ++ tailWord_1842627).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1842627).length < 2 ^ (prefixWord ++ tailWord_1842627).sum := by decide
  have hdescent : baseEnd_1842627 < baseStart_1842627 := by decide
  rcases family_descends (prefixWord ++ tailWord_1842627) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1842655 : List Nat := [1, 1, 2, 3, 3, 1, 5, 5]
def baseStart_1842655 : Nat := 118140960795 + 1842655 * 2 ^ 59
def prefixEnd_1842655 : Nat := 4983230072969 + 3 ^ 40 * 1842655 * 2
def baseEnd_1842655 : Nat := 140172991912680494450117

theorem tailTrace_1842655 : CollatzResearch.WordTrace tailWord_1842655 prefixEnd_1842655 140172991912680494450117 := by
  unfold tailWord_1842655
  simp only [CollatzResearch.WordTrace]
  refine ⟨67207149139383110264529419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44804766092922073509686279 67207149139383110264529419)
  ·
    refine ⟨100810723709074665396794129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67207149139383110264529419 100810723709074665396794129)
    ·
      refine ⟨75608042781805999047595597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 100810723709074665396794129 75608042781805999047595597)
      ·
        refine ⟨28353016043177249642848349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 75608042781805999047595597 28353016043177249642848349)
        ·
          refine ⟨10632381016191468616068131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28353016043177249642848349 10632381016191468616068131)
          ·
            refine ⟨15948571524287202924102197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10632381016191468616068131 15948571524287202924102197)
            ·
              refine ⟨1495178580401925274134581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 15948571524287202924102197 1495178580401925274134581)
              ·
                refine ⟨140172991912680494450117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1495178580401925274134581 140172991912680494450117)
                ·
                  rfl

theorem cell21_1842655_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 5, 5].length) (baseStart_1842655 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1842655 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1842655 prefixEnd_1842655 := by exact prefixLift 1842655
  have htrace : WordTrace (prefixWord ++ tailWord_1842655) baseStart_1842655 baseEnd_1842655 := by
    simpa [prefixWord, tailWord_1842655, baseEnd_1842655] using wordTrace_append hprefix tailTrace_1842655
  have hstable : (prefixWord ++ tailWord_1842655).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1842655).length < 2 ^ (prefixWord ++ tailWord_1842655).sum := by decide
  have hdescent : baseEnd_1842655 < baseStart_1842655 := by decide
  rcases family_descends (prefixWord ++ tailWord_1842655) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1842683 : List Nat := [1, 1, 1, 1, 1, 3, 2, 5, 6]
def baseStart_1842683 : Nat := 118140960795 + 1842683 * 2 ^ 59
def prefixEnd_1842683 : Nat := 4983230072969 + 3 ^ 40 * 1842683 * 2
def baseEnd_1842683 : Nat := 420525365719519656883627

theorem tailTrace_1842683 : CollatzResearch.WordTrace tailWord_1842683 prefixEnd_1842683 420525365719519656883627 := by
  unfold tailWord_1842683
  simp only [CollatzResearch.WordTrace]
  refine ⟨67208170383281671046548703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44805446922187780697699135 67208170383281671046548703)
  ·
    refine ⟨100812255574922506569823055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67208170383281671046548703 100812255574922506569823055)
    ·
      refine ⟨151218383362383759854734583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100812255574922506569823055 151218383362383759854734583)
      ·
        refine ⟨226827575043575639782101875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 151218383362383759854734583 226827575043575639782101875)
        ·
          refine ⟨340241362565363459673152813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 226827575043575639782101875 340241362565363459673152813)
          ·
            refine ⟨127590510962011297377432305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 340241362565363459673152813 127590510962011297377432305)
            ·
              refine ⟨95692883221508473033074229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 127590510962011297377432305 95692883221508473033074229)
              ·
                refine ⟨8971207802016419346850709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 95692883221508473033074229 8971207802016419346850709)
                ·
                  refine ⟨420525365719519656883627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8971207802016419346850709 420525365719519656883627)
                  ·
                    rfl

theorem cell21_1842683_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 2, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 2, 5, 6].length) (baseStart_1842683 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1842683 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1842683 prefixEnd_1842683 := by exact prefixLift 1842683
  have htrace : WordTrace (prefixWord ++ tailWord_1842683) baseStart_1842683 baseEnd_1842683 := by
    simpa [prefixWord, tailWord_1842683, baseEnd_1842683] using wordTrace_append hprefix tailTrace_1842683
  have hstable : (prefixWord ++ tailWord_1842683).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1842683).length < 2 ^ (prefixWord ++ tailWord_1842683).sum := by decide
  have hdescent : baseEnd_1842683 < baseStart_1842683 := by decide
  rcases family_descends (prefixWord ++ tailWord_1842683) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1842720 : List Nat := [2, 1, 1, 6, 1, 3, 1, 3, 3]
def baseStart_1842720 : Nat := 118140960795 + 1842720 * 2 ^ 59
def prefixEnd_1842720 : Nat := 4983230072969 + 3 ^ 40 * 1842720 * 2
def baseEnd_1842720 : Nat := 420533809623615814766885

theorem tailTrace_1842720 : CollatzResearch.WordTrace tailWord_1842720 prefixEnd_1842720 420533809623615814766885 := by
  unfold tailWord_1842720
  simp only [CollatzResearch.WordTrace]
  refine ⟨33604759942073813182822807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44806346589431750910430409 33604759942073813182822807)
  ·
    refine ⟨50407139913110719774234211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33604759942073813182822807 50407139913110719774234211)
    ·
      refine ⟨75610709869666079661351317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50407139913110719774234211 75610709869666079661351317)
      ·
        refine ⟨3544252025140597484125843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 75610709869666079661351317 3544252025140597484125843)
        ·
          refine ⟨5316378037710896226188765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3544252025140597484125843 5316378037710896226188765)
          ·
            refine ⟨1993641764141586084820787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5316378037710896226188765 1993641764141586084820787)
            ·
              refine ⟨2990462646212379127231181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1993641764141586084820787 2990462646212379127231181)
              ·
                refine ⟨1121423492329642172711693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2990462646212379127231181 1121423492329642172711693)
                ·
                  refine ⟨420533809623615814766885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1121423492329642172711693 420533809623615814766885)
                  ·
                    rfl

theorem cell21_1842720_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 3, 1, 3, 3].length) (baseStart_1842720 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1842720 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1842720 prefixEnd_1842720 := by exact prefixLift 1842720
  have htrace : WordTrace (prefixWord ++ tailWord_1842720) baseStart_1842720 baseEnd_1842720 := by
    simpa [prefixWord, tailWord_1842720, baseEnd_1842720] using wordTrace_append hprefix tailTrace_1842720
  have hstable : (prefixWord ++ tailWord_1842720).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1842720).length < 2 ^ (prefixWord ++ tailWord_1842720).sum := by decide
  have hdescent : baseEnd_1842720 < baseStart_1842720 := by decide
  rcases family_descends (prefixWord ++ tailWord_1842720) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1842821 : List Nat := [1, 3, 1, 1, 4, 1, 3, 2, 5]
def baseStart_1842821 : Nat := 118140960795 + 1842821 * 2 ^ 59
def prefixEnd_1842821 : Nat := 4983230072969 + 3 ^ 40 * 1842821 * 2
def baseEnd_1842821 : Nat := 420556859199662083583345

theorem tailTrace_1842821 : CollatzResearch.WordTrace tailWord_1842821 prefixEnd_1842821 420556859199662083583345 := by
  unfold tailWord_1842821
  simp only [CollatzResearch.WordTrace]
  refine ⟨67213203656781720615072317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44808802437854480410048211 67213203656781720615072317)
  ·
    refine ⟨25204951371293145230652119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 67213203656781720615072317 25204951371293145230652119)
    ·
      refine ⟨37807427056939717845978179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25204951371293145230652119 37807427056939717845978179)
      ·
        refine ⟨56711140585409576768967269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37807427056939717845978179 56711140585409576768967269)
        ·
          refine ⟨10633338859764295644181363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 56711140585409576768967269 10633338859764295644181363)
          ·
            refine ⟨15950008289646443466272045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10633338859764295644181363 15950008289646443466272045)
            ·
              refine ⟨5981253108617416299852017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15950008289646443466272045 5981253108617416299852017)
              ·
                refine ⟨4485939831463062224889013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5981253108617416299852017 4485939831463062224889013)
                ·
                  refine ⟨420556859199662083583345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4485939831463062224889013 420556859199662083583345)
                  ·
                    rfl

theorem cell21_1842821_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 3, 2, 5].length) (baseStart_1842821 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1842821 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1842821 prefixEnd_1842821 := by exact prefixLift 1842821
  have htrace : WordTrace (prefixWord ++ tailWord_1842821) baseStart_1842821 baseEnd_1842821 := by
    simpa [prefixWord, tailWord_1842821, baseEnd_1842821] using wordTrace_append hprefix tailTrace_1842821
  have hstable : (prefixWord ++ tailWord_1842821).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1842821).length < 2 ^ (prefixWord ++ tailWord_1842821).sum := by decide
  have hdescent : baseEnd_1842821 < baseStart_1842821 := by decide
  rcases family_descends (prefixWord ++ tailWord_1842821) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1842852 : List Nat := [2, 3, 1, 2, 2, 3, 1, 1, 6]
def baseStart_1842852 : Nat := 118140960795 + 1842852 * 2 ^ 59
def prefixEnd_1842852 : Nat := 4983230072969 + 3 ^ 40 * 1842852 * 2
def baseEnd_1842852 : Nat := 420563933822012918566615

theorem tailTrace_1842852 : CollatzResearch.WordTrace tailWord_1842852 prefixEnd_1842852 420563933822012918566615 := by
  unfold tailWord_1842852
  simp only [CollatzResearch.WordTrace]
  refine ⟨33607167159834706454725405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44809556213112941939633873 33607167159834706454725405)
  ·
    refine ⟨12602687684938014920522027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 33607167159834706454725405 12602687684938014920522027)
    ·
      refine ⟨18904031527407022380783041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12602687684938014920522027 18904031527407022380783041)
      ·
        refine ⟨14178023645555266785587281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18904031527407022380783041 14178023645555266785587281)
        ·
          refine ⟨10633517734166450089190461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14178023645555266785587281 10633517734166450089190461)
          ·
            refine ⟨3987569150312418783446423, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10633517734166450089190461 3987569150312418783446423)
            ·
              refine ⟨5981353725468628175169635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3987569150312418783446423 5981353725468628175169635)
              ·
                refine ⟨8972030588202942262754453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5981353725468628175169635 8972030588202942262754453)
                ·
                  refine ⟨420563933822012918566615, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8972030588202942262754453 420563933822012918566615)
                  ·
                    rfl

theorem cell21_1842852_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 3, 1, 1, 6].length) (baseStart_1842852 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1842852 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1842852 prefixEnd_1842852 := by exact prefixLift 1842852
  have htrace : WordTrace (prefixWord ++ tailWord_1842852) baseStart_1842852 baseEnd_1842852 := by
    simpa [prefixWord, tailWord_1842852, baseEnd_1842852] using wordTrace_append hprefix tailTrace_1842852
  have hstable : (prefixWord ++ tailWord_1842852).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1842852).length < 2 ^ (prefixWord ++ tailWord_1842852).sum := by decide
  have hdescent : baseEnd_1842852 < baseStart_1842852 := by decide
  rcases family_descends (prefixWord ++ tailWord_1842852) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1842886 : List Nat := [6, 1, 2, 1, 1, 1, 1, 2, 6]
def baseStart_1842886 : Nat := 118140960795 + 1842886 * 2 ^ 59
def prefixEnd_1842886 : Nat := 4983230072969 + 3 ^ 40 * 1842886 * 2
def baseEnd_1842886 : Nat := 420571693085236414999879

theorem tailTrace_1842886 : CollatzResearch.WordTrace tailWord_1842886 prefixEnd_1842886 420571693085236414999879 := by
  unfold tailWord_1842886
  simp only [CollatzResearch.WordTrace]
  refine ⟨2100486700048319897380891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 44810382934364157810792341 2100486700048319897380891)
  ·
    refine ⟨3150730050072479846071337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2100486700048319897380891 3150730050072479846071337)
    ·
      refine ⟨2363047537554359884553503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3150730050072479846071337 2363047537554359884553503)
      ·
        refine ⟨3544571306331539826830255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2363047537554359884553503 3544571306331539826830255)
        ·
          refine ⟨5316856959497309740245383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3544571306331539826830255 5316856959497309740245383)
          ·
            refine ⟨7975285439245964610368075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5316856959497309740245383 7975285439245964610368075)
            ·
              refine ⟨11962928158868946915552113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7975285439245964610368075 11962928158868946915552113)
              ·
                refine ⟨8972196119151710186664085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11962928158868946915552113 8972196119151710186664085)
                ·
                  refine ⟨420571693085236414999879, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8972196119151710186664085 420571693085236414999879)
                  ·
                    rfl

theorem cell21_1842886_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 1, 1, 2, 6].length) (baseStart_1842886 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1842886 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1842886 prefixEnd_1842886 := by exact prefixLift 1842886
  have htrace : WordTrace (prefixWord ++ tailWord_1842886) baseStart_1842886 baseEnd_1842886 := by
    simpa [prefixWord, tailWord_1842886, baseEnd_1842886] using wordTrace_append hprefix tailTrace_1842886
  have hstable : (prefixWord ++ tailWord_1842886).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1842886).length < 2 ^ (prefixWord ++ tailWord_1842886).sum := by decide
  have hdescent : baseEnd_1842886 < baseStart_1842886 := by decide
  rcases family_descends (prefixWord ++ tailWord_1842886) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1842911 : List Nat := [1, 1, 2, 3, 2, 2, 1, 3, 6]
def baseStart_1842911 : Nat := 118140960795 + 1842911 * 2 ^ 59
def prefixEnd_1842911 : Nat := 4983230072969 + 3 ^ 40 * 1842911 * 2
def baseEnd_1842911 : Nat := 420577398425841927083161

theorem tailTrace_1842911 : CollatzResearch.WordTrace tailWord_1842911 prefixEnd_1842911 420577398425841927083161 := by
  unfold tailWord_1842911
  simp only [CollatzResearch.WordTrace]
  refine ⟨67216486226455665985848587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44810990817637110657232391 67216486226455665985848587)
  ·
    refine ⟨100824729339683498978772881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67216486226455665985848587 100824729339683498978772881)
    ·
      refine ⟨75618547004762624234079661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 100824729339683498978772881 75618547004762624234079661)
      ·
        refine ⟨28356955126785984087779873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 75618547004762624234079661 28356955126785984087779873)
        ·
          refine ⟨21267716345089488065834905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28356955126785984087779873 21267716345089488065834905)
          ·
            refine ⟨15950787258817116049376179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21267716345089488065834905 15950787258817116049376179)
            ·
              refine ⟨23926180888225674074064269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15950787258817116049376179 23926180888225674074064269)
              ·
                refine ⟨8972317833084627777774101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23926180888225674074064269 8972317833084627777774101)
                ·
                  refine ⟨420577398425841927083161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8972317833084627777774101 420577398425841927083161)
                  ·
                    rfl

theorem cell21_1842911_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 1, 3, 6].length) (baseStart_1842911 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1842911 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1842911 prefixEnd_1842911 := by exact prefixLift 1842911
  have htrace : WordTrace (prefixWord ++ tailWord_1842911) baseStart_1842911 baseEnd_1842911 := by
    simpa [prefixWord, tailWord_1842911, baseEnd_1842911] using wordTrace_append hprefix tailTrace_1842911
  have hstable : (prefixWord ++ tailWord_1842911).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1842911).length < 2 ^ (prefixWord ++ tailWord_1842911).sum := by decide
  have hdescent : baseEnd_1842911 < baseStart_1842911 := by decide
  rcases family_descends (prefixWord ++ tailWord_1842911) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1842962 : List Nat := [3, 2, 4, 1, 1, 2, 2, 2, 4]
def baseStart_1842962 : Nat := 118140960795 + 1842962 * 2 ^ 59
def prefixEnd_1842962 : Nat := 4983230072969 + 3 ^ 40 * 1842962 * 2
def baseEnd_1842962 : Nat := 420589037320677171733057

theorem tailTrace_1842962 : CollatzResearch.WordTrace tailWord_1842962 prefixEnd_1842962 420589037320677171733057 := by
  unfold tailWord_1842962
  simp only [CollatzResearch.WordTrace]
  refine ⟨16804586587317725423988785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 44812230899513934463970093 16804586587317725423988785)
  ·
    refine ⟨12603439940488294067991589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16804586587317725423988785 12603439940488294067991589)
    ·
      refine ⟨2363144988841555137748423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 12603439940488294067991589 2363144988841555137748423)
      ·
        refine ⟨3544717483262332706622635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2363144988841555137748423 3544717483262332706622635)
        ·
          refine ⟨5317076224893499059933953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3544717483262332706622635 5317076224893499059933953)
          ·
            refine ⟨3987807168670124294950465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5317076224893499059933953 3987807168670124294950465)
            ·
              refine ⟨2990855376502593221212849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3987807168670124294950465 2990855376502593221212849)
              ·
                refine ⟨2243141532376944915909637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2990855376502593221212849 2243141532376944915909637)
                ·
                  refine ⟨420589037320677171733057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2243141532376944915909637 420589037320677171733057)
                  ·
                    rfl

theorem cell21_1842962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 2, 2, 2, 4].length) (baseStart_1842962 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1842962 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1842962 prefixEnd_1842962 := by exact prefixLift 1842962
  have htrace : WordTrace (prefixWord ++ tailWord_1842962) baseStart_1842962 baseEnd_1842962 := by
    simpa [prefixWord, tailWord_1842962, baseEnd_1842962] using wordTrace_append hprefix tailTrace_1842962
  have hstable : (prefixWord ++ tailWord_1842962).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1842962).length < 2 ^ (prefixWord ++ tailWord_1842962).sum := by decide
  have hdescent : baseEnd_1842962 < baseStart_1842962 := by decide
  rcases family_descends (prefixWord ++ tailWord_1842962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1843007 : List Nat := [1, 1, 2, 2, 6, 1, 2, 3, 3]
def baseStart_1843007 : Nat := 118140960795 + 1843007 * 2 ^ 59
def prefixEnd_1843007 : Nat := 4983230072969 + 3 ^ 40 * 1843007 * 2
def baseEnd_1843007 : Nat := 420599306933767093482965

theorem tailTrace_1843007 : CollatzResearch.WordTrace tailWord_1843007 prefixEnd_1843007 420599306933767093482965 := by
  unfold tailWord_1843007
  simp only [CollatzResearch.WordTrace]
  refine ⟨67219987634107874381343275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44813325089405249587562183 67219987634107874381343275)
  ·
    refine ⟨100829981451161811572014913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67219987634107874381343275 100829981451161811572014913)
    ·
      refine ⟨75622486088371358679011185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 100829981451161811572014913 75622486088371358679011185)
      ·
        refine ⟨56716864566278519009258389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 75622486088371358679011185 56716864566278519009258389)
        ·
          refine ⟨2658603026544305578558987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 56716864566278519009258389 2658603026544305578558987)
          ·
            refine ⟨3987904539816458367838481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2658603026544305578558987 3987904539816458367838481)
            ·
              refine ⟨2990928404862343775878861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3987904539816458367838481 2990928404862343775878861)
              ·
                refine ⟨1121598151823378915954573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2990928404862343775878861 1121598151823378915954573)
                ·
                  refine ⟨420599306933767093482965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1121598151823378915954573 420599306933767093482965)
                  ·
                    rfl

theorem cell21_1843007_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 6, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 6, 1, 2, 3, 3].length) (baseStart_1843007 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1843007 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1843007 prefixEnd_1843007 := by exact prefixLift 1843007
  have htrace : WordTrace (prefixWord ++ tailWord_1843007) baseStart_1843007 baseEnd_1843007 := by
    simpa [prefixWord, tailWord_1843007, baseEnd_1843007] using wordTrace_append hprefix tailTrace_1843007
  have hstable : (prefixWord ++ tailWord_1843007).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1843007).length < 2 ^ (prefixWord ++ tailWord_1843007).sum := by decide
  have hdescent : baseEnd_1843007 < baseStart_1843007 := by decide
  rcases family_descends (prefixWord ++ tailWord_1843007) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1843021 : List Nat := [1, 6, 1, 2, 1, 2, 1, 1, 6]
def baseStart_1843021 : Nat := 118140960795 + 1843021 * 2 ^ 59
def prefixEnd_1843021 : Nat := 4983230072969 + 3 ^ 40 * 1843021 * 2
def baseEnd_1843021 : Nat := 420602501924506180249603

theorem tailTrace_1843021 : CollatzResearch.WordTrace tailWord_1843021 prefixEnd_1843021 420602501924506180249603 := by
  unfold tailWord_1843021
  simp only [CollatzResearch.WordTrace]
  refine ⟨67220498256057154772352917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44813665504038103181568611 67220498256057154772352917)
  ·
    refine ⟨3150960855752679129954043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 67220498256057154772352917 3150960855752679129954043)
    ·
      refine ⟨4726441283629018694931065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3150960855752679129954043 4726441283629018694931065)
      ·
        refine ⟨3544830962721764021198299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4726441283629018694931065 3544830962721764021198299)
        ·
          refine ⟨5317246444082646031797449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3544830962721764021198299 5317246444082646031797449)
          ·
            refine ⟨3987934833061984523848087, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5317246444082646031797449 3987934833061984523848087)
            ·
              refine ⟨5981902249592976785772131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3987934833061984523848087 5981902249592976785772131)
              ·
                refine ⟨8972853374389465178658197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5981902249592976785772131 8972853374389465178658197)
                ·
                  refine ⟨420602501924506180249603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8972853374389465178658197 420602501924506180249603)
                  ·
                    rfl

theorem cell21_1843021_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 2, 1, 1, 6].length) (baseStart_1843021 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1843021 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1843021 prefixEnd_1843021 := by exact prefixLift 1843021
  have htrace : WordTrace (prefixWord ++ tailWord_1843021) baseStart_1843021 baseEnd_1843021 := by
    simpa [prefixWord, tailWord_1843021, baseEnd_1843021] using wordTrace_append hprefix tailTrace_1843021
  have hstable : (prefixWord ++ tailWord_1843021).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1843021).length < 2 ^ (prefixWord ++ tailWord_1843021).sum := by decide
  have hdescent : baseEnd_1843021 < baseStart_1843021 := by decide
  rcases family_descends (prefixWord ++ tailWord_1843021) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1843066 : List Nat := [3, 1, 1, 1, 1, 1, 7, 3, 3]
def baseStart_1843066 : Nat := 118140960795 + 1843066 * 2 ^ 59
def prefixEnd_1843066 : Nat := 4983230072969 + 3 ^ 40 * 1843066 * 2
def baseEnd_1843066 : Nat := 420612771537596101999511

theorem tailTrace_1843066 : CollatzResearch.WordTrace tailWord_1843066 prefixEnd_1843066 420612771537596101999511 := by
  unfold tailWord_1843066
  simp only [CollatzResearch.WordTrace]
  refine ⟨16805534885223531864435263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 44814759693929418305160701 16805534885223531864435263)
  ·
    refine ⟨25208302327835297796652895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16805534885223531864435263 25208302327835297796652895)
    ·
      refine ⟨37812453491752946694979343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25208302327835297796652895 37812453491752946694979343)
      ·
        refine ⟨56718680237629420042469015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37812453491752946694979343 56718680237629420042469015)
        ·
          refine ⟨85078020356444130063703523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56718680237629420042469015 85078020356444130063703523)
          ·
            refine ⟨127617030534666195095555285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 85078020356444130063703523 127617030534666195095555285)
            ·
              refine ⟨2991024153156238947552077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 127617030534666195095555285 2991024153156238947552077)
              ·
                refine ⟨1121634057433589605332029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2991024153156238947552077 1121634057433589605332029)
                ·
                  refine ⟨420612771537596101999511, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1121634057433589605332029 420612771537596101999511)
                  ·
                    rfl

theorem cell21_1843066_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 7, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 7, 3, 3].length) (baseStart_1843066 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1843066 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1843066 prefixEnd_1843066 := by exact prefixLift 1843066
  have htrace : WordTrace (prefixWord ++ tailWord_1843066) baseStart_1843066 baseEnd_1843066 := by
    simpa [prefixWord, tailWord_1843066, baseEnd_1843066] using wordTrace_append hprefix tailTrace_1843066
  have hstable : (prefixWord ++ tailWord_1843066).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1843066).length < 2 ^ (prefixWord ++ tailWord_1843066).sum := by decide
  have hdescent : baseEnd_1843066 < baseStart_1843066 := by decide
  rcases family_descends (prefixWord ++ tailWord_1843066) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1843153 : List Nat := [1, 2, 2, 1, 2, 1, 2, 10]
def baseStart_1843153 : Nat := 118140960795 + 1843153 * 2 ^ 59
def prefixEnd_1843153 : Nat := 4983230072969 + 3 ^ 40 * 1843153 * 2
def baseEnd_1843153 : Nat := 140210875374301094683111

theorem tailTrace_1843153 : CollatzResearch.WordTrace tailWord_1843153 prefixEnd_1843153 140210875374301094683111 := by
  unfold tailWord_1843153
  simp only [CollatzResearch.WordTrace]
  refine ⟨67225312691578941316158113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44816875127719294210772075 67225312691578941316158113)
  ·
    refine ⟨50418984518684205987118585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67225312691578941316158113 50418984518684205987118585)
    ·
      refine ⟨37814238389013154490338939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50418984518684205987118585 37814238389013154490338939)
      ·
        refine ⟨56721357583519731735508409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37814238389013154490338939 56721357583519731735508409)
        ·
          refine ⟨42541018187639798801631307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56721357583519731735508409 42541018187639798801631307)
          ·
            refine ⟨63811527281459698202446961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42541018187639798801631307 63811527281459698202446961)
            ·
              refine ⟨47858645461094773651835221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 63811527281459698202446961 47858645461094773651835221)
              ·
                refine ⟨140210875374301094683111, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 47858645461094773651835221 140210875374301094683111)
                ·
                  rfl

theorem cell21_1843153_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 2, 10].length) (baseStart_1843153 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1843153 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1843153 prefixEnd_1843153 := by exact prefixLift 1843153
  have htrace : WordTrace (prefixWord ++ tailWord_1843153) baseStart_1843153 baseEnd_1843153 := by
    simpa [prefixWord, tailWord_1843153, baseEnd_1843153] using wordTrace_append hprefix tailTrace_1843153
  have hstable : (prefixWord ++ tailWord_1843153).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1843153).length < 2 ^ (prefixWord ++ tailWord_1843153).sum := by decide
  have hdescent : baseEnd_1843153 < baseStart_1843153 := by decide
  rcases family_descends (prefixWord ++ tailWord_1843153) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1843156 : List Nat := [2, 4, 1, 2, 1, 1, 1, 5, 4]
def baseStart_1843156 : Nat := 118140960795 + 1843156 * 2 ^ 59
def prefixEnd_1843156 : Nat := 4983230072969 + 3 ^ 40 * 1843156 * 2
def baseEnd_1843156 : Nat := 420633310763775945499327

theorem tailTrace_1843156 : CollatzResearch.WordTrace tailWord_1843156 prefixEnd_1843156 420633310763775945499327 := by
  unfold tailWord_1843156
  simp only [CollatzResearch.WordTrace]
  refine ⟨33612711055284036414258661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44816948073712048552344881 33612711055284036414258661)
  ·
    refine ⟨6302383322865756827673499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 33612711055284036414258661 6302383322865756827673499)
    ·
      refine ⟨9453574984298635241510249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6302383322865756827673499 9453574984298635241510249)
      ·
        refine ⟨7090181238223976431132687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9453574984298635241510249 7090181238223976431132687)
        ·
          refine ⟨10635271857335964646699031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7090181238223976431132687 10635271857335964646699031)
          ·
            refine ⟨15952907786003946970048547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10635271857335964646699031 15952907786003946970048547)
            ·
              refine ⟨23929361679005920455072821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15952907786003946970048547 23929361679005920455072821)
              ·
                refine ⟨2243377657406805042663077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 23929361679005920455072821 2243377657406805042663077)
                ·
                  refine ⟨420633310763775945499327, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2243377657406805042663077 420633310763775945499327)
                  ·
                    rfl

theorem cell21_1843156_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 1, 5, 4].length) (baseStart_1843156 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1843156 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1843156 prefixEnd_1843156 := by exact prefixLift 1843156
  have htrace : WordTrace (prefixWord ++ tailWord_1843156) baseStart_1843156 baseEnd_1843156 := by
    simpa [prefixWord, tailWord_1843156, baseEnd_1843156] using wordTrace_append hprefix tailTrace_1843156
  have hstable : (prefixWord ++ tailWord_1843156).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1843156).length < 2 ^ (prefixWord ++ tailWord_1843156).sum := by decide
  have hdescent : baseEnd_1843156 < baseStart_1843156 := by decide
  rcases family_descends (prefixWord ++ tailWord_1843156) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1843190 : List Nat := [5, 1, 1, 1, 4, 2, 1, 2, 4]
def baseStart_1843190 : Nat := 118140960795 + 1843190 * 2 ^ 59
def prefixEnd_1843190 : Nat := 4983230072969 + 3 ^ 40 * 1843190 * 2
def baseEnd_1843190 : Nat := 420641070026999441932591

theorem tailTrace_1843190 : CollatzResearch.WordTrace tailWord_1843190 prefixEnd_1843190 420641070026999441932591 := by
  unfold tailWord_1843190
  simp only [CollatzResearch.WordTrace]
  refine ⟨4201666387027806039703439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 44817774794963264423503349 4201666387027806039703439)
  ·
    refine ⟨6302499580541709059555159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4201666387027806039703439 6302499580541709059555159)
    ·
      refine ⟨9453749370812563589332739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6302499580541709059555159 9453749370812563589332739)
      ·
        refine ⟨14180624056218845383999109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9453749370812563589332739 14180624056218845383999109)
        ·
          refine ⟨2658867010541033509499833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 14180624056218845383999109 2658867010541033509499833)
          ·
            refine ⟨1994150257905775132124875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2658867010541033509499833 1994150257905775132124875)
            ·
              refine ⟨2991225386858662698187313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1994150257905775132124875 2991225386858662698187313)
              ·
                refine ⟨2243419040143997023640485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2991225386858662698187313 2243419040143997023640485)
                ·
                  refine ⟨420641070026999441932591, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2243419040143997023640485 420641070026999441932591)
                  ·
                    rfl

theorem cell21_1843190_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 4, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 4, 2, 1, 2, 4].length) (baseStart_1843190 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1843190 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1843190 prefixEnd_1843190 := by exact prefixLift 1843190
  have htrace : WordTrace (prefixWord ++ tailWord_1843190) baseStart_1843190 baseEnd_1843190 := by
    simpa [prefixWord, tailWord_1843190, baseEnd_1843190] using wordTrace_append hprefix tailTrace_1843190
  have hstable : (prefixWord ++ tailWord_1843190).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1843190).length < 2 ^ (prefixWord ++ tailWord_1843190).sum := by decide
  have hdescent : baseEnd_1843190 < baseStart_1843190 := by decide
  rcases family_descends (prefixWord ++ tailWord_1843190) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1843201 : List Nat := [1, 2, 4, 1, 2, 1, 4, 1, 5]
def baseStart_1843201 : Nat := 118140960795 + 1843201 * 2 ^ 59
def prefixEnd_1843201 : Nat := 4983230072969 + 3 ^ 40 * 1843201 * 2
def baseEnd_1843201 : Nat := 420643580376865867249235

theorem tailTrace_1843201 : CollatzResearch.WordTrace tailWord_1843201 prefixEnd_1843201 420643580376865867249235 := by
  unfold tailWord_1843201
  simp only [CollatzResearch.WordTrace]
  refine ⟨67227063395405045513905457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44818042263603363675936971 67227063395405045513905457)
  ·
    refine ⟨50420297546553784135429093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67227063395405045513905457 50420297546553784135429093)
    ·
      refine ⟨9453805789978834525392955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 50420297546553784135429093 9453805789978834525392955)
      ·
        refine ⟨14180708684968251788089433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9453805789978834525392955 14180708684968251788089433)
        ·
          refine ⟨10635531513726188841067075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14180708684968251788089433 10635531513726188841067075)
          ·
            refine ⟨15953297270589283261600613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10635531513726188841067075 15953297270589283261600613)
            ·
              refine ⟨2991243238235490611550115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15953297270589283261600613 2991243238235490611550115)
              ·
                refine ⟨4486864857353235917325173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2991243238235490611550115 4486864857353235917325173)
                ·
                  refine ⟨420643580376865867249235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4486864857353235917325173 420643580376865867249235)
                  ·
                    rfl

theorem cell21_1843201_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 4, 1, 5].length) (baseStart_1843201 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1843201 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1843201 prefixEnd_1843201 := by exact prefixLift 1843201
  have htrace : WordTrace (prefixWord ++ tailWord_1843201) baseStart_1843201 baseEnd_1843201 := by
    simpa [prefixWord, tailWord_1843201, baseEnd_1843201] using wordTrace_append hprefix tailTrace_1843201
  have hstable : (prefixWord ++ tailWord_1843201).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1843201).length < 2 ^ (prefixWord ++ tailWord_1843201).sum := by decide
  have hdescent : baseEnd_1843201 < baseStart_1843201 := by decide
  rcases family_descends (prefixWord ++ tailWord_1843201) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1843246 : List Nat := [4, 1, 3, 1, 1, 2, 9]
def baseStart_1843246 : Nat := 118140960795 + 1843246 * 2 ^ 59
def prefixEnd_1843246 : Nat := 4983230072969 + 3 ^ 40 * 1843246 * 2
def baseEnd_1843246 : Nat := 46739316665550643222127

theorem tailTrace_1843246 : CollatzResearch.WordTrace tailWord_1843246 prefixEnd_1843246 46739316665550643222127 := by
  unfold tailWord_1843246
  simp only [CollatzResearch.WordTrace]
  refine ⟨8403588085030252274911699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 44819136453494678799529061 8403588085030252274911699)
  ·
    refine ⟨12605382127545378412367549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8403588085030252274911699 12605382127545378412367549)
    ·
      refine ⟨4727018297829516904637831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12605382127545378412367549 4727018297829516904637831)
      ·
        refine ⟨7090527446744275356956747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4727018297829516904637831 7090527446744275356956747)
        ·
          refine ⟨10635791170116413035435121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7090527446744275356956747 10635791170116413035435121)
          ·
            refine ⟨7976843377587309776576341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10635791170116413035435121 7976843377587309776576341)
            ·
              refine ⟨46739316665550643222127, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 7976843377587309776576341 46739316665550643222127)
              ·
                rfl

theorem cell21_1843246_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 2, 9].length) (baseStart_1843246 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1843246 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1843246 prefixEnd_1843246 := by exact prefixLift 1843246
  have htrace : WordTrace (prefixWord ++ tailWord_1843246) baseStart_1843246 baseEnd_1843246 := by
    simpa [prefixWord, tailWord_1843246, baseEnd_1843246] using wordTrace_append hprefix tailTrace_1843246
  have hstable : (prefixWord ++ tailWord_1843246).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1843246).length < 2 ^ (prefixWord ++ tailWord_1843246).sum := by decide
  have hdescent : baseEnd_1843246 < baseStart_1843246 := by decide
  rcases family_descends (prefixWord ++ tailWord_1843246) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1843252 : List Nat := [2, 5, 1, 2, 3, 1, 1, 1, 5]
def baseStart_1843252 : Nat := 118140960795 + 1843252 * 2 ^ 59
def prefixEnd_1843252 : Nat := 4983230072969 + 3 ^ 40 * 1843252 * 2
def baseEnd_1843252 : Nat := 420655219271701111899131

theorem tailTrace_1843252 : CollatzResearch.WordTrace tailWord_1843252 prefixEnd_1843252 420655219271701111899131 := by
  unfold tailWord_1843252
  simp only [CollatzResearch.WordTrace]
  refine ⟨33614461759110140612006005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44819282345480187482674673 33614461759110140612006005)
  ·
    refine ⟨3151355789916575682375563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 33614461759110140612006005 3151355789916575682375563)
    ·
      refine ⟨4727033684874863523563345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3151355789916575682375563 4727033684874863523563345)
      ·
        refine ⟨3545275263656147642672509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4727033684874863523563345 3545275263656147642672509)
        ·
          refine ⟨1329478223871055366002191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3545275263656147642672509 1329478223871055366002191)
          ·
            refine ⟨1994217335806583049003287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1329478223871055366002191 1994217335806583049003287)
            ·
              refine ⟨2991326003709874573504931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1994217335806583049003287 2991326003709874573504931)
              ·
                refine ⟨4486989005564811860257397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2991326003709874573504931 4486989005564811860257397)
                ·
                  refine ⟨420655219271701111899131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4486989005564811860257397 420655219271701111899131)
                  ·
                    rfl

theorem cell21_1843252_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 3, 1, 1, 1, 5].length) (baseStart_1843252 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1843252 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1843252 prefixEnd_1843252 := by exact prefixLift 1843252
  have htrace : WordTrace (prefixWord ++ tailWord_1843252) baseStart_1843252 baseEnd_1843252 := by
    simpa [prefixWord, tailWord_1843252, baseEnd_1843252] using wordTrace_append hprefix tailTrace_1843252
  have hstable : (prefixWord ++ tailWord_1843252).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1843252).length < 2 ^ (prefixWord ++ tailWord_1843252).sum := by decide
  have hdescent : baseEnd_1843252 < baseStart_1843252 := by decide
  rcases family_descends (prefixWord ++ tailWord_1843252) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1843277 : List Nat := [1, 6, 1, 1, 1, 1, 2, 1, 7]
def baseStart_1843277 : Nat := 118140960795 + 1843277 * 2 ^ 59
def prefixEnd_1843277 : Nat := 4983230072969 + 3 ^ 40 * 1843277 * 2
def baseEnd_1843277 : Nat := 420660924612306623982413

theorem tailTrace_1843277 : CollatzResearch.WordTrace tailWord_1843277 prefixEnd_1843277 420660924612306623982413 := by
  unfold tailWord_1843277
  simp only [CollatzResearch.WordTrace]
  refine ⟨67229835343129710493672085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44819890228753140329114723 67229835343129710493672085)
  ·
    refine ⟨3151398531709205179390879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 67229835343129710493672085 3151398531709205179390879)
    ·
      refine ⟨4727097797563807769086319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3151398531709205179390879 4727097797563807769086319)
      ·
        refine ⟨7090646696345711653629479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4727097797563807769086319 7090646696345711653629479)
        ·
          refine ⟨10635970044518567480444219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7090646696345711653629479 10635970044518567480444219)
          ·
            refine ⟨15953955066777851220666329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10635970044518567480444219 15953955066777851220666329)
            ·
              refine ⟨11965466300083388415499747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15953955066777851220666329 11965466300083388415499747)
              ·
                refine ⟨17948199450125082623249621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11965466300083388415499747 17948199450125082623249621)
                ·
                  refine ⟨420660924612306623982413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 17948199450125082623249621 420660924612306623982413)
                  ·
                    rfl

theorem cell21_1843277_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 2, 1, 7].length) (baseStart_1843277 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1843277 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1843277 prefixEnd_1843277 := by exact prefixLift 1843277
  have htrace : WordTrace (prefixWord ++ tailWord_1843277) baseStart_1843277 baseEnd_1843277 := by
    simpa [prefixWord, tailWord_1843277, baseEnd_1843277] using wordTrace_append hprefix tailTrace_1843277
  have hstable : (prefixWord ++ tailWord_1843277).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1843277).length < 2 ^ (prefixWord ++ tailWord_1843277).sum := by decide
  have hdescent : baseEnd_1843277 < baseStart_1843277 := by decide
  rcases family_descends (prefixWord ++ tailWord_1843277) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1843308 : List Nat := [2, 2, 1, 1, 3, 4, 2, 2, 4]
def baseStart_1843308 : Nat := 118140960795 + 1843308 * 2 ^ 59
def prefixEnd_1843308 : Nat := 4983230072969 + 3 ^ 40 * 1843308 * 2
def baseEnd_1843308 : Nat := 420667999234657458965683

theorem tailTrace_1843308 : CollatzResearch.WordTrace tailWord_1843308 prefixEnd_1843308 420667999234657458965683 := by
  unfold tailWord_1843308
  simp only [CollatzResearch.WordTrace]
  refine ⟨33615483003008701394025289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44820644004011601858700385 33615483003008701394025289)
  ·
    refine ⟨25211612252256526045518967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33615483003008701394025289 25211612252256526045518967)
    ·
      refine ⟨37817418378384789068278451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25211612252256526045518967 37817418378384789068278451)
      ·
        refine ⟨56726127567577183602417677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37817418378384789068278451 56726127567577183602417677)
        ·
          refine ⟨21272297837841443850906629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 56726127567577183602417677 21272297837841443850906629)
          ·
            refine ⟨3988555844595270722044993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 21272297837841443850906629 3988555844595270722044993)
            ·
              refine ⟨2991416883446453041533745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3988555844595270722044993 2991416883446453041533745)
              ·
                refine ⟨2243562662584839781150309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2991416883446453041533745 2243562662584839781150309)
                ·
                  refine ⟨420667999234657458965683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2243562662584839781150309 420667999234657458965683)
                  ·
                    rfl

theorem cell21_1843308_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 4, 2, 2, 4].length) (baseStart_1843308 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1843308 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1843308 prefixEnd_1843308 := by exact prefixLift 1843308
  have htrace : WordTrace (prefixWord ++ tailWord_1843308) baseStart_1843308 baseEnd_1843308 := by
    simpa [prefixWord, tailWord_1843308, baseEnd_1843308] using wordTrace_append hprefix tailTrace_1843308
  have hstable : (prefixWord ++ tailWord_1843308).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1843308).length < 2 ^ (prefixWord ++ tailWord_1843308).sum := by decide
  have hdescent : baseEnd_1843308 < baseStart_1843308 := by decide
  rcases family_descends (prefixWord ++ tailWord_1843308) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1843311 : List Nat := [1, 1, 2, 1, 3, 6, 2, 2, 3]
def baseStart_1843311 : Nat := 118140960795 + 1843311 * 2 ^ 59
def prefixEnd_1843311 : Nat := 4983230072969 + 3 ^ 40 * 1843311 * 2
def baseEnd_1843311 : Nat := 420668683875530120415677

theorem tailTrace_1843311 : CollatzResearch.WordTrace tailWord_1843311 prefixEnd_1843311 420668683875530120415677 := by
  unfold tailWord_1843311
  simp only [CollatzResearch.WordTrace]
  refine ⟨67231075425006534300409787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44820716950004356200273191 67231075425006534300409787)
  ·
    refine ⟨100846613137509801450614681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67231075425006534300409787 100846613137509801450614681)
    ·
      refine ⟨75634959853132351087961011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 100846613137509801450614681 75634959853132351087961011)
      ·
        refine ⟨113452439779698526631941517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75634959853132351087961011 113452439779698526631941517)
        ·
          refine ⟨42544664917386947486978069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 113452439779698526631941517 42544664917386947486978069)
          ·
            refine ⟨1994281168002513163452097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 42544664917386947486978069 1994281168002513163452097)
            ·
              refine ⟨1495710876001884872589073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1994281168002513163452097 1495710876001884872589073)
              ·
                refine ⟨1121783157001413654441805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1495710876001884872589073 1121783157001413654441805)
                ·
                  refine ⟨420668683875530120415677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1121783157001413654441805 420668683875530120415677)
                  ·
                    rfl

theorem cell21_1843311_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 6, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 6, 2, 2, 3].length) (baseStart_1843311 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1843311 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1843311 prefixEnd_1843311 := by exact prefixLift 1843311
  have htrace : WordTrace (prefixWord ++ tailWord_1843311) baseStart_1843311 baseEnd_1843311 := by
    simpa [prefixWord, tailWord_1843311, baseEnd_1843311] using wordTrace_append hprefix tailTrace_1843311
  have hstable : (prefixWord ++ tailWord_1843311).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1843311).length < 2 ^ (prefixWord ++ tailWord_1843311).sum := by decide
  have hdescent : baseEnd_1843311 < baseStart_1843311 := by decide
  rcases family_descends (prefixWord ++ tailWord_1843311) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1843384 : List Nat := [2, 1, 2, 1, 2, 1, 7, 1, 4]
def baseStart_1843384 : Nat := 118140960795 + 1843384 * 2 ^ 59
def prefixEnd_1843384 : Nat := 4983230072969 + 3 ^ 40 * 1843384 * 2
def baseEnd_1843384 : Nat := 420685343470098215698861

theorem tailTrace_1843384 : CollatzResearch.WordTrace tailWord_1843384 prefixEnd_1843384 420685343470098215698861 := by
  unfold tailWord_1843384
  simp only [CollatzResearch.WordTrace]
  refine ⟨33616868976871033883908603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44822491969161378511878137 33616868976871033883908603)
  ·
    refine ⟨50425303465306550825862905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33616868976871033883908603 50425303465306550825862905)
    ·
      refine ⟨37818977598979913119397179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50425303465306550825862905 37818977598979913119397179)
      ·
        refine ⟨56728466398469869679095769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37818977598979913119397179 56728466398469869679095769)
        ·
          refine ⟨42546349798852402259321827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56728466398469869679095769 42546349798852402259321827)
          ·
            refine ⟨63819524698278603388982741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42546349798852402259321827 63819524698278603388982741)
            ·
              refine ⟨1495770110115904766929283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 63819524698278603388982741 1495770110115904766929283)
              ·
                refine ⟨2243655165173857150393925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1495770110115904766929283 2243655165173857150393925)
                ·
                  refine ⟨420685343470098215698861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2243655165173857150393925 420685343470098215698861)
                  ·
                    rfl

theorem cell21_1843384_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 7, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 7, 1, 4].length) (baseStart_1843384 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1843384 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1843384 prefixEnd_1843384 := by exact prefixLift 1843384
  have htrace : WordTrace (prefixWord ++ tailWord_1843384) baseStart_1843384 baseEnd_1843384 := by
    simpa [prefixWord, tailWord_1843384, baseEnd_1843384] using wordTrace_append hprefix tailTrace_1843384
  have hstable : (prefixWord ++ tailWord_1843384).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1843384).length < 2 ^ (prefixWord ++ tailWord_1843384).sum := by decide
  have hdescent : baseEnd_1843384 < baseStart_1843384 := by decide
  rcases family_descends (prefixWord ++ tailWord_1843384) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1843404 : List Nat := [2, 2, 1, 6, 1, 2, 1, 3, 3]
def baseStart_1843404 : Nat := 118140960795 + 1843404 * 2 ^ 59
def prefixEnd_1843404 : Nat := 4983230072969 + 3 ^ 40 * 1843404 * 2
def baseEnd_1843404 : Nat := 420689907742582625365487

theorem tailTrace_1843404 : CollatzResearch.WordTrace tailWord_1843404 prefixEnd_1843404 420689907742582625365487 := by
  unfold tailWord_1843404
  simp only [CollatzResearch.WordTrace]
  refine ⟨33617233706834805591772633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44822978275779740789030177 33617233706834805591772633)
  ·
    refine ⟨25212925280126104193829475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33617233706834805591772633 25212925280126104193829475)
    ·
      refine ⟨37819387920189156290744213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25212925280126104193829475 37819387920189156290744213)
      ·
        refine ⟨1772783808758866701128635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 37819387920189156290744213 1772783808758866701128635)
        ·
          refine ⟨2659175713138300051692953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1772783808758866701128635 2659175713138300051692953)
          ·
            refine ⟨1994381784853725038769715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2659175713138300051692953 1994381784853725038769715)
            ·
              refine ⟨2991572677280587558154573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1994381784853725038769715 2991572677280587558154573)
              ·
                refine ⟨1121839753980220334307965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2991572677280587558154573 1121839753980220334307965)
                ·
                  refine ⟨420689907742582625365487, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1121839753980220334307965 420689907742582625365487)
                  ·
                    rfl

theorem cell21_1843404_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 6, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 6, 1, 2, 1, 3, 3].length) (baseStart_1843404 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1843404 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1843404 prefixEnd_1843404 := by exact prefixLift 1843404
  have htrace : WordTrace (prefixWord ++ tailWord_1843404) baseStart_1843404 baseEnd_1843404 := by
    simpa [prefixWord, tailWord_1843404, baseEnd_1843404] using wordTrace_append hprefix tailTrace_1843404
  have hstable : (prefixWord ++ tailWord_1843404).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1843404).length < 2 ^ (prefixWord ++ tailWord_1843404).sum := by decide
  have hdescent : baseEnd_1843404 < baseStart_1843404 := by decide
  rcases family_descends (prefixWord ++ tailWord_1843404) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1843429 : List Nat := [1, 3, 1, 4, 2, 1, 3, 1, 5]
def baseStart_1843429 : Nat := 118140960795 + 1843429 * 2 ^ 59
def prefixEnd_1843429 : Nat := 4983230072969 + 3 ^ 40 * 1843429 * 2
def baseEnd_1843429 : Nat := 420695613083188137448769

theorem tailTrace_1843429 : CollatzResearch.WordTrace tailWord_1843429 prefixEnd_1843429 420695613083188137448769 := by
  unfold tailWord_1843429
  simp only [CollatzResearch.WordTrace]
  refine ⟨67235379238579040453205341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44823586159052693635470227 67235379238579040453205341)
  ·
    refine ⟨25213267214467140169952003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 67235379238579040453205341 25213267214467140169952003)
    ·
      refine ⟨37819900821700710254928005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25213267214467140169952003 37819900821700710254928005)
      ·
        refine ⟨7091231404068883172799001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 37819900821700710254928005 7091231404068883172799001)
        ·
          refine ⟨5318423553051662379599251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7091231404068883172799001 5318423553051662379599251)
          ·
            refine ⟨7977635329577493569398877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5318423553051662379599251 7977635329577493569398877)
            ·
              refine ⟨2991613248591560088524579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7977635329577493569398877 2991613248591560088524579)
              ·
                refine ⟨4487419872887340132786869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2991613248591560088524579 4487419872887340132786869)
                ·
                  refine ⟨420695613083188137448769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4487419872887340132786869 420695613083188137448769)
                  ·
                    rfl

theorem cell21_1843429_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 1, 3, 1, 5].length) (baseStart_1843429 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1843429 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1843429 prefixEnd_1843429 := by exact prefixLift 1843429
  have htrace : WordTrace (prefixWord ++ tailWord_1843429) baseStart_1843429 baseEnd_1843429 := by
    simpa [prefixWord, tailWord_1843429, baseEnd_1843429] using wordTrace_append hprefix tailTrace_1843429
  have hstable : (prefixWord ++ tailWord_1843429).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1843429).length < 2 ^ (prefixWord ++ tailWord_1843429).sum := by decide
  have hdescent : baseEnd_1843429 < baseStart_1843429 := by decide
  rcases family_descends (prefixWord ++ tailWord_1843429) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1843443 : List Nat := [1, 1, 1, 2, 2, 4, 3, 3, 4]
def baseStart_1843443 : Nat := 118140960795 + 1843443 * 2 ^ 59
def prefixEnd_1843443 : Nat := 4983230072969 + 3 ^ 40 * 1843443 * 2
def baseEnd_1843443 : Nat := 420698808073927224215407

theorem tailTrace_1843443 : CollatzResearch.WordTrace tailWord_1843443 prefixEnd_1843443 420698808073927224215407 := by
  unfold tailWord_1843443
  simp only [CollatzResearch.WordTrace]
  refine ⟨67235889860528320844214983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44823926573685547229476655 67235889860528320844214983)
  ·
    refine ⟨100853834790792481266322475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67235889860528320844214983 100853834790792481266322475)
    ·
      refine ⟨151280752186188721899483713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100853834790792481266322475 151280752186188721899483713)
      ·
        refine ⟨113460564139641541424612785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 151280752186188721899483713 113460564139641541424612785)
        ·
          refine ⟨85095423104731156068459589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 113460564139641541424612785 85095423104731156068459589)
          ·
            refine ⟨15955391832137091762836173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 85095423104731156068459589 15955391832137091762836173)
            ·
              refine ⟨5983271937051409411063565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15955391832137091762836173 5983271937051409411063565)
              ·
                refine ⟨2243726976394278529148837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5983271937051409411063565 2243726976394278529148837)
                ·
                  refine ⟨420698808073927224215407, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2243726976394278529148837 420698808073927224215407)
                  ·
                    rfl

theorem cell21_1843443_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 3, 3, 4].length) (baseStart_1843443 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1843443 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1843443 prefixEnd_1843443 := by exact prefixLift 1843443
  have htrace : WordTrace (prefixWord ++ tailWord_1843443) baseStart_1843443 baseEnd_1843443 := by
    simpa [prefixWord, tailWord_1843443, baseEnd_1843443] using wordTrace_append hprefix tailTrace_1843443
  have hstable : (prefixWord ++ tailWord_1843443).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1843443).length < 2 ^ (prefixWord ++ tailWord_1843443).sum := by decide
  have hdescent : baseEnd_1843443 < baseStart_1843443 := by decide
  rcases family_descends (prefixWord ++ tailWord_1843443) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1843457 : List Nat := [1, 2, 4, 1, 1, 2, 1, 9]
def baseStart_1843457 : Nat := 118140960795 + 1843457 * 2 ^ 59
def prefixEnd_1843457 : Nat := 4983230072969 + 3 ^ 40 * 1843457 * 2
def baseEnd_1843457 : Nat := 140234001021555436994015

theorem tailTrace_1843457 : CollatzResearch.WordTrace tailWord_1843457 prefixEnd_1843457 140234001021555436994015 := by
  unfold tailWord_1843457
  simp only [CollatzResearch.WordTrace]
  refine ⟨67236400482477601235224625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44824266988318400823483083 67236400482477601235224625)
  ·
    refine ⟨50427300361858200926418469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67236400482477601235224625 50427300361858200926418469)
    ·
      refine ⟨9455118817848412673703463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 50427300361858200926418469 9455118817848412673703463)
      ·
        refine ⟨14182678226772619010555195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9455118817848412673703463 14182678226772619010555195)
        ·
          refine ⟨21274017340158928515832793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14182678226772619010555195 21274017340158928515832793)
          ·
            refine ⟨15955513005119196386874595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21274017340158928515832793 15955513005119196386874595)
            ·
              refine ⟨23933269507678794580311893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15955513005119196386874595 23933269507678794580311893)
              ·
                refine ⟨140234001021555436994015, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 23933269507678794580311893 140234001021555436994015)
                ·
                  rfl

theorem cell21_1843457_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 1, 9].length) (baseStart_1843457 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1843457 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1843457 prefixEnd_1843457 := by exact prefixLift 1843457
  have htrace : WordTrace (prefixWord ++ tailWord_1843457) baseStart_1843457 baseEnd_1843457 := by
    simpa [prefixWord, tailWord_1843457, baseEnd_1843457] using wordTrace_append hprefix tailTrace_1843457
  have hstable : (prefixWord ++ tailWord_1843457).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1843457).length < 2 ^ (prefixWord ++ tailWord_1843457).sum := by decide
  have hdescent : baseEnd_1843457 < baseStart_1843457 := by decide
  rcases family_descends (prefixWord ++ tailWord_1843457) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1843505 : List Nat := [1, 2, 2, 3, 4, 1, 1, 2, 5]
def baseStart_1843505 : Nat := 118140960795 + 1843505 * 2 ^ 59
def prefixEnd_1843505 : Nat := 4983230072969 + 3 ^ 40 * 1843505 * 2
def baseEnd_1843505 : Nat := 420712957318628894181947

theorem tailTrace_1843505 : CollatzResearch.WordTrace tailWord_1843505 prefixEnd_1843505 420712957318628894181947 := by
  unfold tailWord_1843505
  simp only [CollatzResearch.WordTrace]
  refine ⟨67238151186303705432971969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44825434124202470288647979 67238151186303705432971969)
  ·
    refine ⟨50428613389727779074728977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67238151186303705432971969 50428613389727779074728977)
    ·
      refine ⟨37821460042295834306046733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50428613389727779074728977 37821460042295834306046733)
      ·
        refine ⟨14183047515860937864767525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 37821460042295834306046733 14183047515860937864767525)
        ·
          refine ⟨2659321409223925849643911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 14183047515860937864767525 2659321409223925849643911)
          ·
            refine ⟨3988982113835888774465867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2659321409223925849643911 3988982113835888774465867)
            ·
              refine ⟨5983473170753833161698801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3988982113835888774465867 5983473170753833161698801)
              ·
                refine ⟨4487604878065374871274101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5983473170753833161698801 4487604878065374871274101)
                ·
                  refine ⟨420712957318628894181947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4487604878065374871274101 420712957318628894181947)
                  ·
                    rfl

theorem cell21_1843505_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 4, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 4, 1, 1, 2, 5].length) (baseStart_1843505 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1843505 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1843505 prefixEnd_1843505 := by exact prefixLift 1843505
  have htrace : WordTrace (prefixWord ++ tailWord_1843505) baseStart_1843505 baseEnd_1843505 := by
    simpa [prefixWord, tailWord_1843505, baseEnd_1843505] using wordTrace_append hprefix tailTrace_1843505
  have hstable : (prefixWord ++ tailWord_1843505).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1843505).length < 2 ^ (prefixWord ++ tailWord_1843505).sum := by decide
  have hdescent : baseEnd_1843505 < baseStart_1843505 := by decide
  rcases family_descends (prefixWord ++ tailWord_1843505) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1843536 : List Nat := [2, 1, 1, 1, 1, 8, 1, 2, 4]
def baseStart_1843536 : Nat := 118140960795 + 1843536 * 2 ^ 59
def prefixEnd_1843536 : Nat := 4983230072969 + 3 ^ 40 * 1843536 * 2
def baseEnd_1843536 : Nat := 420720031940979729165217

theorem tailTrace_1843536 : CollatzResearch.WordTrace tailWord_1843536 prefixEnd_1843536 420720031940979729165217 := by
  unfold tailWord_1843536
  simp only [CollatzResearch.WordTrace]
  refine ⟨33619640924595698863675231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44826187899460931818233641 33619640924595698863675231)
  ·
    refine ⟨50429461386893548295512847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33619640924595698863675231 50429461386893548295512847)
    ·
      refine ⟨75644192080340322443269271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50429461386893548295512847 75644192080340322443269271)
      ·
        refine ⟨113466288120510483664903907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75644192080340322443269271 113466288120510483664903907)
        ·
          refine ⟨170199432180765725497355861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 113466288120510483664903907 170199432180765725497355861)
          ·
            refine ⟨1994524595868348345672139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 170199432180765725497355861 1994524595868348345672139)
            ·
              refine ⟨2991786893802522518508209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1994524595868348345672139 2991786893802522518508209)
              ·
                refine ⟨2243840170351891888881157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2991786893802522518508209 2243840170351891888881157)
                ·
                  refine ⟨420720031940979729165217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2243840170351891888881157 420720031940979729165217)
                  ·
                    rfl

theorem cell21_1843536_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 8, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 8, 1, 2, 4].length) (baseStart_1843536 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1843536 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1843536 prefixEnd_1843536 := by exact prefixLift 1843536
  have htrace : WordTrace (prefixWord ++ tailWord_1843536) baseStart_1843536 baseEnd_1843536 := by
    simpa [prefixWord, tailWord_1843536, baseEnd_1843536] using wordTrace_append hprefix tailTrace_1843536
  have hstable : (prefixWord ++ tailWord_1843536).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1843536).length < 2 ^ (prefixWord ++ tailWord_1843536).sum := by decide
  have hdescent : baseEnd_1843536 < baseStart_1843536 := by decide
  rcases family_descends (prefixWord ++ tailWord_1843536) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1843598 : List Nat := [4, 1, 1, 4, 1, 3, 1, 1, 5]
def baseStart_1843598 : Nat := 118140960795 + 1843598 * 2 ^ 59
def prefixEnd_1843598 : Nat := 4983230072969 + 3 ^ 40 * 1843598 * 2
def baseEnd_1843598 : Nat := 420734181185681399131757

theorem tailTrace_1843598 : CollatzResearch.WordTrace tailWord_1843598 prefixEnd_1843598 420734181185681399131757 := by
  unfold tailWord_1843598
  simp only [CollatzResearch.WordTrace]
  refine ⟨8405192896870847789513431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 44827695449977854877404965 8405192896870847789513431)
  ·
    refine ⟨12607789345306271684270147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8405192896870847789513431 12607789345306271684270147)
    ·
      refine ⟨18911684017959407526405221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12607789345306271684270147 18911684017959407526405221)
      ·
        refine ⟨3545940753367388911200979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 18911684017959407526405221 3545940753367388911200979)
        ·
          refine ⟨5318911130051083366801469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3545940753367388911200979 5318911130051083366801469)
          ·
            refine ⟨1994591673769156262550551, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5318911130051083366801469 1994591673769156262550551)
            ·
              refine ⟨2991887510653734393825827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1994591673769156262550551 2991887510653734393825827)
              ·
                refine ⟨4487831265980601590738741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2991887510653734393825827 4487831265980601590738741)
                ·
                  refine ⟨420734181185681399131757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4487831265980601590738741 420734181185681399131757)
                  ·
                    rfl

theorem cell21_1843598_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 3, 1, 1, 5].length) (baseStart_1843598 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1843598 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1843598 prefixEnd_1843598 := by exact prefixLift 1843598
  have htrace : WordTrace (prefixWord ++ tailWord_1843598) baseStart_1843598 baseEnd_1843598 := by
    simpa [prefixWord, tailWord_1843598, baseEnd_1843598] using wordTrace_append hprefix tailTrace_1843598
  have hstable : (prefixWord ++ tailWord_1843598).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1843598).length < 2 ^ (prefixWord ++ tailWord_1843598).sum := by decide
  have hdescent : baseEnd_1843598 < baseStart_1843598 := by decide
  rcases family_descends (prefixWord ++ tailWord_1843598) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1843609 : List Nat := [1, 2, 1, 2, 1, 4, 4, 6]
def baseStart_1843609 : Nat := 118140960795 + 1843609 * 2 ^ 59
def prefixEnd_1843609 : Nat := 4983230072969 + 3 ^ 40 * 1843609 * 2
def baseEnd_1843609 : Nat := 140245563845182608149467

theorem tailTrace_1843609 : CollatzResearch.WordTrace tailWord_1843609 prefixEnd_1843609 140245563845182608149467 := by
  unfold tailWord_1843609
  simp only [CollatzResearch.WordTrace]
  refine ⟨67241944377926931194757881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44827962918617954129838587 67241944377926931194757881)
  ·
    refine ⟨50431458283445198396068411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67241944377926931194757881 50431458283445198396068411)
    ·
      refine ⟨75647187425167797594102617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50431458283445198396068411 75647187425167797594102617)
      ·
        refine ⟨56735390568875848195576963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 75647187425167797594102617 56735390568875848195576963)
        ·
          refine ⟨85103085853313772293365445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56735390568875848195576963 85103085853313772293365445)
          ·
            refine ⟨15956828597496332305006021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 85103085853313772293365445 15956828597496332305006021)
            ·
              refine ⟨2991905362030562307188629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15956828597496332305006021 2991905362030562307188629)
              ·
                refine ⟨140245563845182608149467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2991905362030562307188629 140245563845182608149467)
                ·
                  rfl

theorem cell21_1843609_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 4, 6].length) (baseStart_1843609 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1843609 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1843609 prefixEnd_1843609 := by exact prefixLift 1843609
  have htrace : WordTrace (prefixWord ++ tailWord_1843609) baseStart_1843609 baseEnd_1843609 := by
    simpa [prefixWord, tailWord_1843609, baseEnd_1843609] using wordTrace_append hprefix tailTrace_1843609
  have hstable : (prefixWord ++ tailWord_1843609).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1843609).length < 2 ^ (prefixWord ++ tailWord_1843609).sum := by decide
  have hdescent : baseEnd_1843609 < baseStart_1843609 := by decide
  rcases family_descends (prefixWord ++ tailWord_1843609) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1843699 : List Nat := [1, 1, 1, 2, 2, 2, 3, 2, 7]
def baseStart_1843699 : Nat := 118140960795 + 1843699 * 2 ^ 59
def prefixEnd_1843699 : Nat := 4983230072969 + 3 ^ 40 * 1843699 * 2
def baseEnd_1843699 : Nat := 420757230761727667948217

theorem tailTrace_1843699 : CollatzResearch.WordTrace tailWord_1843699 prefixEnd_1843699 420757230761727667948217 := by
  unfold tailWord_1843699
  simp only [CollatzResearch.WordTrace]
  refine ⟨67245226947600876565534151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44830151298400584377022767 67245226947600876565534151)
  ·
    refine ⟨100867840421401314848301227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67245226947600876565534151 100867840421401314848301227)
    ·
      refine ⟨151301760632101972272451841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100867840421401314848301227 151301760632101972272451841)
      ·
        refine ⟨113476320474076479204338881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 151301760632101972272451841 113476320474076479204338881)
        ·
          refine ⟨85107240355557359403254161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 113476320474076479204338881 85107240355557359403254161)
          ·
            refine ⟨63830430266668019552440621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 85107240355557359403254161 63830430266668019552440621)
            ·
              refine ⟨23936411350000507332165233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 63830430266668019552440621 23936411350000507332165233)
              ·
                refine ⟨17952308512500380499123925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23936411350000507332165233 17952308512500380499123925)
                ·
                  refine ⟨420757230761727667948217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 17952308512500380499123925 420757230761727667948217)
                  ·
                    rfl

theorem cell21_1843699_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 3, 2, 7].length) (baseStart_1843699 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1843699 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1843699 prefixEnd_1843699 := by exact prefixLift 1843699
  have htrace : WordTrace (prefixWord ++ tailWord_1843699) baseStart_1843699 baseEnd_1843699 := by
    simpa [prefixWord, tailWord_1843699, baseEnd_1843699] using wordTrace_append hprefix tailTrace_1843699
  have hstable : (prefixWord ++ tailWord_1843699).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1843699).length < 2 ^ (prefixWord ++ tailWord_1843699).sum := by decide
  have hdescent : baseEnd_1843699 < baseStart_1843699 := by decide
  rcases family_descends (prefixWord ++ tailWord_1843699) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1843826 : List Nat := [3, 2, 1, 2, 4, 1, 1, 4, 3]
def baseStart_1843826 : Nat := 118140960795 + 1843826 * 2 ^ 59
def prefixEnd_1843826 : Nat := 4983230072969 + 3 ^ 40 * 1843826 * 2
def baseEnd_1843826 : Nat := 420786213892003669331291

theorem tailTrace_1843826 : CollatzResearch.WordTrace tailWord_1843826 prefixEnd_1843826 420786213892003669331291 := by
  unfold tailWord_1843826
  simp only [CollatzResearch.WordTrace]
  refine ⟨16812464754535194313851833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 44833239345427184836938221 16812464754535194313851833)
  ·
    refine ⟨12609348565901395735388875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16812464754535194313851833 12609348565901395735388875)
    ·
      refine ⟨18914022848852093603083313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12609348565901395735388875 18914022848852093603083313)
      ·
        refine ⟨14185517136639070202312485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18914022848852093603083313 14185517136639070202312485)
        ·
          refine ⟨2659784463119825662933591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 14185517136639070202312485 2659784463119825662933591)
          ·
            refine ⟨3989676694679738494400387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2659784463119825662933591 3989676694679738494400387)
            ·
              refine ⟨5984515042019607741600581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3989676694679738494400387 5984515042019607741600581)
              ·
                refine ⟨1122096570378676451550109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5984515042019607741600581 1122096570378676451550109)
                ·
                  refine ⟨420786213892003669331291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1122096570378676451550109 420786213892003669331291)
                  ·
                    rfl

theorem cell21_1843826_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 4, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 4, 1, 1, 4, 3].length) (baseStart_1843826 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1843826 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1843826 prefixEnd_1843826 := by exact prefixLift 1843826
  have htrace : WordTrace (prefixWord ++ tailWord_1843826) baseStart_1843826 baseEnd_1843826 := by
    simpa [prefixWord, tailWord_1843826, baseEnd_1843826] using wordTrace_append hprefix tailTrace_1843826
  have hstable : (prefixWord ++ tailWord_1843826).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1843826).length < 2 ^ (prefixWord ++ tailWord_1843826).sum := by decide
  have hdescent : baseEnd_1843826 < baseStart_1843826 := by decide
  rcases family_descends (prefixWord ++ tailWord_1843826) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1843854 : List Nat := [4, 1, 1, 3, 1, 1, 5, 5]
def baseStart_1843854 : Nat := 118140960795 + 1843854 * 2 ^ 59
def prefixEnd_1843854 : Nat := 4983230072969 + 3 ^ 40 * 1843854 * 2
def baseEnd_1843854 : Nat := 140264201291160614288189

theorem tailTrace_1843854 : CollatzResearch.WordTrace tailWord_1843854 prefixEnd_1843854 140264201291160614288189 := by
  unfold tailWord_1843854
  simp only [CollatzResearch.WordTrace]
  refine ⟨8406360032754917254678327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 44833920174692892024951077 8406360032754917254678327)
  ·
    refine ⟨12609540049132375882017491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8406360032754917254678327 12609540049132375882017491)
    ·
      refine ⟨18914310073698563823026237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12609540049132375882017491 18914310073698563823026237)
      ·
        refine ⟨7092866277636961433634839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18914310073698563823026237 7092866277636961433634839)
        ·
          refine ⟨10639299416455442150452259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7092866277636961433634839 10639299416455442150452259)
          ·
            refine ⟨15958949124683163225678389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10639299416455442150452259 15958949124683163225678389)
            ·
              refine ⟨1496151480439046552407349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 15958949124683163225678389 1496151480439046552407349)
              ·
                refine ⟨140264201291160614288189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1496151480439046552407349 140264201291160614288189)
                ·
                  rfl

theorem cell21_1843854_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 5, 5].length) (baseStart_1843854 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1843854 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1843854 prefixEnd_1843854 := by exact prefixLift 1843854
  have htrace : WordTrace (prefixWord ++ tailWord_1843854) baseStart_1843854 baseEnd_1843854 := by
    simpa [prefixWord, tailWord_1843854, baseEnd_1843854] using wordTrace_append hprefix tailTrace_1843854
  have hstable : (prefixWord ++ tailWord_1843854).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1843854).length < 2 ^ (prefixWord ++ tailWord_1843854).sum := by decide
  have hdescent : baseEnd_1843854 < baseStart_1843854 := by decide
  rcases family_descends (prefixWord ++ tailWord_1843854) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1843885 : List Nat := [1, 5, 2, 1, 1, 3, 2, 1, 5]
def baseStart_1843885 : Nat := 118140960795 + 1843885 * 2 ^ 59
def prefixEnd_1843885 : Nat := 4983230072969 + 3 ^ 40 * 1843885 * 2
def baseEnd_1843885 : Nat := 420799678495832677847837

theorem tailTrace_1843885 : CollatzResearch.WordTrace tailWord_1843885 prefixEnd_1843885 420799678495832677847837 := by
  unfold tailWord_1843885
  simp only [CollatzResearch.WordTrace]
  refine ⟨67252010924927030331805109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44834673949951353554536739 67252010924927030331805109)
  ·
    refine ⟨6304876024211909093606729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 67252010924927030331805109 6304876024211909093606729)
    ·
      refine ⟨4728657018158931820205047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6304876024211909093606729 4728657018158931820205047)
      ·
        refine ⟨7092985527238397730307571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4728657018158931820205047 7092985527238397730307571)
        ·
          refine ⟨10639478290857596595461357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7092985527238397730307571 10639478290857596595461357)
          ·
            refine ⟨3989804359071598723298009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10639478290857596595461357 3989804359071598723298009)
            ·
              refine ⟨2992353269303699042473507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3989804359071598723298009 2992353269303699042473507)
              ·
                refine ⟨4488529903955548563710261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2992353269303699042473507 4488529903955548563710261)
                ·
                  refine ⟨420799678495832677847837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4488529903955548563710261 420799678495832677847837)
                  ·
                    rfl

theorem cell21_1843885_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 3, 2, 1, 5].length) (baseStart_1843885 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1843885 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1843885 prefixEnd_1843885 := by exact prefixLift 1843885
  have htrace : WordTrace (prefixWord ++ tailWord_1843885) baseStart_1843885 baseEnd_1843885 := by
    simpa [prefixWord, tailWord_1843885, baseEnd_1843885] using wordTrace_append hprefix tailTrace_1843885
  have hstable : (prefixWord ++ tailWord_1843885).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1843885).length < 2 ^ (prefixWord ++ tailWord_1843885).sum := by decide
  have hdescent : baseEnd_1843885 < baseStart_1843885 := by decide
  rcases family_descends (prefixWord ++ tailWord_1843885) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1843905 : List Nat := [1, 2, 6, 2, 2, 1, 2, 5]
def baseStart_1843905 : Nat := 118140960795 + 1843905 * 2 ^ 59
def prefixEnd_1843905 : Nat := 4983230072969 + 3 ^ 40 * 1843905 * 2
def baseEnd_1843905 : Nat := 140268080922772362504821

theorem tailTrace_1843905 : CollatzResearch.WordTrace tailWord_1843905 prefixEnd_1843905 140268080922772362504821 := by
  unfold tailWord_1843905
  simp only [CollatzResearch.WordTrace]
  refine ⟨67252740384854573747533169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44835160256569715831688779 67252740384854573747533169)
  ·
    refine ⟨50439555288640930310649877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67252740384854573747533169 50439555288640930310649877)
    ·
      refine ⟨2364354154155043608311713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 50439555288640930310649877 2364354154155043608311713)
      ·
        refine ⟨1773265615616282706233785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2364354154155043608311713 1773265615616282706233785)
        ·
          refine ⟨1329949211712212029675339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1773265615616282706233785 1329949211712212029675339)
          ·
            refine ⟨1994923817568318044513009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1329949211712212029675339 1994923817568318044513009)
            ·
              refine ⟨1496192863176238533384757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1994923817568318044513009 1496192863176238533384757)
              ·
                refine ⟨140268080922772362504821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1496192863176238533384757 140268080922772362504821)
                ·
                  rfl

theorem cell21_1843905_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 2, 2, 1, 2, 5].length) (baseStart_1843905 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1843905 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1843905 prefixEnd_1843905 := by exact prefixLift 1843905
  have htrace : WordTrace (prefixWord ++ tailWord_1843905) baseStart_1843905 baseEnd_1843905 := by
    simpa [prefixWord, tailWord_1843905, baseEnd_1843905] using wordTrace_append hprefix tailTrace_1843905
  have hstable : (prefixWord ++ tailWord_1843905).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1843905).length < 2 ^ (prefixWord ++ tailWord_1843905).sum := by decide
  have hdescent : baseEnd_1843905 < baseStart_1843905 := by decide
  rcases family_descends (prefixWord ++ tailWord_1843905) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1844003 : List Nat := [1, 1, 1, 4, 2, 1, 1, 5, 5]
def baseStart_1844003 : Nat := 118140960795 + 1844003 * 2 ^ 59
def prefixEnd_1844003 : Nat := 4983230072969 + 3 ^ 40 * 1844003 * 2
def baseEnd_1844003 : Nat := 420826607703490694880929

theorem tailTrace_1844003 : CollatzResearch.WordTrace tailWord_1844003 prefixEnd_1844003 420826607703490694880929 := by
  unfold tailWord_1844003
  simp only [CollatzResearch.WordTrace]
  refine ⟨67256314738499536484600663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44837543158999690989733775 67256314738499536484600663)
  ·
    refine ⟨100884472107749304726900995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67256314738499536484600663 100884472107749304726900995)
    ·
      refine ⟨151326708161623957090351493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100884472107749304726900995 151326708161623957090351493)
      ·
        refine ⟨28373757780304491954440905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 151326708161623957090351493 28373757780304491954440905)
        ·
          refine ⟨21280318335228368965830679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28373757780304491954440905 21280318335228368965830679)
          ·
            refine ⟨31920477502842553448746019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21280318335228368965830679 31920477502842553448746019)
            ·
              refine ⟨47880716254263830173119029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31920477502842553448746019 47880716254263830173119029)
              ·
                refine ⟨4488817148837234078729909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 47880716254263830173119029 4488817148837234078729909)
                ·
                  refine ⟨420826607703490694880929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4488817148837234078729909 420826607703490694880929)
                  ·
                    rfl

theorem cell21_1844003_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 1, 5, 5].length) (baseStart_1844003 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1844003 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1844003 prefixEnd_1844003 := by exact prefixLift 1844003
  have htrace : WordTrace (prefixWord ++ tailWord_1844003) baseStart_1844003 baseEnd_1844003 := by
    simpa [prefixWord, tailWord_1844003, baseEnd_1844003] using wordTrace_append hprefix tailTrace_1844003
  have hstable : (prefixWord ++ tailWord_1844003).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1844003).length < 2 ^ (prefixWord ++ tailWord_1844003).sum := by decide
  have hdescent : baseEnd_1844003 < baseStart_1844003 := by decide
  rcases family_descends (prefixWord ++ tailWord_1844003) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1844068 : List Nat := [2, 3, 1, 1, 4, 2, 3, 1, 4]
def baseStart_1844068 : Nat := 118140960795 + 1844068 * 2 ^ 59
def prefixEnd_1844068 : Nat := 4983230072969 + 3 ^ 40 * 1844068 * 2
def baseEnd_1844068 : Nat := 420841441589065026297463

theorem tailTrace_1844068 : CollatzResearch.WordTrace tailWord_1844068 prefixEnd_1844068 420841441589065026297463 := by
  unfold tailWord_1844068
  simp only [CollatzResearch.WordTrace]
  refine ⟨33629342741632026292858429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44839123655509368390477905 33629342741632026292858429)
  ·
    refine ⟨12611003528112009859821911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 33629342741632026292858429 12611003528112009859821911)
    ·
      refine ⟨18916505292168014789732867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12611003528112009859821911 18916505292168014789732867)
      ·
        refine ⟨28374757938252022184599301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18916505292168014789732867 28374757938252022184599301)
        ·
          refine ⟨5320267113422254159612369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 28374757938252022184599301 5320267113422254159612369)
          ·
            refine ⟨3990200335066690619709277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5320267113422254159612369 3990200335066690619709277)
            ·
              refine ⟨1496325125650008982390979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3990200335066690619709277 1496325125650008982390979)
              ·
                refine ⟨2244487688475013473586469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1496325125650008982390979 2244487688475013473586469)
                ·
                  refine ⟨420841441589065026297463, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2244487688475013473586469 420841441589065026297463)
                  ·
                    rfl

theorem cell21_1844068_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 2, 3, 1, 4].length) (baseStart_1844068 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1844068 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1844068 prefixEnd_1844068 := by exact prefixLift 1844068
  have htrace : WordTrace (prefixWord ++ tailWord_1844068) baseStart_1844068 baseEnd_1844068 := by
    simpa [prefixWord, tailWord_1844068, baseEnd_1844068] using wordTrace_append hprefix tailTrace_1844068
  have hstable : (prefixWord ++ tailWord_1844068).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1844068).length < 2 ^ (prefixWord ++ tailWord_1844068).sum := by decide
  have hdescent : baseEnd_1844068 < baseStart_1844068 := by decide
  rcases family_descends (prefixWord ++ tailWord_1844068) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1844096 : List Nat := [2, 1, 1, 2, 1, 2, 2, 7, 3]
def baseStart_1844096 : Nat := 118140960795 + 1844096 * 2 ^ 59
def prefixEnd_1844096 : Nat := 4983230072969 + 3 ^ 40 * 1844096 * 2
def baseEnd_1844096 : Nat := 420847831570543199830739

theorem tailTrace_1844096 : CollatzResearch.WordTrace tailWord_1844096 prefixEnd_1844096 420847831570543199830739 := by
  unfold tailWord_1844096
  simp only [CollatzResearch.WordTrace]
  refine ⟨33629853363581306683868071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44839804484775075578490761 33629853363581306683868071)
  ·
    refine ⟨50444780045371960025802107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33629853363581306683868071 50444780045371960025802107)
    ·
      refine ⟨75667170068057940038703161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50444780045371960025802107 75667170068057940038703161)
      ·
        refine ⟨56750377551043455029027371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 75667170068057940038703161 56750377551043455029027371)
        ·
          refine ⟨85125566326565182543541057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56750377551043455029027371 85125566326565182543541057)
          ·
            refine ⟨63844174744923886907655793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 85125566326565182543541057 63844174744923886907655793)
            ·
              refine ⟨47883131058692915180741845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 63844174744923886907655793 47883131058692915180741845)
              ·
                refine ⟨1122260884188115199548637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 47883131058692915180741845 1122260884188115199548637)
                ·
                  refine ⟨420847831570543199830739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1122260884188115199548637 420847831570543199830739)
                  ·
                    rfl

theorem cell21_1844096_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 2, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 2, 7, 3].length) (baseStart_1844096 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1844096 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1844096 prefixEnd_1844096 := by exact prefixLift 1844096
  have htrace : WordTrace (prefixWord ++ tailWord_1844096) baseStart_1844096 baseEnd_1844096 := by
    simpa [prefixWord, tailWord_1844096, baseEnd_1844096] using wordTrace_append hprefix tailTrace_1844096
  have hstable : (prefixWord ++ tailWord_1844096).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1844096).length < 2 ^ (prefixWord ++ tailWord_1844096).sum := by decide
  have hdescent : baseEnd_1844096 < baseStart_1844096 := by decide
  rcases family_descends (prefixWord ++ tailWord_1844096) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1844127 : List Nat := [1, 1, 2, 5, 2, 2, 1, 3, 4]
def baseStart_1844127 : Nat := 118140960795 + 1844127 * 2 ^ 59
def prefixEnd_1844127 : Nat := 4983230072969 + 3 ^ 40 * 1844127 * 2
def baseEnd_1844127 : Nat := 420854906192894034814009

theorem tailTrace_1844127 : CollatzResearch.WordTrace tailWord_1844127 prefixEnd_1844127 420854906192894034814009 := by
  unfold tailWord_1844127
  simp only [CollatzResearch.WordTrace]
  refine ⟨67260837390050305662114635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44840558260033537108076423 67260837390050305662114635)
  ·
    refine ⟨100891256085075458493171953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67260837390050305662114635 100891256085075458493171953)
    ·
      refine ⟨75668442063806593869878965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 100891256085075458493171953 75668442063806593869878965)
      ·
        refine ⟨7093916443481868175301153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 75668442063806593869878965 7093916443481868175301153)
        ·
          refine ⟨5320437332611401131475865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7093916443481868175301153 5320437332611401131475865)
          ·
            refine ⟨3990327999458550848606899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5320437332611401131475865 3990327999458550848606899)
            ·
              refine ⟨5985491999187826272910349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3990327999458550848606899 5985491999187826272910349)
              ·
                refine ⟨2244559499695434852341381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5985491999187826272910349 2244559499695434852341381)
                ·
                  refine ⟨420854906192894034814009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2244559499695434852341381 420854906192894034814009)
                  ·
                    rfl

theorem cell21_1844127_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 2, 1, 3, 4].length) (baseStart_1844127 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1844127 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1844127 prefixEnd_1844127 := by exact prefixLift 1844127
  have htrace : WordTrace (prefixWord ++ tailWord_1844127) baseStart_1844127 baseEnd_1844127 := by
    simpa [prefixWord, tailWord_1844127, baseEnd_1844127] using wordTrace_append hprefix tailTrace_1844127
  have hstable : (prefixWord ++ tailWord_1844127).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1844127).length < 2 ^ (prefixWord ++ tailWord_1844127).sum := by decide
  have hdescent : baseEnd_1844127 < baseStart_1844127 := by decide
  rcases family_descends (prefixWord ++ tailWord_1844127) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1844164 : List Nat := [2, 3, 3, 3, 1, 2, 2, 2, 3]
def baseStart_1844164 : Nat := 118140960795 + 1844164 * 2 ^ 59
def prefixEnd_1844164 : Nat := 4983230072969 + 3 ^ 40 * 1844164 * 2
def baseEnd_1844164 : Nat := 420863350096990192697267

theorem tailTrace_1844164 : CollatzResearch.WordTrace tailWord_1844164 prefixEnd_1844164 420863350096990192697267 := by
  unfold tailWord_1844164
  simp only [CollatzResearch.WordTrace]
  refine ⟨33631093445458130490605773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44841457927277507320807697 33631093445458130490605773)
  ·
    refine ⟨12611660042046798933977165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 33631093445458130490605773 12611660042046798933977165)
    ·
      refine ⟨4729372515767549600241437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12611660042046798933977165 4729372515767549600241437)
      ·
        refine ⟨1773514693412831100090539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4729372515767549600241437 1773514693412831100090539)
        ·
          refine ⟨2660272040119246650135809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1773514693412831100090539 2660272040119246650135809)
          ·
            refine ⟨1995204030089434987601857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2660272040119246650135809 1995204030089434987601857)
            ·
              refine ⟨1496403022567076240701393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1995204030089434987601857 1496403022567076240701393)
              ·
                refine ⟨1122302266925307180526045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1496403022567076240701393 1122302266925307180526045)
                ·
                  refine ⟨420863350096990192697267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1122302266925307180526045 420863350096990192697267)
                  ·
                    rfl

theorem cell21_1844164_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 3, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 3, 1, 2, 2, 2, 3].length) (baseStart_1844164 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1844164 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1844164 prefixEnd_1844164 := by exact prefixLift 1844164
  have htrace : WordTrace (prefixWord ++ tailWord_1844164) baseStart_1844164 baseEnd_1844164 := by
    simpa [prefixWord, tailWord_1844164, baseEnd_1844164] using wordTrace_append hprefix tailTrace_1844164
  have hstable : (prefixWord ++ tailWord_1844164).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1844164).length < 2 ^ (prefixWord ++ tailWord_1844164).sum := by decide
  have hdescent : baseEnd_1844164 < baseStart_1844164 := by decide
  rcases family_descends (prefixWord ++ tailWord_1844164) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1844200 : List Nat := [2, 1, 4, 1, 1, 1, 2, 9]
def baseStart_1844200 : Nat := 118140960795 + 1844200 * 2 ^ 59
def prefixEnd_1844200 : Nat := 4983230072969 + 3 ^ 40 * 1844200 * 2
def baseEnd_1844200 : Nat := 140290521929154043365731

theorem tailTrace_1844200 : CollatzResearch.WordTrace tailWord_1844200 prefixEnd_1844200 140290521929154043365731 := by
  unfold tailWord_1844200
  simp only [CollatzResearch.WordTrace]
  refine ⟨33631749959392919564761027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44842333279190559419681369 33631749959392919564761027)
  ·
    refine ⟨50447624939089379347141541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33631749959392919564761027 50447624939089379347141541)
    ·
      refine ⟨9458929676079258627589039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 50447624939089379347141541 9458929676079258627589039)
      ·
        refine ⟨14188394514118887941383559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9458929676079258627589039 14188394514118887941383559)
        ·
          refine ⟨21282591771178331912075339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14188394514118887941383559 21282591771178331912075339)
          ·
            refine ⟨31923887656767497868113009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21282591771178331912075339 31923887656767497868113009)
            ·
              refine ⟨23942915742575623401084757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31923887656767497868113009 23942915742575623401084757)
              ·
                refine ⟨140290521929154043365731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 23942915742575623401084757 140290521929154043365731)
                ·
                  rfl

theorem cell21_1844200_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 2, 9].length) (baseStart_1844200 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1844200 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1844200 prefixEnd_1844200 := by exact prefixLift 1844200
  have htrace : WordTrace (prefixWord ++ tailWord_1844200) baseStart_1844200 baseEnd_1844200 := by
    simpa [prefixWord, tailWord_1844200, baseEnd_1844200] using wordTrace_append hprefix tailTrace_1844200
  have hstable : (prefixWord ++ tailWord_1844200).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1844200).length < 2 ^ (prefixWord ++ tailWord_1844200).sum := by decide
  have hdescent : baseEnd_1844200 < baseStart_1844200 := by decide
  rcases family_descends (prefixWord ++ tailWord_1844200) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1844206 : List Nat := [4, 1, 2, 1, 4, 1, 2, 3, 3]
def baseStart_1844206 : Nat := 118140960795 + 1844206 * 2 ^ 59
def prefixEnd_1844206 : Nat := 4983230072969 + 3 ^ 40 * 1844206 * 2
def baseEnd_1844206 : Nat := 420872935069207452997181

theorem tailTrace_1844206 : CollatzResearch.WordTrace tailWord_1844206 prefixEnd_1844206 420872935069207452997181 := by
  unfold tailWord_1844206
  simp only [CollatzResearch.WordTrace]
  refine ⟨8407964844595512769280059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 44842479171176068102826981 8407964844595512769280059)
  ·
    refine ⟨12611947266893269153920089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8407964844595512769280059 12611947266893269153920089)
    ·
      refine ⟨9458960450169951865440067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12611947266893269153920089 9458960450169951865440067)
      ·
        refine ⟨14188440675254927798160101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9458960450169951865440067 14188440675254927798160101)
        ·
          refine ⟨2660332626610298962155019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 14188440675254927798160101 2660332626610298962155019)
          ·
            refine ⟨3990498939915448443232529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2660332626610298962155019 3990498939915448443232529)
            ·
              refine ⟨2992874204936586332424397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3990498939915448443232529 2992874204936586332424397)
              ·
                refine ⟨1122327826851219874659149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2992874204936586332424397 1122327826851219874659149)
                ·
                  refine ⟨420872935069207452997181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1122327826851219874659149 420872935069207452997181)
                  ·
                    rfl

theorem cell21_1844206_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 4, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 4, 1, 2, 3, 3].length) (baseStart_1844206 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1844206 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1844206 prefixEnd_1844206 := by exact prefixLift 1844206
  have htrace : WordTrace (prefixWord ++ tailWord_1844206) baseStart_1844206 baseEnd_1844206 := by
    simpa [prefixWord, tailWord_1844206, baseEnd_1844206] using wordTrace_append hprefix tailTrace_1844206
  have hstable : (prefixWord ++ tailWord_1844206).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1844206).length < 2 ^ (prefixWord ++ tailWord_1844206).sum := by decide
  have hdescent : baseEnd_1844206 < baseStart_1844206 := by decide
  rcases family_descends (prefixWord ++ tailWord_1844206) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1844212 : List Nat := [2, 6, 2, 1, 2, 1, 1, 2, 4]
def baseStart_1844212 : Nat := 118140960795 + 1844212 * 2 ^ 59
def prefixEnd_1844212 : Nat := 4983230072969 + 3 ^ 40 * 1844212 * 2
def baseEnd_1844212 : Nat := 420874304350952775897169

theorem tailTrace_1844212 : CollatzResearch.WordTrace tailWord_1844212 prefixEnd_1844212 420874304350952775897169 := by
  unfold tailWord_1844212
  simp only [CollatzResearch.WordTrace]
  refine ⟨33631968797371182589479445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44842625063161576785972593 33631968797371182589479445)
  ·
    refine ⟨1576498537376774183881849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 33631968797371182589479445 1576498537376774183881849)
    ·
      refine ⟨1182373903032580637911387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1576498537376774183881849 1182373903032580637911387)
      ·
        refine ⟨1773560854548870956867081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1182373903032580637911387 1773560854548870956867081)
        ·
          refine ⟨1330170640911653217650311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1773560854548870956867081 1330170640911653217650311)
          ·
            refine ⟨1995255961367479826475467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1330170640911653217650311 1995255961367479826475467)
            ·
              refine ⟨2992883942051219739713201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1995255961367479826475467 2992883942051219739713201)
              ·
                refine ⟨2244662956538414804784901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2992883942051219739713201 2244662956538414804784901)
                ·
                  refine ⟨420874304350952775897169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2244662956538414804784901 420874304350952775897169)
                  ·
                    rfl

theorem cell21_1844212_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 2, 1, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 2, 1, 2, 1, 1, 2, 4].length) (baseStart_1844212 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1844212 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1844212 prefixEnd_1844212 := by exact prefixLift 1844212
  have htrace : WordTrace (prefixWord ++ tailWord_1844212) baseStart_1844212 baseEnd_1844212 := by
    simpa [prefixWord, tailWord_1844212, baseEnd_1844212] using wordTrace_append hprefix tailTrace_1844212
  have hstable : (prefixWord ++ tailWord_1844212).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1844212).length < 2 ^ (prefixWord ++ tailWord_1844212).sum := by decide
  have hdescent : baseEnd_1844212 < baseStart_1844212 := by decide
  rcases family_descends (prefixWord ++ tailWord_1844212) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1844321 : List Nat := [1, 2, 3, 1, 1, 2, 2, 1, 8]
def baseStart_1844321 : Nat := 118140960795 + 1844321 * 2 ^ 59
def prefixEnd_1844321 : Nat := 4983230072969 + 3 ^ 40 * 1844321 * 2
def baseEnd_1844321 : Nat := 420899179635992808580279

theorem tailTrace_1844321 : CollatzResearch.WordTrace tailWord_1844321 prefixEnd_1844321 420899179635992808580279 := by
  unfold tailWord_1844321
  simp only [CollatzResearch.WordTrace]
  refine ⟨67267913151347476794676817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44845275434231651196451211 67267913151347476794676817)
  ·
    refine ⟨50450934863510607596007613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67267913151347476794676817 50450934863510607596007613)
    ·
      refine ⟨18919100573816477848502855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 50450934863510607596007613 18919100573816477848502855)
      ·
        refine ⟨28378650860724716772754283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18919100573816477848502855 28378650860724716772754283)
        ·
          refine ⟨42567976291087075159131425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28378650860724716772754283 42567976291087075159131425)
          ·
            refine ⟨31925982218315306369348569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42567976291087075159131425 31925982218315306369348569)
            ·
              refine ⟨23944486663736479777011427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31925982218315306369348569 23944486663736479777011427)
              ·
                refine ⟨35916729995604719665517141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23944486663736479777011427 35916729995604719665517141)
                ·
                  refine ⟨420899179635992808580279, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 35916729995604719665517141 420899179635992808580279)
                  ·
                    rfl

theorem cell21_1844321_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 2, 1, 8].length) (baseStart_1844321 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1844321 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1844321 prefixEnd_1844321 := by exact prefixLift 1844321
  have htrace : WordTrace (prefixWord ++ tailWord_1844321) baseStart_1844321 baseEnd_1844321 := by
    simpa [prefixWord, tailWord_1844321, baseEnd_1844321] using wordTrace_append hprefix tailTrace_1844321
  have hstable : (prefixWord ++ tailWord_1844321).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1844321).length < 2 ^ (prefixWord ++ tailWord_1844321).sum := by decide
  have hdescent : baseEnd_1844321 < baseStart_1844321 := by decide
  rcases family_descends (prefixWord ++ tailWord_1844321) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1844324 : List Nat := [2, 3, 1, 1, 2, 1, 1, 7, 3]
def baseStart_1844324 : Nat := 118140960795 + 1844324 * 2 ^ 59
def prefixEnd_1844324 : Nat := 4983230072969 + 3 ^ 40 * 1844324 * 2
def baseEnd_1844324 : Nat := 420899864276865470030273

theorem tailTrace_1844324 : CollatzResearch.WordTrace tailWord_1844324 prefixEnd_1844324 420899864276865470030273 := by
  unfold tailWord_1844324
  simp only [CollatzResearch.WordTrace]
  refine ⟨33634011285168304153518013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44845348380224405538024017 33634011285168304153518013)
  ·
    refine ⟨12612754231938114057569255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 33634011285168304153518013 12612754231938114057569255)
    ·
      refine ⟨18919131347907171086353883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12612754231938114057569255 18919131347907171086353883)
      ·
        refine ⟨28378697021860756629530825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18919131347907171086353883 28378697021860756629530825)
        ·
          refine ⟨21284022766395567472148119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28378697021860756629530825 21284022766395567472148119)
          ·
            refine ⟨31926034149593351208222179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21284022766395567472148119 31926034149593351208222179)
            ·
              refine ⟨47889051224390026812333269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31926034149593351208222179 47889051224390026812333269)
              ·
                refine ⟨1122399638071641253414061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 47889051224390026812333269 1122399638071641253414061)
                ·
                  refine ⟨420899864276865470030273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1122399638071641253414061 420899864276865470030273)
                  ·
                    rfl

theorem cell21_1844324_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 1, 7, 3].length) (baseStart_1844324 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1844324 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1844324 prefixEnd_1844324 := by exact prefixLift 1844324
  have htrace : WordTrace (prefixWord ++ tailWord_1844324) baseStart_1844324 baseEnd_1844324 := by
    simpa [prefixWord, tailWord_1844324, baseEnd_1844324] using wordTrace_append hprefix tailTrace_1844324
  have hstable : (prefixWord ++ tailWord_1844324).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1844324).length < 2 ^ (prefixWord ++ tailWord_1844324).sum := by decide
  have hdescent : baseEnd_1844324 < baseStart_1844324 := by decide
  rcases family_descends (prefixWord ++ tailWord_1844324) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1844352 : List Nat := [2, 1, 1, 2, 1, 3, 5, 6]
def baseStart_1844352 : Nat := 118140960795 + 1844352 * 2 ^ 59
def prefixEnd_1844352 : Nat := 4983230072969 + 3 ^ 40 * 1844352 * 2
def baseEnd_1844352 : Nat := 140302084752781214521183

theorem tailTrace_1844352 : CollatzResearch.WordTrace tailWord_1844352 prefixEnd_1844352 140302084752781214521183 := by
  unfold tailWord_1844352
  simp only [CollatzResearch.WordTrace]
  refine ⟨33634521907117584544527655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44846029209490112726036873 33634521907117584544527655)
  ·
    refine ⟨50451782860676376816791483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33634521907117584544527655 50451782860676376816791483)
    ·
      refine ⟨75677674291014565225187225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50451782860676376816791483 75677674291014565225187225)
      ·
        refine ⟨56758255718260923918890419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 75677674291014565225187225 56758255718260923918890419)
        ·
          refine ⟨85137383577391385878335629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56758255718260923918890419 85137383577391385878335629)
          ·
            refine ⟨31926518841521769704375861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 85137383577391385878335629 31926518841521769704375861)
            ·
              refine ⟨2993111141392665909785237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 31926518841521769704375861 2993111141392665909785237)
              ·
                refine ⟨140302084752781214521183, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2993111141392665909785237 140302084752781214521183)
                ·
                  rfl

theorem cell21_1844352_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 5, 6].length) (baseStart_1844352 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1844352 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1844352 prefixEnd_1844352 := by exact prefixLift 1844352
  have htrace : WordTrace (prefixWord ++ tailWord_1844352) baseStart_1844352 baseEnd_1844352 := by
    simpa [prefixWord, tailWord_1844352, baseEnd_1844352] using wordTrace_append hprefix tailTrace_1844352
  have hstable : (prefixWord ++ tailWord_1844352).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1844352).length < 2 ^ (prefixWord ++ tailWord_1844352).sum := by decide
  have hdescent : baseEnd_1844352 < baseStart_1844352 := by decide
  rcases family_descends (prefixWord ++ tailWord_1844352) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1844406 : List Nat := [5, 1, 3, 2, 1, 1, 3, 1, 4]
def baseStart_1844406 : Nat := 118140960795 + 1844406 * 2 ^ 59
def prefixEnd_1844406 : Nat := 4983230072969 + 3 ^ 40 * 1844406 * 2
def baseEnd_1844406 : Nat := 420918577794051549663439

theorem tailTrace_1844406 : CollatzResearch.WordTrace tailWord_1844406 prefixEnd_1844406 420918577794051549663439 := by
  unfold tailWord_1844406
  simp only [CollatzResearch.WordTrace]
  refine ⟨4204438334752471019470067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 44847342237359690874347381 4204438334752471019470067)
  ·
    refine ⟨6306657502128706529205101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4204438334752471019470067 6306657502128706529205101)
    ·
      refine ⟨2364996563298264948451913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6306657502128706529205101 2364996563298264948451913)
      ·
        refine ⟨1773747422473698711338935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2364996563298264948451913 1773747422473698711338935)
        ·
          refine ⟨2660621133710548067008403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1773747422473698711338935 2660621133710548067008403)
          ·
            refine ⟨3990931700565822100512605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2660621133710548067008403 3990931700565822100512605)
            ·
              refine ⟨1496599387712183287692227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3990931700565822100512605 1496599387712183287692227)
              ·
                refine ⟨2244899081568274931538341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1496599387712183287692227 2244899081568274931538341)
                ·
                  refine ⟨420918577794051549663439, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2244899081568274931538341 420918577794051549663439)
                  ·
                    rfl

theorem cell21_1844406_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 2, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 2, 1, 1, 3, 1, 4].length) (baseStart_1844406 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1844406 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1844406 prefixEnd_1844406 := by exact prefixLift 1844406
  have htrace : WordTrace (prefixWord ++ tailWord_1844406) baseStart_1844406 baseEnd_1844406 := by
    simpa [prefixWord, tailWord_1844406, baseEnd_1844406] using wordTrace_append hprefix tailTrace_1844406
  have hstable : (prefixWord ++ tailWord_1844406).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1844406).length < 2 ^ (prefixWord ++ tailWord_1844406).sum := by decide
  have hdescent : baseEnd_1844406 < baseStart_1844406 := by decide
  rcases family_descends (prefixWord ++ tailWord_1844406) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1844459 : List Nat := [1, 1, 1, 1, 2, 6, 3, 1, 5]
def baseStart_1844459 : Nat := 118140960795 + 1844459 * 2 ^ 59
def prefixEnd_1844459 : Nat := 4983230072969 + 3 ^ 40 * 1844459 * 2
def baseEnd_1844459 : Nat := 420930673116135235279997

theorem tailTrace_1844459 : CollatzResearch.WordTrace tailWord_1844459 prefixEnd_1844459 420930673116135235279997 := by
  unfold tailWord_1844459
  simp only [CollatzResearch.WordTrace]
  refine ⟨67272946424847526363200431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44848630949898350908800287 67272946424847526363200431)
  ·
    refine ⟨100909419637271289544800647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67272946424847526363200431 100909419637271289544800647)
    ·
      refine ⟨151364129455906934317200971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100909419637271289544800647 151364129455906934317200971)
      ·
        refine ⟨227046194183860401475801457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 151364129455906934317200971 227046194183860401475801457)
        ·
          refine ⟨170284645637895301106851093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 227046194183860401475801457 170284645637895301106851093)
          ·
            refine ⟨7982092764276342239383645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 170284645637895301106851093 7982092764276342239383645)
            ·
              refine ⟨2993284786603628339768867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7982092764276342239383645 2993284786603628339768867)
              ·
                refine ⟨4489927179905442509653301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2993284786603628339768867 4489927179905442509653301)
                ·
                  refine ⟨420930673116135235279997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4489927179905442509653301 420930673116135235279997)
                  ·
                    rfl

theorem cell21_1844459_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 6, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 6, 3, 1, 5].length) (baseStart_1844459 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1844459 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1844459 prefixEnd_1844459 := by exact prefixLift 1844459
  have htrace : WordTrace (prefixWord ++ tailWord_1844459) baseStart_1844459 baseEnd_1844459 := by
    simpa [prefixWord, tailWord_1844459, baseEnd_1844459] using wordTrace_append hprefix tailTrace_1844459
  have hstable : (prefixWord ++ tailWord_1844459).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1844459).length < 2 ^ (prefixWord ++ tailWord_1844459).sum := by decide
  have hdescent : baseEnd_1844459 < baseStart_1844459 := by decide
  rcases family_descends (prefixWord ++ tailWord_1844459) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1844563 : List Nat := [1, 1, 1, 2, 1, 1, 14]
def baseStart_1844563 : Nat := 118140960795 + 1844563 * 2 ^ 59
def prefixEnd_1844563 : Nat := 4983230072969 + 3 ^ 40 * 1844563 * 2
def baseEnd_1844563 : Nat := 46772711925894907282939

theorem tailTrace_1844563 : CollatzResearch.WordTrace tailWord_1844563 prefixEnd_1844563 46772711925894907282939 := by
  unfold tailWord_1844563
  simp only [CollatzResearch.WordTrace]
  refine ⟨67276739616470752124986343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44851159744313834749990895 67276739616470752124986343)
  ·
    refine ⟨100915109424706128187479515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67276739616470752124986343 100915109424706128187479515)
    ·
      refine ⟨151372664137059192281219273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100915109424706128187479515 151372664137059192281219273)
      ·
        refine ⟨113529498102794394210914455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 151372664137059192281219273 113529498102794394210914455)
        ·
          refine ⟨170294247154191591316371683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 113529498102794394210914455 170294247154191591316371683)
          ·
            refine ⟨255441370731287386974557525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 170294247154191591316371683 255441370731287386974557525)
            ·
              refine ⟨46772711925894907282939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 14 255441370731287386974557525 46772711925894907282939)
              ·
                rfl

theorem cell21_1844563_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 14].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 14].length) (baseStart_1844563 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1844563 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1844563 prefixEnd_1844563 := by exact prefixLift 1844563
  have htrace : WordTrace (prefixWord ++ tailWord_1844563) baseStart_1844563 baseEnd_1844563 := by
    simpa [prefixWord, tailWord_1844563, baseEnd_1844563] using wordTrace_append hprefix tailTrace_1844563
  have hstable : (prefixWord ++ tailWord_1844563).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1844563).length < 2 ^ (prefixWord ++ tailWord_1844563).sum := by decide
  have hdescent : baseEnd_1844563 < baseStart_1844563 := by decide
  rcases family_descends (prefixWord ++ tailWord_1844563) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1844597 : List Nat := [1, 3, 4, 1, 3, 1, 1, 7]
def baseStart_1844597 : Nat := 118140960795 + 1844597 * 2 ^ 59
def prefixEnd_1844597 : Nat := 4983230072969 + 3 ^ 40 * 1844597 * 2
def baseEnd_1844597 : Nat := 140320722198759220659905

theorem tailTrace_1844597 : CollatzResearch.WordTrace tailWord_1844597 prefixEnd_1844597 140320722198759220659905 := by
  unfold tailWord_1844597
  simp only [CollatzResearch.WordTrace]
  refine ⟨67277979698347575931724045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44851986465565050621149363 67277979698347575931724045)
  ·
    refine ⟨25229242386880340974396517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 67277979698347575931724045 25229242386880340974396517)
    ·
      refine ⟨4730482947540063932699347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 25229242386880340974396517 4730482947540063932699347)
      ·
        refine ⟨7095724421310095899049021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4730482947540063932699347 7095724421310095899049021)
        ·
          refine ⟨2660896657991285962143383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7095724421310095899049021 2660896657991285962143383)
          ·
            refine ⟨3991344986986928943215075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2660896657991285962143383 3991344986986928943215075)
            ·
              refine ⟨5987017480480393414822613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3991344986986928943215075 5987017480480393414822613)
              ·
                refine ⟨140320722198759220659905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5987017480480393414822613 140320722198759220659905)
                ·
                  rfl

theorem cell21_1844597_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 3, 1, 1, 7].length) (baseStart_1844597 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1844597 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1844597 prefixEnd_1844597 := by exact prefixLift 1844597
  have htrace : WordTrace (prefixWord ++ tailWord_1844597) baseStart_1844597 baseEnd_1844597 := by
    simpa [prefixWord, tailWord_1844597, baseEnd_1844597] using wordTrace_append hprefix tailTrace_1844597
  have hstable : (prefixWord ++ tailWord_1844597).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1844597).length < 2 ^ (prefixWord ++ tailWord_1844597).sum := by decide
  have hdescent : baseEnd_1844597 < baseStart_1844597 := by decide
  rcases family_descends (prefixWord ++ tailWord_1844597) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1844628 : List Nat := [2, 4, 2, 1, 2, 1, 3, 1, 5]
def baseStart_1844628 : Nat := 118140960795 + 1844628 * 2 ^ 59
def prefixEnd_1844628 : Nat := 4983230072969 + 3 ^ 40 * 1844628 * 2
def baseEnd_1844628 : Nat := 420969241218628496962985

theorem tailTrace_1844628 : CollatzResearch.WordTrace tailWord_1844628 prefixEnd_1844628 420969241218628496962985 := by
  unfold tailWord_1844628
  simp only [CollatzResearch.WordTrace]
  refine ⟨33639555180617634113051269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44852740240823512150735025 33639555180617634113051269)
  ·
    refine ⟨6307416596365806396197113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 33639555180617634113051269 6307416596365806396197113)
    ·
      refine ⟨4730562447274354797147835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6307416596365806396197113 4730562447274354797147835)
      ·
        refine ⟨7095843670911532195721753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4730562447274354797147835 7095843670911532195721753)
        ·
          refine ⟨5321882753183649146791315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7095843670911532195721753 5321882753183649146791315)
          ·
            refine ⟨7982824129775473720186973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5321882753183649146791315 7982824129775473720186973)
            ·
              refine ⟨2993559048665802645070115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7982824129775473720186973 2993559048665802645070115)
              ·
                refine ⟨4490338572998703967605173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2993559048665802645070115 4490338572998703967605173)
                ·
                  refine ⟨420969241218628496962985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4490338572998703967605173 420969241218628496962985)
                  ·
                    rfl

theorem cell21_1844628_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 1, 3, 1, 5].length) (baseStart_1844628 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1844628 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1844628 prefixEnd_1844628 := by exact prefixLift 1844628
  have htrace : WordTrace (prefixWord ++ tailWord_1844628) baseStart_1844628 baseEnd_1844628 := by
    simpa [prefixWord, tailWord_1844628, baseEnd_1844628] using wordTrace_append hprefix tailTrace_1844628
  have hstable : (prefixWord ++ tailWord_1844628).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1844628).length < 2 ^ (prefixWord ++ tailWord_1844628).sum := by decide
  have hdescent : baseEnd_1844628 < baseStart_1844628 := by decide
  rcases family_descends (prefixWord ++ tailWord_1844628) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1844791 : List Nat := [1, 1, 3, 1, 2, 4, 9]
def baseStart_1844791 : Nat := 118140960795 + 1844791 * 2 ^ 59
def prefixEnd_1844791 : Nat := 4983230072969 + 3 ^ 40 * 1844791 * 2
def baseEnd_1844791 : Nat := 46778493337708492860665

theorem tailTrace_1844791 : CollatzResearch.WordTrace tailWord_1844791 prefixEnd_1844791 46778493337708492860665 := by
  unfold tailWord_1844791
  simp only [CollatzResearch.WordTrace]
  refine ⟨67285055459644747064286227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44856703639763164709524151 67285055459644747064286227)
  ·
    refine ⟨100927583189467120596429341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67285055459644747064286227 100927583189467120596429341)
    ·
      refine ⟨37847843696050170223661003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 100927583189467120596429341 37847843696050170223661003)
      ·
        refine ⟨56771765544075255335491505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37847843696050170223661003 56771765544075255335491505)
        ·
          refine ⟨42578824158056441501618629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56771765544075255335491505 42578824158056441501618629)
          ·
            refine ⟨7983529529635582781553493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 42578824158056441501618629 7983529529635582781553493)
            ·
              refine ⟨46778493337708492860665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 7983529529635582781553493 46778493337708492860665)
              ·
                rfl

theorem cell21_1844791_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 4, 9].length) (baseStart_1844791 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1844791 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1844791 prefixEnd_1844791 := by exact prefixLift 1844791
  have htrace : WordTrace (prefixWord ++ tailWord_1844791) baseStart_1844791 baseEnd_1844791 := by
    simpa [prefixWord, tailWord_1844791, baseEnd_1844791] using wordTrace_append hprefix tailTrace_1844791
  have hstable : (prefixWord ++ tailWord_1844791).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1844791).length < 2 ^ (prefixWord ++ tailWord_1844791).sum := by decide
  have hdescent : baseEnd_1844791 < baseStart_1844791 := by decide
  rcases family_descends (prefixWord ++ tailWord_1844791) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1844797 : List Nat := [1, 4, 1, 3, 4, 1, 1, 1, 5]
def baseStart_1844797 : Nat := 118140960795 + 1844797 * 2 ^ 59
def prefixEnd_1844797 : Nat := 4983230072969 + 3 ^ 40 * 1844797 * 2
def baseEnd_1844797 : Nat := 421007809321121758645973

theorem tailTrace_1844797 : CollatzResearch.WordTrace tailWord_1844797 prefixEnd_1844797 421007809321121758645973 := by
  unfold tailWord_1844797
  simp only [CollatzResearch.WordTrace]
  refine ⟨67285274297623010089004645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44856849531748673392669763 67285274297623010089004645)
  ·
    refine ⟨12615988930804314391688371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 67285274297623010089004645 12615988930804314391688371)
    ·
      refine ⟨18923983396206471587532557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12615988930804314391688371 18923983396206471587532557)
      ·
        refine ⟨7096493773577426845324709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18923983396206471587532557 7096493773577426845324709)
        ·
          refine ⟨1330592582545767533498383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7096493773577426845324709 1330592582545767533498383)
          ·
            refine ⟨1995888873818651300247575, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1330592582545767533498383 1995888873818651300247575)
            ·
              refine ⟨2993833310727976950371363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1995888873818651300247575 2993833310727976950371363)
              ·
                refine ⟨4490749966091965425557045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2993833310727976950371363 4490749966091965425557045)
                ·
                  refine ⟨421007809321121758645973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4490749966091965425557045 421007809321121758645973)
                  ·
                    rfl

theorem cell21_1844797_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 4, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 4, 1, 1, 1, 5].length) (baseStart_1844797 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1844797 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1844797 prefixEnd_1844797 := by exact prefixLift 1844797
  have htrace : WordTrace (prefixWord ++ tailWord_1844797) baseStart_1844797 baseEnd_1844797 := by
    simpa [prefixWord, tailWord_1844797, baseEnd_1844797] using wordTrace_append hprefix tailTrace_1844797
  have hstable : (prefixWord ++ tailWord_1844797).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1844797).length < 2 ^ (prefixWord ++ tailWord_1844797).sum := by decide
  have hdescent : baseEnd_1844797 < baseStart_1844797 := by decide
  rcases family_descends (prefixWord ++ tailWord_1844797) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1844904 : List Nat := [2, 1, 7, 1, 1, 1, 1, 1, 6]
def baseStart_1844904 : Nat := 118140960795 + 1844904 * 2 ^ 59
def prefixEnd_1844904 : Nat := 4983230072969 + 3 ^ 40 * 1844904 * 2
def baseEnd_1844904 : Nat := 421032228178913350362421

theorem tailTrace_1844904 : CollatzResearch.WordTrace tailWord_1844904 prefixEnd_1844904 421032228178913350362421 := by
  unfold tailWord_1844904
  simp only [CollatzResearch.WordTrace]
  refine ⟨33644588454117683681574883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44859451272156911575433177 33644588454117683681574883)
  ·
    refine ⟨50466882681176525522362325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33644588454117683681574883 50466882681176525522362325)
    ·
      refine ⟨1182817562840074816930367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 50466882681176525522362325 1182817562840074816930367)
      ·
        refine ⟨1774226344260112225395551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1182817562840074816930367 1774226344260112225395551)
        ·
          refine ⟨2661339516390168338093327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1774226344260112225395551 2661339516390168338093327)
          ·
            refine ⟨3992009274585252507139991, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2661339516390168338093327 3992009274585252507139991)
            ·
              refine ⟨5988013911877878760709987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3992009274585252507139991 5988013911877878760709987)
              ·
                refine ⟨8982020867816818141064981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5988013911877878760709987 8982020867816818141064981)
                ·
                  refine ⟨421032228178913350362421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8982020867816818141064981 421032228178913350362421)
                  ·
                    rfl

theorem cell21_1844904_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 7, 1, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 7, 1, 1, 1, 1, 1, 6].length) (baseStart_1844904 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1844904 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1844904 prefixEnd_1844904 := by exact prefixLift 1844904
  have htrace : WordTrace (prefixWord ++ tailWord_1844904) baseStart_1844904 baseEnd_1844904 := by
    simpa [prefixWord, tailWord_1844904, baseEnd_1844904] using wordTrace_append hprefix tailTrace_1844904
  have hstable : (prefixWord ++ tailWord_1844904).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1844904).length < 2 ^ (prefixWord ++ tailWord_1844904).sum := by decide
  have hdescent : baseEnd_1844904 < baseStart_1844904 := by decide
  rcases family_descends (prefixWord ++ tailWord_1844904) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1844915 : List Nat := [1, 1, 1, 2, 3, 3, 1, 6, 3]
def baseStart_1844915 : Nat := 118140960795 + 1844915 * 2 ^ 59
def prefixEnd_1844915 : Nat := 4983230072969 + 3 ^ 40 * 1844915 * 2
def baseEnd_1844915 : Nat := 421034738528779775679065

theorem tailTrace_1844915 : CollatzResearch.WordTrace tailWord_1844915 prefixEnd_1844915 421034738528779775679065 := by
  unfold tailWord_1844915
  simp only [CollatzResearch.WordTrace]
  refine ⟨67289578111195516241800199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44859718740797010827866799 67289578111195516241800199)
  ·
    refine ⟨100934367166793274362700299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67289578111195516241800199 100934367166793274362700299)
    ·
      refine ⟨151401550750189911544050449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100934367166793274362700299 151401550750189911544050449)
      ·
        refine ⟨113551163062642433658037837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 151401550750189911544050449 113551163062642433658037837)
        ·
          refine ⟨42581686148490912621764189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 113551163062642433658037837 42581686148490912621764189)
          ·
            refine ⟨15968132305684092233161571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 42581686148490912621764189 15968132305684092233161571)
            ·
              refine ⟨23952198458526138349742357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15968132305684092233161571 23952198458526138349742357)
              ·
                refine ⟨1122759302743412735144173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 23952198458526138349742357 1122759302743412735144173)
                ·
                  refine ⟨421034738528779775679065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1122759302743412735144173 421034738528779775679065)
                  ·
                    rfl

theorem cell21_1844915_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 1, 6, 3].length) (baseStart_1844915 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1844915 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1844915 prefixEnd_1844915 := by exact prefixLift 1844915
  have htrace : WordTrace (prefixWord ++ tailWord_1844915) baseStart_1844915 baseEnd_1844915 := by
    simpa [prefixWord, tailWord_1844915, baseEnd_1844915] using wordTrace_append hprefix tailTrace_1844915
  have hstable : (prefixWord ++ tailWord_1844915).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1844915).length < 2 ^ (prefixWord ++ tailWord_1844915).sum := by decide
  have hdescent : baseEnd_1844915 < baseStart_1844915 := by decide
  rcases family_descends (prefixWord ++ tailWord_1844915) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1844980 : List Nat := [2, 6, 1, 1, 1, 2, 1, 3, 4]
def baseStart_1844980 : Nat := 118140960795 + 1844980 * 2 ^ 59
def prefixEnd_1844980 : Nat := 4983230072969 + 3 ^ 40 * 1844980 * 2
def baseEnd_1844980 : Nat := 421049572414354107095599

theorem tailTrace_1844980 : CollatzResearch.WordTrace tailWord_1844980 prefixEnd_1844980 421049572414354107095599 := by
  unfold tailWord_1844980
  simp only [CollatzResearch.WordTrace]
  refine ⟨33645974427980016171458197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44861299237306688228610929 33645974427980016171458197)
  ·
    refine ⟨1577155051311563258037103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 33645974427980016171458197 1577155051311563258037103)
    ·
      refine ⟨2365732576967344887055655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1577155051311563258037103 2365732576967344887055655)
      ·
        refine ⟨3548598865451017330583483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2365732576967344887055655 3548598865451017330583483)
        ·
          refine ⟨5322898298176525995875225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3548598865451017330583483 5322898298176525995875225)
          ·
            refine ⟨3992173723632394496906419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5322898298176525995875225 3992173723632394496906419)
            ·
              refine ⟨5988260585448591745359629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3992173723632394496906419 5988260585448591745359629)
              ·
                refine ⟨2245597719543221904509861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5988260585448591745359629 2245597719543221904509861)
                ·
                  refine ⟨421049572414354107095599, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2245597719543221904509861 421049572414354107095599)
                  ·
                    rfl

theorem cell21_1844980_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 2, 1, 3, 4].length) (baseStart_1844980 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1844980 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1844980 prefixEnd_1844980 := by exact prefixLift 1844980
  have htrace : WordTrace (prefixWord ++ tailWord_1844980) baseStart_1844980 baseEnd_1844980 := by
    simpa [prefixWord, tailWord_1844980, baseEnd_1844980] using wordTrace_append hprefix tailTrace_1844980
  have hstable : (prefixWord ++ tailWord_1844980).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1844980).length < 2 ^ (prefixWord ++ tailWord_1844980).sum := by decide
  have hdescent : baseEnd_1844980 < baseStart_1844980 := by decide
  rcases family_descends (prefixWord ++ tailWord_1844980) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1845025 : List Nat := [1, 2, 3, 2, 1, 5, 2, 2, 3]
def baseStart_1845025 : Nat := 118140960795 + 1845025 * 2 ^ 59
def prefixEnd_1845025 : Nat := 4983230072969 + 3 ^ 40 * 1845025 * 2
def baseEnd_1845025 : Nat := 421059842027444028845507

theorem tailTrace_1845025 : CollatzResearch.WordTrace tailWord_1845025 prefixEnd_1845025 421059842027444028845507 := by
  unfold tailWord_1845025
  simp only [CollatzResearch.WordTrace]
  refine ⟨67293590140797005028304529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44862393427198003352203019 67293590140797005028304529)
  ·
    refine ⟨50470192605597753771228397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67293590140797005028304529 50470192605597753771228397)
    ·
      refine ⟨18926322227099157664210649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 50470192605597753771228397 18926322227099157664210649)
      ·
        refine ⟨14194741670324368248157987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18926322227099157664210649 14194741670324368248157987)
        ·
          refine ⟨21292112505486552372236981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14194741670324368248157987 21292112505486552372236981)
          ·
            refine ⟨1996135547389364284897217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 21292112505486552372236981 1996135547389364284897217)
            ·
              refine ⟨1497101660542023213672913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1996135547389364284897217 1497101660542023213672913)
              ·
                refine ⟨1122826245406517410254685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1497101660542023213672913 1122826245406517410254685)
                ·
                  refine ⟨421059842027444028845507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1122826245406517410254685 421059842027444028845507)
                  ·
                    rfl

theorem cell21_1845025_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 5, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 5, 2, 2, 3].length) (baseStart_1845025 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1845025 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1845025 prefixEnd_1845025 := by exact prefixLift 1845025
  have htrace : WordTrace (prefixWord ++ tailWord_1845025) baseStart_1845025 baseEnd_1845025 := by
    simpa [prefixWord, tailWord_1845025, baseEnd_1845025] using wordTrace_append hprefix tailTrace_1845025
  have hstable : (prefixWord ++ tailWord_1845025).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1845025).length < 2 ^ (prefixWord ++ tailWord_1845025).sum := by decide
  have hdescent : baseEnd_1845025 < baseStart_1845025 := by decide
  rcases family_descends (prefixWord ++ tailWord_1845025) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1845036 : List Nat := [2, 2, 1, 1, 1, 7, 1, 6]
def baseStart_1845036 : Nat := 118140960795 + 1845036 * 2 ^ 59
def prefixEnd_1845036 : Nat := 4983230072969 + 3 ^ 40 * 1845036 * 2
def baseEnd_1845036 : Nat := 140354117459103484720717

theorem tailTrace_1845036 : CollatzResearch.WordTrace tailWord_1845036 prefixEnd_1845036 140354117459103484720717 := by
  unfold tailWord_1845036
  simp only [CollatzResearch.WordTrace]
  refine ⟨33646995671878576953477481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44862660895838102604636641 33646995671878576953477481)
  ·
    refine ⟨25235246753908932715108111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33646995671878576953477481 25235246753908932715108111)
    ·
      refine ⟨37852870130863399072662167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25235246753908932715108111 37852870130863399072662167)
      ·
        refine ⟨56779305196295098608993251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37852870130863399072662167 56779305196295098608993251)
        ·
          refine ⟨85168957794442647913489877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56779305196295098608993251 85168957794442647913489877)
          ·
            refine ⟨1996147448307249560472419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 85168957794442647913489877 1996147448307249560472419)
            ·
              refine ⟨2994221172460874340708629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1996147448307249560472419 2994221172460874340708629)
              ·
                refine ⟨140354117459103484720717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2994221172460874340708629 140354117459103484720717)
                ·
                  rfl

theorem cell21_1845036_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 7, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 7, 1, 6].length) (baseStart_1845036 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1845036 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1845036 prefixEnd_1845036 := by exact prefixLift 1845036
  have htrace : WordTrace (prefixWord ++ tailWord_1845036) baseStart_1845036 baseEnd_1845036 := by
    simpa [prefixWord, tailWord_1845036, baseEnd_1845036] using wordTrace_append hprefix tailTrace_1845036
  have hstable : (prefixWord ++ tailWord_1845036).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1845036).length < 2 ^ (prefixWord ++ tailWord_1845036).sum := by decide
  have hdescent : baseEnd_1845036 < baseStart_1845036 := by decide
  rcases family_descends (prefixWord ++ tailWord_1845036) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1845050 : List Nat := [3, 1, 1, 1, 5, 1, 1, 1, 7]
def baseStart_1845050 : Nat := 118140960795 + 1845050 * 2 ^ 59
def prefixEnd_1845050 : Nat := 4983230072969 + 3 ^ 40 * 1845050 * 2
def baseEnd_1845050 : Nat := 421065547368049540928789

theorem tailTrace_1845050 : CollatzResearch.WordTrace tailWord_1845050 prefixEnd_1845050 421065547368049540928789 := by
  unfold tailWord_1845050
  simp only [CollatzResearch.WordTrace]
  refine ⟨16823625491426608574491151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 44863001310470956198643069 16823625491426608574491151)
  ·
    refine ⟨25235438237139912861736727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16823625491426608574491151 25235438237139912861736727)
    ·
      refine ⟨37853157355709869292605091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25235438237139912861736727 37853157355709869292605091)
      ·
        refine ⟨56779736033564803938907637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37853157355709869292605091 56779736033564803938907637)
        ·
          refine ⟨5323100253146700369272591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 56779736033564803938907637 5323100253146700369272591)
          ·
            refine ⟨7984650379720050553908887, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5323100253146700369272591 7984650379720050553908887)
            ·
              refine ⟨11976975569580075830863331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7984650379720050553908887 11976975569580075830863331)
              ·
                refine ⟨17965463354370113746294997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11976975569580075830863331 17965463354370113746294997)
                ·
                  refine ⟨421065547368049540928789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 17965463354370113746294997 421065547368049540928789)
                  ·
                    rfl

theorem cell21_1845050_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 1, 1, 1, 7].length) (baseStart_1845050 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1845050 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1845050 prefixEnd_1845050 := by exact prefixLift 1845050
  have htrace : WordTrace (prefixWord ++ tailWord_1845050) baseStart_1845050 baseEnd_1845050 := by
    simpa [prefixWord, tailWord_1845050, baseEnd_1845050] using wordTrace_append hprefix tailTrace_1845050
  have hstable : (prefixWord ++ tailWord_1845050).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1845050).length < 2 ^ (prefixWord ++ tailWord_1845050).sum := by decide
  have hdescent : baseEnd_1845050 < baseStart_1845050 := by decide
  rcases family_descends (prefixWord ++ tailWord_1845050) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1845053 : List Nat := [1, 4, 1, 4, 1, 2, 3, 5]
def baseStart_1845053 : Nat := 118140960795 + 1845053 * 2 ^ 59
def prefixEnd_1845053 : Nat := 4983230072969 + 3 ^ 40 * 1845053 * 2
def baseEnd_1845053 : Nat := 140355410669640734126261

theorem tailTrace_1845053 : CollatzResearch.WordTrace tailWord_1845053 prefixEnd_1845053 140355410669640734126261 := by
  unfold tailWord_1845053
  simp only [CollatzResearch.WordTrace]
  refine ⟨67294611384695565810323813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44863074256463710540215875 67294611384695565810323813)
  ·
    refine ⟨12617739634630418589435715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 67294611384695565810323813 12617739634630418589435715)
    ·
      refine ⟨18926609451945627884153573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12617739634630418589435715 18926609451945627884153573)
      ·
        refine ⟨3548739272239805228278795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 18926609451945627884153573 3548739272239805228278795)
        ·
          refine ⟨5323108908359707842418193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3548739272239805228278795 5323108908359707842418193)
          ·
            refine ⟨3992331681269780881813645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5323108908359707842418193 3992331681269780881813645)
            ·
              refine ⟨1497124380476167830680117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3992331681269780881813645 1497124380476167830680117)
              ·
                refine ⟨140355410669640734126261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1497124380476167830680117 140355410669640734126261)
                ·
                  rfl

theorem cell21_1845053_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 2, 3, 5].length) (baseStart_1845053 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1845053 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1845053 prefixEnd_1845053 := by exact prefixLift 1845053
  have htrace : WordTrace (prefixWord ++ tailWord_1845053) baseStart_1845053 baseEnd_1845053 := by
    simpa [prefixWord, tailWord_1845053, baseEnd_1845053] using wordTrace_append hprefix tailTrace_1845053
  have hstable : (prefixWord ++ tailWord_1845053).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1845053).length < 2 ^ (prefixWord ++ tailWord_1845053).sum := by decide
  have hdescent : baseEnd_1845053 < baseStart_1845053 := by decide
  rcases family_descends (prefixWord ++ tailWord_1845053) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1845084 : List Nat := [2, 2, 4, 2, 2, 1, 2, 1, 5]
def baseStart_1845084 : Nat := 118140960795 + 1845084 * 2 ^ 59
def prefixEnd_1845084 : Nat := 4983230072969 + 3 ^ 40 * 1845084 * 2
def baseEnd_1845084 : Nat := 421073306631273037362053

theorem tailTrace_1845084 : CollatzResearch.WordTrace tailWord_1845084 prefixEnd_1845084 421073306631273037362053 := by
  unfold tailWord_1845084
  simp only [CollatzResearch.WordTrace]
  refine ⟨33647871023791629052351153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44863828031722172069801537 33647871023791629052351153)
  ·
    refine ⟨25235903267843721789263365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33647871023791629052351153 25235903267843721789263365)
    ·
      refine ⟨4731731862720697835486881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 25235903267843721789263365 4731731862720697835486881)
      ·
        refine ⟨3548798897040523376615161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4731731862720697835486881 3548798897040523376615161)
        ·
          refine ⟨2661599172780392532461371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3548798897040523376615161 2661599172780392532461371)
          ·
            refine ⟨3992398759170588798692057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2661599172780392532461371 3992398759170588798692057)
            ·
              refine ⟨2994299069377941599019043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3992398759170588798692057 2994299069377941599019043)
              ·
                refine ⟨4491448604066912398528565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2994299069377941599019043 4491448604066912398528565)
                ·
                  refine ⟨421073306631273037362053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4491448604066912398528565 421073306631273037362053)
                  ·
                    rfl

theorem cell21_1845084_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 2, 1, 2, 1, 5].length) (baseStart_1845084 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1845084 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1845084 prefixEnd_1845084 := by exact prefixLift 1845084
  have htrace : WordTrace (prefixWord ++ tailWord_1845084) baseStart_1845084 baseEnd_1845084 := by
    simpa [prefixWord, tailWord_1845084, baseEnd_1845084] using wordTrace_append hprefix tailTrace_1845084
  have hstable : (prefixWord ++ tailWord_1845084).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1845084).length < 2 ^ (prefixWord ++ tailWord_1845084).sum := by decide
  have hdescent : baseEnd_1845084 < baseStart_1845084 := by decide
  rcases family_descends (prefixWord ++ tailWord_1845084) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1845095 : List Nat := [1, 1, 5, 1, 2, 1, 2, 8]
def baseStart_1845095 : Nat := 118140960795 + 1845095 * 2 ^ 59
def prefixEnd_1845095 : Nat := 4983230072969 + 3 ^ 40 * 1845095 * 2
def baseEnd_1845095 : Nat := 140358605660379820892899

theorem tailTrace_1845095 : CollatzResearch.WordTrace tailWord_1845095 prefixEnd_1845095 140358605660379820892899 := by
  unfold tailWord_1845095
  simp only [CollatzResearch.WordTrace]
  refine ⟨67296143250543406983352739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44864095500362271322235159 67296143250543406983352739)
  ·
    refine ⟨100944214875815110475029109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67296143250543406983352739 100944214875815110475029109)
    ·
      refine ⟨9463520144607666607033979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 100944214875815110475029109 9463520144607666607033979)
      ·
        refine ⟨14195280216911499910550969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9463520144607666607033979 14195280216911499910550969)
        ·
          refine ⟨10646460162683624932913227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14195280216911499910550969 10646460162683624932913227)
          ·
            refine ⟨15969690244025437399369841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10646460162683624932913227 15969690244025437399369841)
            ·
              refine ⟨11977267683019078049527381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15969690244025437399369841 11977267683019078049527381)
              ·
                refine ⟨140358605660379820892899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 11977267683019078049527381 140358605660379820892899)
                ·
                  rfl

theorem cell21_1845095_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 2, 8].length) (baseStart_1845095 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1845095 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1845095 prefixEnd_1845095 := by exact prefixLift 1845095
  have htrace : WordTrace (prefixWord ++ tailWord_1845095) baseStart_1845095 baseEnd_1845095 := by
    simpa [prefixWord, tailWord_1845095, baseEnd_1845095] using wordTrace_append hprefix tailTrace_1845095
  have hstable : (prefixWord ++ tailWord_1845095).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1845095).length < 2 ^ (prefixWord ++ tailWord_1845095).sum := by decide
  have hdescent : baseEnd_1845095 < baseStart_1845095 := by decide
  rcases family_descends (prefixWord ++ tailWord_1845095) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1845118 : List Nat := [4, 2, 3, 1, 1, 3, 1, 3, 3]
def baseStart_1845118 : Nat := 118140960795 + 1845118 * 2 ^ 59
def prefixEnd_1845118 : Nat := 4983230072969 + 3 ^ 40 * 1845118 * 2
def baseEnd_1845118 : Nat := 421081065894496533795317

theorem tailTrace_1845118 : CollatzResearch.WordTrace tailWord_1845118 prefixEnd_1845118 421081065894496533795317 := by
  unfold tailWord_1845118
  simp only [CollatzResearch.WordTrace]
  refine ⟨8412122766182510238930001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 44864654752973387940960005 8412122766182510238930001)
  ·
    refine ⟨6309092074636882679197501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8412122766182510238930001 6309092074636882679197501)
    ·
      refine ⟨2365909527988831004699063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6309092074636882679197501 2365909527988831004699063)
      ·
        refine ⟨3548864291983246507048595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2365909527988831004699063 3548864291983246507048595)
        ·
          refine ⟨5323296437974869760572893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3548864291983246507048595 5323296437974869760572893)
          ·
            refine ⟨1996236164240576160214835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5323296437974869760572893 1996236164240576160214835)
            ·
              refine ⟨2994354246360864240322253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1996236164240576160214835 2994354246360864240322253)
              ·
                refine ⟨1122882842385324090120845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2994354246360864240322253 1122882842385324090120845)
                ·
                  refine ⟨421081065894496533795317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1122882842385324090120845 421081065894496533795317)
                  ·
                    rfl

theorem cell21_1845118_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 3, 1, 3, 3].length) (baseStart_1845118 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1845118 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1845118 prefixEnd_1845118 := by exact prefixLift 1845118
  have htrace : WordTrace (prefixWord ++ tailWord_1845118) baseStart_1845118 baseEnd_1845118 := by
    simpa [prefixWord, tailWord_1845118, baseEnd_1845118] using wordTrace_append hprefix tailTrace_1845118
  have hstable : (prefixWord ++ tailWord_1845118).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1845118).length < 2 ^ (prefixWord ++ tailWord_1845118).sum := by decide
  have hdescent : baseEnd_1845118 < baseStart_1845118 := by decide
  rcases family_descends (prefixWord ++ tailWord_1845118) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1845143 : List Nat := [1, 1, 3, 3, 1, 5, 1, 1, 5]
def baseStart_1845143 : Nat := 118140960795 + 1845143 * 2 ^ 59
def prefixEnd_1845143 : Nat := 4983230072969 + 3 ^ 40 * 1845143 * 2
def baseEnd_1845143 : Nat := 421086771235102045878599

theorem tailTrace_1845143 : CollatzResearch.WordTrace tailWord_1845143 prefixEnd_1845143 421086771235102045878599 := by
  unfold tailWord_1845143
  simp only [CollatzResearch.WordTrace]
  refine ⟨67297893954369511181100083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44865262636246340787400055 67297893954369511181100083)
  ·
    refine ⟨100946840931554266771650125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67297893954369511181100083 100946840931554266771650125)
    ·
      refine ⟨37855065349332850039368797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 100946840931554266771650125 37855065349332850039368797)
      ·
        refine ⟨14195649505999818764763299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 37855065349332850039368797 14195649505999818764763299)
        ·
          refine ⟨21293474258999728147144949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14195649505999818764763299 21293474258999728147144949)
          ·
            refine ⟨1996263211781224513794839, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 21293474258999728147144949 1996263211781224513794839)
            ·
              refine ⟨2994394817671836770692259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1996263211781224513794839 2994394817671836770692259)
              ·
                refine ⟨4491592226507755156038389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2994394817671836770692259 4491592226507755156038389)
                ·
                  refine ⟨421086771235102045878599, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4491592226507755156038389 421086771235102045878599)
                  ·
                    rfl

theorem cell21_1845143_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 5, 1, 1, 5].length) (baseStart_1845143 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1845143 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1845143 prefixEnd_1845143 := by exact prefixLift 1845143
  have htrace : WordTrace (prefixWord ++ tailWord_1845143) baseStart_1845143 baseEnd_1845143 := by
    simpa [prefixWord, tailWord_1845143, baseEnd_1845143] using wordTrace_append hprefix tailTrace_1845143
  have hstable : (prefixWord ++ tailWord_1845143).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1845143).length < 2 ^ (prefixWord ++ tailWord_1845143).sum := by decide
  have hdescent : baseEnd_1845143 < baseStart_1845143 := by decide
  rcases family_descends (prefixWord ++ tailWord_1845143) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1845281 : List Nat := [1, 2, 3, 2, 4, 2, 2, 5]
def baseStart_1845281 : Nat := 118140960795 + 1845281 * 2 ^ 59
def prefixEnd_1845281 : Nat := 4983230072969 + 3 ^ 40 * 1845281 * 2
def baseEnd_1845281 : Nat := 140372754905081490859439

theorem tailTrace_1845281 : CollatzResearch.WordTrace tailWord_1845281 prefixEnd_1845281 140372754905081490859439 := by
  unfold tailWord_1845281
  simp only [CollatzResearch.WordTrace]
  refine ⟨67302927227869560749623697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44868618151913040499749131 67302927227869560749623697)
  ·
    refine ⟨50477195420902170562217773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67302927227869560749623697 50477195420902170562217773)
    ·
      refine ⟨18928948282838313960831665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 50477195420902170562217773 18928948282838313960831665)
      ·
        refine ⟨14196711212128735470623749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18928948282838313960831665 14196711212128735470623749)
        ·
          refine ⟨2661883352274137900741953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 14196711212128735470623749 2661883352274137900741953)
          ·
            refine ⟨1996412514205603425556465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2661883352274137900741953 1996412514205603425556465)
            ·
              refine ⟨1497309385654202569167349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1996412514205603425556465 1497309385654202569167349)
              ·
                refine ⟨140372754905081490859439, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1497309385654202569167349 140372754905081490859439)
                ·
                  rfl

theorem cell21_1845281_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 4, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 4, 2, 2, 5].length) (baseStart_1845281 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1845281 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1845281 prefixEnd_1845281 := by exact prefixLift 1845281
  have htrace : WordTrace (prefixWord ++ tailWord_1845281) baseStart_1845281 baseEnd_1845281 := by
    simpa [prefixWord, tailWord_1845281, baseEnd_1845281] using wordTrace_append hprefix tailTrace_1845281
  have hstable : (prefixWord ++ tailWord_1845281).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1845281).length < 2 ^ (prefixWord ++ tailWord_1845281).sum := by decide
  have hdescent : baseEnd_1845281 < baseStart_1845281 := by decide
  rcases family_descends (prefixWord ++ tailWord_1845281) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1845309 : List Nat := [1, 4, 1, 3, 1, 1, 2, 4, 4]
def baseStart_1845309 : Nat := 118140960795 + 1845309 * 2 ^ 59
def prefixEnd_1845309 : Nat := 4983230072969 + 3 ^ 40 * 1845309 * 2
def baseEnd_1845309 : Nat := 421124654696722646111593

theorem tailTrace_1845309 : CollatzResearch.WordTrace tailWord_1845309 prefixEnd_1845309 421124654696722646111593 := by
  unfold tailWord_1845309
  simp only [CollatzResearch.WordTrace]
  refine ⟨67303948471768121531642981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44869298981178747687761987 67303948471768121531642981)
  ·
    refine ⟨12619490338456522787183059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 67303948471768121531642981 12619490338456522787183059)
    ·
      refine ⟨18929235507684784180774589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12619490338456522787183059 18929235507684784180774589)
      ·
        refine ⟨7098463315381794067790471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18929235507684784180774589 7098463315381794067790471)
        ·
          refine ⟨10647694973072691101685707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7098463315381794067790471 10647694973072691101685707)
          ·
            refine ⟨15971542459609036652528561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10647694973072691101685707 15971542459609036652528561)
            ·
              refine ⟨11978656844706777489396421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15971542459609036652528561 11978656844706777489396421)
              ·
                refine ⟨2245998158382520779261829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11978656844706777489396421 2245998158382520779261829)
                ·
                  refine ⟨421124654696722646111593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2245998158382520779261829 421124654696722646111593)
                  ·
                    rfl

theorem cell21_1845309_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 2, 4, 4].length) (baseStart_1845309 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1845309 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1845309 prefixEnd_1845309 := by exact prefixLift 1845309
  have htrace : WordTrace (prefixWord ++ tailWord_1845309) baseStart_1845309 baseEnd_1845309 := by
    simpa [prefixWord, tailWord_1845309, baseEnd_1845309] using wordTrace_append hprefix tailTrace_1845309
  have hstable : (prefixWord ++ tailWord_1845309).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1845309).length < 2 ^ (prefixWord ++ tailWord_1845309).sum := by decide
  have hdescent : baseEnd_1845309 < baseStart_1845309 := by decide
  rcases family_descends (prefixWord ++ tailWord_1845309) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1845312 : List Nat := [2, 1, 1, 2, 2, 5, 3, 2, 3]
def baseStart_1845312 : Nat := 118140960795 + 1845312 * 2 ^ 59
def prefixEnd_1845312 : Nat := 4983230072969 + 3 ^ 40 * 1845312 * 2
def baseEnd_1845312 : Nat := 421125339337595307561587

theorem tailTrace_1845312 : CollatzResearch.WordTrace tailWord_1845312 prefixEnd_1845312 421125339337595307561587 := by
  unfold tailWord_1845312
  simp only [CollatzResearch.WordTrace]
  refine ⟨33652028945378626522001095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44869371927171502029334793 33652028945378626522001095)
  ·
    refine ⟨50478043418067939783001643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33652028945378626522001095 50478043418067939783001643)
    ·
      refine ⟨75717065127101909674502465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50478043418067939783001643 75717065127101909674502465)
      ·
        refine ⟨56787798845326432255876849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 75717065127101909674502465 56787798845326432255876849)
        ·
          refine ⟨42590849133994824191907637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56787798845326432255876849 42590849133994824191907637)
          ·
            refine ⟨3992892106312014767991341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 42590849133994824191907637 3992892106312014767991341)
            ·
              refine ⟨1497334539867005537996753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3992892106312014767991341 1497334539867005537996753)
              ·
                refine ⟨1123000904900254153497565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1497334539867005537996753 1123000904900254153497565)
                ·
                  refine ⟨421125339337595307561587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1123000904900254153497565 421125339337595307561587)
                  ·
                    rfl

theorem cell21_1845312_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 5, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 5, 3, 2, 3].length) (baseStart_1845312 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1845312 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1845312 prefixEnd_1845312 := by exact prefixLift 1845312
  have htrace : WordTrace (prefixWord ++ tailWord_1845312) baseStart_1845312 baseEnd_1845312 := by
    simpa [prefixWord, tailWord_1845312, baseEnd_1845312] using wordTrace_append hprefix tailTrace_1845312
  have hstable : (prefixWord ++ tailWord_1845312).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1845312).length < 2 ^ (prefixWord ++ tailWord_1845312).sum := by decide
  have hdescent : baseEnd_1845312 < baseStart_1845312 := by decide
  rcases family_descends (prefixWord ++ tailWord_1845312) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1845326 : List Nat := [4, 1, 1, 1, 1, 4, 4, 1, 4]
def baseStart_1845326 : Nat := 118140960795 + 1845326 * 2 ^ 59
def prefixEnd_1845326 : Nat := 4983230072969 + 3 ^ 40 * 1845326 * 2
def baseEnd_1845326 : Nat := 421128534328334394328225

theorem tailTrace_1845326 : CollatzResearch.WordTrace tailWord_1845326 prefixEnd_1845326 421128534328334394328225 := by
  unfold tailWord_1845326
  simp only [CollatzResearch.WordTrace]
  refine ⟨8413071064088316679376479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 44869712341804355623341221 8413071064088316679376479)
  ·
    refine ⟨12619606596132475019064719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8413071064088316679376479 12619606596132475019064719)
    ·
      refine ⟨18929409894198712528597079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12619606596132475019064719 18929409894198712528597079)
      ·
        refine ⟨28394114841298068792895619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18929409894198712528597079 28394114841298068792895619)
        ·
          refine ⟨42591172261947103189343429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28394114841298068792895619 42591172261947103189343429)
          ·
            refine ⟨7985844799115081848001893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 42591172261947103189343429 7985844799115081848001893)
            ·
              refine ⟨1497345899834077846500355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7985844799115081848001893 1497345899834077846500355)
              ·
                refine ⟨2246018849751116769750533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1497345899834077846500355 2246018849751116769750533)
                ·
                  refine ⟨421128534328334394328225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2246018849751116769750533 421128534328334394328225)
                  ·
                    rfl

theorem cell21_1845326_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 4, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 4, 4, 1, 4].length) (baseStart_1845326 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1845326 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1845326 prefixEnd_1845326 := by exact prefixLift 1845326
  have htrace : WordTrace (prefixWord ++ tailWord_1845326) baseStart_1845326 baseEnd_1845326 := by
    simpa [prefixWord, tailWord_1845326, baseEnd_1845326] using wordTrace_append hprefix tailTrace_1845326
  have hstable : (prefixWord ++ tailWord_1845326).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1845326).length < 2 ^ (prefixWord ++ tailWord_1845326).sum := by decide
  have hdescent : baseEnd_1845326 < baseStart_1845326 := by decide
  rcases family_descends (prefixWord ++ tailWord_1845326) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1845337 : List Nat := [1, 2, 1, 2, 2, 1, 4, 1, 7]
def baseStart_1845337 : Nat := 118140960795 + 1845337 * 2 ^ 59
def prefixEnd_1845337 : Nat := 4983230072969 + 3 ^ 40 * 1845337 * 2
def baseEnd_1845337 : Nat := 421131044678200819644869

theorem tailTrace_1845337 : CollatzResearch.WordTrace tailWord_1845337 prefixEnd_1845337 421131044678200819644869 := by
  unfold tailWord_1845337
  simp only [CollatzResearch.WordTrace]
  refine ⟨67304969715666682313662265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44869979810444454875774843 67304969715666682313662265)
  ·
    refine ⟨50478727286750011735246699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67304969715666682313662265 50478727286750011735246699)
    ·
      refine ⟨75718090930125017602870049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50478727286750011735246699 75718090930125017602870049)
      ·
        refine ⟨56788568197593763202152537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 75718090930125017602870049 56788568197593763202152537)
        ·
          refine ⟨42591426148195322401614403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56788568197593763202152537 42591426148195322401614403)
          ·
            refine ⟨63887139222292983602421605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42591426148195322401614403 63887139222292983602421605)
            ·
              refine ⟨11978838604179934425454051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 63887139222292983602421605 11978838604179934425454051)
              ·
                refine ⟨17968257906269901638181077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11978838604179934425454051 17968257906269901638181077)
                ·
                  refine ⟨421131044678200819644869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 17968257906269901638181077 421131044678200819644869)
                  ·
                    rfl

theorem cell21_1845337_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 4, 1, 7].length) (baseStart_1845337 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1845337 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1845337 prefixEnd_1845337 := by exact prefixLift 1845337
  have htrace : WordTrace (prefixWord ++ tailWord_1845337) baseStart_1845337 baseEnd_1845337 := by
    simpa [prefixWord, tailWord_1845337, baseEnd_1845337] using wordTrace_append hprefix tailTrace_1845337
  have hstable : (prefixWord ++ tailWord_1845337).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1845337).length < 2 ^ (prefixWord ++ tailWord_1845337).sum := by decide
  have hdescent : baseEnd_1845337 < baseStart_1845337 := by decide
  rcases family_descends (prefixWord ++ tailWord_1845337) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1845413 : List Nat := [1, 3, 1, 2, 1, 3, 1, 2, 7]
def baseStart_1845413 : Nat := 118140960795 + 1845413 * 2 ^ 59
def prefixEnd_1845413 : Nat := 4983230072969 + 3 ^ 40 * 1845413 * 2
def baseEnd_1845413 : Nat := 421148388913641576378047

theorem tailTrace_1845413 : CollatzResearch.WordTrace tailWord_1845413 prefixEnd_1845413 421148388913641576378047 := by
  unfold tailWord_1845413
  simp only [CollatzResearch.WordTrace]
  refine ⟨67307741663391347293428893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44871827775594231528952595 67307741663391347293428893)
  ·
    refine ⟨25240403123771755235035835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 67307741663391347293428893 25240403123771755235035835)
    ·
      refine ⟨37860604685657632852553753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25240403123771755235035835 37860604685657632852553753)
      ·
        refine ⟨28395453514243224639415315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37860604685657632852553753 28395453514243224639415315)
        ·
          refine ⟨42593180271364836959122973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28395453514243224639415315 42593180271364836959122973)
          ·
            refine ⟨15972442601761813859671115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 42593180271364836959122973 15972442601761813859671115)
            ·
              refine ⟨23958663902642720789506673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15972442601761813859671115 23958663902642720789506673)
              ·
                refine ⟨17968997926982040592130005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23958663902642720789506673 17968997926982040592130005)
                ·
                  refine ⟨421148388913641576378047, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 17968997926982040592130005 421148388913641576378047)
                  ·
                    rfl

theorem cell21_1845413_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 1, 2, 7].length) (baseStart_1845413 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1845413 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1845413 prefixEnd_1845413 := by exact prefixLift 1845413
  have htrace : WordTrace (prefixWord ++ tailWord_1845413) baseStart_1845413 baseEnd_1845413 := by
    simpa [prefixWord, tailWord_1845413, baseEnd_1845413] using wordTrace_append hprefix tailTrace_1845413
  have hstable : (prefixWord ++ tailWord_1845413).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1845413).length < 2 ^ (prefixWord ++ tailWord_1845413).sum := by decide
  have hdescent : baseEnd_1845413 < baseStart_1845413 := by decide
  rcases family_descends (prefixWord ++ tailWord_1845413) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1845464 : List Nat := [2, 1, 2, 2, 4, 3, 1, 3, 3]
def baseStart_1845464 : Nat := 118140960795 + 1845464 * 2 ^ 59
def prefixEnd_1845464 : Nat := 4983230072969 + 3 ^ 40 * 1845464 * 2
def baseEnd_1845464 : Nat := 421160027808476821027943

theorem tailTrace_1845464 : CollatzResearch.WordTrace tailWord_1845464 prefixEnd_1845464 421160027808476821027943 := by
  unfold tailWord_1845464
  simp only [CollatzResearch.WordTrace]
  refine ⟨33654800893103291501767723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44873067857471055335690297 33654800893103291501767723)
  ·
    refine ⟨50482201339654937252651585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33654800893103291501767723 50482201339654937252651585)
    ·
      refine ⟨37861651004741202939488689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50482201339654937252651585 37861651004741202939488689)
      ·
        refine ⟨28396238253555902204616517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37861651004741202939488689 28396238253555902204616517)
        ·
          refine ⟨5324294672541731663365597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 28396238253555902204616517 5324294672541731663365597)
          ·
            refine ⟨1996610502203149373762099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5324294672541731663365597 1996610502203149373762099)
            ·
              refine ⟨2994915753304724060643149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1996610502203149373762099 2994915753304724060643149)
              ·
                refine ⟨1123093407489271522741181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2994915753304724060643149 1123093407489271522741181)
                ·
                  refine ⟨421160027808476821027943, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1123093407489271522741181 421160027808476821027943)
                  ·
                    rfl

theorem cell21_1845464_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 3, 1, 3, 3].length) (baseStart_1845464 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1845464 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1845464 prefixEnd_1845464 := by exact prefixLift 1845464
  have htrace : WordTrace (prefixWord ++ tailWord_1845464) baseStart_1845464 baseEnd_1845464 := by
    simpa [prefixWord, tailWord_1845464, baseEnd_1845464] using wordTrace_append hprefix tailTrace_1845464
  have hstable : (prefixWord ++ tailWord_1845464).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1845464).length < 2 ^ (prefixWord ++ tailWord_1845464).sum := by decide
  have hdescent : baseEnd_1845464 < baseStart_1845464 := by decide
  rcases family_descends (prefixWord ++ tailWord_1845464) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1845540 : List Nat := [2, 3, 1, 3, 1, 2, 4, 2, 3]
def baseStart_1845540 : Nat := 118140960795 + 1845540 * 2 ^ 59
def prefixEnd_1845540 : Nat := 4983230072969 + 3 ^ 40 * 1845540 * 2
def baseEnd_1845540 : Nat := 421177372043917577761121

theorem tailTrace_1845540 : CollatzResearch.WordTrace tailWord_1845540 prefixEnd_1845540 421177372043917577761121 := by
  unfold tailWord_1845540
  simp only [CollatzResearch.WordTrace]
  refine ⟨33656186866965623991651037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44874915822620831988868049 33656186866965623991651037)
  ·
    refine ⟨12621070075112108996869139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 33656186866965623991651037 12621070075112108996869139)
    ·
      refine ⟨18931605112668163495303709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12621070075112108996869139 18931605112668163495303709)
      ·
        refine ⟨7099351917250561310738891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18931605112668163495303709 7099351917250561310738891)
        ·
          refine ⟨10649027875875841966108337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7099351917250561310738891 10649027875875841966108337)
          ·
            refine ⟨7986770906906881474581253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10649027875875841966108337 7986770906906881474581253)
            ·
              refine ⟨1497519545045040276483985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7986770906906881474581253 1497519545045040276483985)
              ·
                refine ⟨1123139658783780207362989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1497519545045040276483985 1123139658783780207362989)
                ·
                  refine ⟨421177372043917577761121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1123139658783780207362989 421177372043917577761121)
                  ·
                    rfl

theorem cell21_1845540_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 2, 4, 2, 3].length) (baseStart_1845540 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1845540 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1845540 prefixEnd_1845540 := by exact prefixLift 1845540
  have htrace : WordTrace (prefixWord ++ tailWord_1845540) baseStart_1845540 baseEnd_1845540 := by
    simpa [prefixWord, tailWord_1845540, baseEnd_1845540] using wordTrace_append hprefix tailTrace_1845540
  have hstable : (prefixWord ++ tailWord_1845540).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1845540).length < 2 ^ (prefixWord ++ tailWord_1845540).sum := by decide
  have hdescent : baseEnd_1845540 < baseStart_1845540 := by decide
  rcases family_descends (prefixWord ++ tailWord_1845540) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1845543 : List Nat := [1, 1, 8, 1, 2, 1, 1, 6]
def baseStart_1845543 : Nat := 118140960795 + 1845543 * 2 ^ 59
def prefixEnd_1845543 : Nat := 4983230072969 + 3 ^ 40 * 1845543 * 2
def baseEnd_1845543 : Nat := 140392685561596746403705

theorem tailTrace_1845543 : CollatzResearch.WordTrace tailWord_1845543 prefixEnd_1845543 140392685561596746403705 := by
  unfold tailWord_1845543
  simp only [CollatzResearch.WordTrace]
  refine ⟨67312483152920379495661283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44874988768613586330440855 67312483152920379495661283)
  ·
    refine ⟨100968724729380569243491925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67312483152920379495661283 100968724729380569243491925)
    ·
      refine ⟨1183227242922428545822171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 8 100968724729380569243491925 1183227242922428545822171)
      ·
        refine ⟨1774840864383642818733257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1183227242922428545822171 1774840864383642818733257)
        ·
          refine ⟨1331130648287732114049943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1774840864383642818733257 1331130648287732114049943)
          ·
            refine ⟨1996695972431598171074915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1331130648287732114049943 1996695972431598171074915)
            ·
              refine ⟨2995043958647397256612373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1996695972431598171074915 2995043958647397256612373)
              ·
                refine ⟨140392685561596746403705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2995043958647397256612373 140392685561596746403705)
                ·
                  rfl

theorem cell21_1845543_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 8, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 8, 1, 2, 1, 1, 6].length) (baseStart_1845543 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1845543 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1845543 prefixEnd_1845543 := by exact prefixLift 1845543
  have htrace : WordTrace (prefixWord ++ tailWord_1845543) baseStart_1845543 baseEnd_1845543 := by
    simpa [prefixWord, tailWord_1845543, baseEnd_1845543] using wordTrace_append hprefix tailTrace_1845543
  have hstable : (prefixWord ++ tailWord_1845543).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1845543).length < 2 ^ (prefixWord ++ tailWord_1845543).sum := by decide
  have hdescent : baseEnd_1845543 < baseStart_1845543 := by decide
  rcases family_descends (prefixWord ++ tailWord_1845543) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1845627 : List Nat := [1, 1, 1, 1, 1, 7, 4, 5]
def baseStart_1845627 : Nat := 118140960795 + 1845627 * 2 ^ 59
def prefixEnd_1845627 : Nat := 4983230072969 + 3 ^ 40 * 1845627 * 2
def baseEnd_1845627 : Nat := 140399075543074919936981

theorem tailTrace_1845627 : CollatzResearch.WordTrace tailWord_1845627 prefixEnd_1845627 140399075543074919936981 := by
  unfold tailWord_1845627
  simp only [CollatzResearch.WordTrace]
  refine ⟨67315546884616061841719135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44877031256410707894479423 67315546884616061841719135)
  ·
    refine ⟨100973320326924092762578703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67315546884616061841719135 100973320326924092762578703)
    ·
      refine ⟨151459980490386139143868055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100973320326924092762578703 151459980490386139143868055)
      ·
        refine ⟨227189970735579208715802083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 151459980490386139143868055 227189970735579208715802083)
        ·
          refine ⟨340784956103368813073703125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 227189970735579208715802083 340784956103368813073703125)
          ·
            refine ⟨7987147408672706556414917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 340784956103368813073703125 7987147408672706556414917)
            ·
              refine ⟨1497590139126132479327797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7987147408672706556414917 1497590139126132479327797)
              ·
                refine ⟨140399075543074919936981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1497590139126132479327797 140399075543074919936981)
                ·
                  rfl

theorem cell21_1845627_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 7, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 7, 4, 5].length) (baseStart_1845627 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1845627 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1845627 prefixEnd_1845627 := by exact prefixLift 1845627
  have htrace : WordTrace (prefixWord ++ tailWord_1845627) baseStart_1845627 baseEnd_1845627 := by
    simpa [prefixWord, tailWord_1845627, baseEnd_1845627] using wordTrace_append hprefix tailTrace_1845627
  have hstable : (prefixWord ++ tailWord_1845627).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1845627).length < 2 ^ (prefixWord ++ tailWord_1845627).sum := by decide
  have hdescent : baseEnd_1845627 < baseStart_1845627 := by decide
  rcases family_descends (prefixWord ++ tailWord_1845627) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1845658 : List Nat := [3, 1, 1, 4, 1, 2, 3, 1, 5]
def baseStart_1845658 : Nat := 118140960795 + 1845658 * 2 ^ 59
def prefixEnd_1845658 : Nat := 4983230072969 + 3 ^ 40 * 1845658 * 2
def baseEnd_1845658 : Nat := 421204301251575594794213

theorem tailTrace_1845658 : CollatzResearch.WordTrace tailWord_1845658 prefixEnd_1845658 421204301251575594794213 := by
  unfold tailWord_1845658
  simp only [CollatzResearch.WordTrace]
  refine ⟨16829169386875938534024407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 44877785031669169424065085 16829169386875938534024407)
  ·
    refine ⟨25243754080313907801036611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16829169386875938534024407 25243754080313907801036611)
    ·
      refine ⟨37865631120470861701554917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25243754080313907801036611 37865631120470861701554917)
      ·
        refine ⟨7099805835088286569041547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 37865631120470861701554917 7099805835088286569041547)
        ·
          refine ⟨10649708752632429853562321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7099805835088286569041547 10649708752632429853562321)
          ·
            refine ⟨7987281564474322390171741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10649708752632429853562321 7987281564474322390171741)
            ·
              refine ⟨2995230586677870896314403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7987281564474322390171741 2995230586677870896314403)
              ·
                refine ⟨4492845880016806344471605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2995230586677870896314403 4492845880016806344471605)
                ·
                  refine ⟨421204301251575594794213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4492845880016806344471605 421204301251575594794213)
                  ·
                    rfl

theorem cell21_1845658_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 2, 3, 1, 5].length) (baseStart_1845658 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1845658 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1845658 prefixEnd_1845658 := by exact prefixLift 1845658
  have htrace : WordTrace (prefixWord ++ tailWord_1845658) baseStart_1845658 baseEnd_1845658 := by
    simpa [prefixWord, tailWord_1845658, baseEnd_1845658] using wordTrace_append hprefix tailTrace_1845658
  have hstable : (prefixWord ++ tailWord_1845658).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1845658).length < 2 ^ (prefixWord ++ tailWord_1845658).sum := by decide
  have hdescent : baseEnd_1845658 < baseStart_1845658 := by decide
  rcases family_descends (prefixWord ++ tailWord_1845658) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1845793 : List Nat := [1, 2, 3, 2, 2, 1, 1, 4, 5]
def baseStart_1845793 : Nat := 118140960795 + 1845793 * 2 ^ 59
def prefixEnd_1845793 : Nat := 4983230072969 + 3 ^ 40 * 1845793 * 2
def baseEnd_1845793 : Nat := 421235110090845360043937

theorem tailTrace_1845793 : CollatzResearch.WordTrace tailWord_1845793 prefixEnd_1845793 421235110090845360043937 := by
  unfold tailWord_1845793
  simp only [CollatzResearch.WordTrace]
  refine ⟨67321601402014672192262033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44881067601343114794841355 67321601402014672192262033)
  ·
    refine ⟨50491201051511004144196525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67321601402014672192262033 50491201051511004144196525)
    ·
      refine ⟨18934200394316626554073697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 50491201051511004144196525 18934200394316626554073697)
      ·
        refine ⟨14200650295737469915555273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18934200394316626554073697 14200650295737469915555273)
        ·
          refine ⟨10650487721803102436666455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14200650295737469915555273 10650487721803102436666455)
          ·
            refine ⟨15975731582704653654999683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10650487721803102436666455 15975731582704653654999683)
            ·
              refine ⟨23963597374056980482499525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15975731582704653654999683 23963597374056980482499525)
              ·
                refine ⟨4493174507635683840468661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 23963597374056980482499525 4493174507635683840468661)
                ·
                  refine ⟨421235110090845360043937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4493174507635683840468661 421235110090845360043937)
                  ·
                    rfl

theorem cell21_1845793_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 1, 4, 5].length) (baseStart_1845793 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1845793 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1845793 prefixEnd_1845793 := by exact prefixLift 1845793
  have htrace : WordTrace (prefixWord ++ tailWord_1845793) baseStart_1845793 baseEnd_1845793 := by
    simpa [prefixWord, tailWord_1845793, baseEnd_1845793] using wordTrace_append hprefix tailTrace_1845793
  have hstable : (prefixWord ++ tailWord_1845793).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1845793).length < 2 ^ (prefixWord ++ tailWord_1845793).sum := by decide
  have hdescent : baseEnd_1845793 < baseStart_1845793 := by decide
  rcases family_descends (prefixWord ++ tailWord_1845793) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1845796 : List Nat := [2, 3, 1, 5, 1, 1, 1, 7]
def baseStart_1845796 : Nat := 118140960795 + 1845796 * 2 ^ 59
def prefixEnd_1845796 : Nat := 4983230072969 + 3 ^ 40 * 1845796 * 2
def baseEnd_1845796 : Nat := 140411931577239340497977

theorem tailTrace_1845796 : CollatzResearch.WordTrace tailWord_1845796 prefixEnd_1845796 140411931577239340497977 := by
  unfold tailWord_1845796
  simp only [CollatzResearch.WordTrace]
  refine ⟨33660855410501901852310621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44881140547335869136414161 33660855410501901852310621)
  ·
    refine ⟨12622820778938213194616483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 33660855410501901852310621 12622820778938213194616483)
    ·
      refine ⟨18934231168407319791924725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12622820778938213194616483 18934231168407319791924725)
      ·
        refine ⟨1775084172038186230492943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 18934231168407319791924725 1775084172038186230492943)
        ·
          refine ⟨2662626258057279345739415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1775084172038186230492943 2662626258057279345739415)
          ·
            refine ⟨3993939387085919018609123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2662626258057279345739415 3993939387085919018609123)
            ·
              refine ⟨5990909080628878527913685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3993939387085919018609123 5990909080628878527913685)
              ·
                refine ⟨140411931577239340497977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5990909080628878527913685 140411931577239340497977)
                ·
                  rfl

theorem cell21_1845796_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 5, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 5, 1, 1, 1, 7].length) (baseStart_1845796 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1845796 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1845796 prefixEnd_1845796 := by exact prefixLift 1845796
  have htrace : WordTrace (prefixWord ++ tailWord_1845796) baseStart_1845796 baseEnd_1845796 := by
    simpa [prefixWord, tailWord_1845796, baseEnd_1845796] using wordTrace_append hprefix tailTrace_1845796
  have hstable : (prefixWord ++ tailWord_1845796).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1845796).length < 2 ^ (prefixWord ++ tailWord_1845796).sum := by decide
  have hdescent : baseEnd_1845796 < baseStart_1845796 := by decide
  rcases family_descends (prefixWord ++ tailWord_1845796) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1845838 : List Nat := [4, 1, 1, 1, 1, 2, 3, 8]
def baseStart_1845838 : Nat := 118140960795 + 1845838 * 2 ^ 59
def prefixEnd_1845838 : Nat := 4983230072969 + 3 ^ 40 * 1845838 * 2
def baseEnd_1845838 : Nat := 140415126567978427264615

theorem tailTrace_1845838 : CollatzResearch.WordTrace tailWord_1845838 prefixEnd_1845838 140415126567978427264615 := by
  unfold tailWord_1845838
  simp only [CollatzResearch.WordTrace]
  refine ⟨8415405335856455609706271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 44882161791234429918433445 8415405335856455609706271)
  ·
    refine ⟨12623108003784683414559407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8415405335856455609706271 12623108003784683414559407)
    ·
      refine ⟨18934662005677025121839111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12623108003784683414559407 18934662005677025121839111)
      ·
        refine ⟨28401993008515537682758667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18934662005677025121839111 28401993008515537682758667)
        ·
          refine ⟨42602989512773306524138001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28401993008515537682758667 42602989512773306524138001)
          ·
            refine ⟨31952242134579979893103501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42602989512773306524138001 31952242134579979893103501)
            ·
              refine ⟨11982090800467492459913813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31952242134579979893103501 11982090800467492459913813)
              ·
                refine ⟨140415126567978427264615, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 11982090800467492459913813 140415126567978427264615)
                ·
                  rfl

theorem cell21_1845838_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 3, 8].length) (baseStart_1845838 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1845838 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1845838 prefixEnd_1845838 := by exact prefixLift 1845838
  have htrace : WordTrace (prefixWord ++ tailWord_1845838) baseStart_1845838 baseEnd_1845838 := by
    simpa [prefixWord, tailWord_1845838, baseEnd_1845838] using wordTrace_append hprefix tailTrace_1845838
  have hstable : (prefixWord ++ tailWord_1845838).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1845838).length < 2 ^ (prefixWord ++ tailWord_1845838).sum := by decide
  have hdescent : baseEnd_1845838 < baseStart_1845838 := by decide
  rcases family_descends (prefixWord ++ tailWord_1845838) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1845841 : List Nat := [1, 2, 2, 1, 3, 3, 4, 1, 4]
def baseStart_1845841 : Nat := 118140960795 + 1845841 * 2 ^ 59
def prefixEnd_1845841 : Nat := 4983230072969 + 3 ^ 40 * 1845841 * 2
def baseEnd_1845841 : Nat := 421246064344807943243839

theorem tailTrace_1845841 : CollatzResearch.WordTrace tailWord_1845841 prefixEnd_1845841 421246064344807943243839 := by
  unfold tailWord_1845841
  simp only [CollatzResearch.WordTrace]
  refine ⟨67323352105840776390009377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44882234737227184260006251 67323352105840776390009377)
  ·
    refine ⟨50492514079380582292507033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67323352105840776390009377 50492514079380582292507033)
    ·
      refine ⟨37869385559535436719380275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50492514079380582292507033 37869385559535436719380275)
      ·
        refine ⟨56804078339303155079070413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37869385559535436719380275 56804078339303155079070413)
        ·
          refine ⟨21301529377238683154651405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 56804078339303155079070413 21301529377238683154651405)
          ·
            refine ⟨7988073516464506182994277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21301529377238683154651405 7988073516464506182994277)
            ·
              refine ⟨1497763784337094909311427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7988073516464506182994277 1497763784337094909311427)
              ·
                refine ⟨2246645676505642363967141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1497763784337094909311427 2246645676505642363967141)
                ·
                  refine ⟨421246064344807943243839, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2246645676505642363967141 421246064344807943243839)
                  ·
                    rfl

theorem cell21_1845841_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 3, 4, 1, 4].length) (baseStart_1845841 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1845841 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1845841 prefixEnd_1845841 := by exact prefixLift 1845841
  have htrace : WordTrace (prefixWord ++ tailWord_1845841) baseStart_1845841 baseEnd_1845841 := by
    simpa [prefixWord, tailWord_1845841, baseEnd_1845841] using wordTrace_append hprefix tailTrace_1845841
  have hstable : (prefixWord ++ tailWord_1845841).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1845841).length < 2 ^ (prefixWord ++ tailWord_1845841).sum := by decide
  have hdescent : baseEnd_1845841 < baseStart_1845841 := by decide
  rcases family_descends (prefixWord ++ tailWord_1845841) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1845878 : List Nat := [5, 1, 1, 2, 4, 1, 2, 2, 3]
def baseStart_1845878 : Nat := 118140960795 + 1845878 * 2 ^ 59
def prefixEnd_1845878 : Nat := 4983230072969 + 3 ^ 40 * 1845878 * 2
def baseEnd_1845878 : Nat := 421254508248904101127097

theorem tailTrace_1845878 : CollatzResearch.WordTrace tailWord_1845878 prefixEnd_1845878 421254508248904101127097 := by
  unfold tailWord_1845878
  simp only [CollatzResearch.WordTrace]
  refine ⟨4207793850419170731819143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 44883134404471154472737525 4207793850419170731819143)
  ·
    refine ⟨6311690775628756097728715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4207793850419170731819143 6311690775628756097728715)
    ·
      refine ⟨9467536163443134146593073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6311690775628756097728715 9467536163443134146593073)
      ·
        refine ⟨7100652122582350609944805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9467536163443134146593073 7100652122582350609944805)
        ·
          refine ⟨1331372272984190739364651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7100652122582350609944805 1331372272984190739364651)
          ·
            refine ⟨1997058409476286109046977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1331372272984190739364651 1997058409476286109046977)
            ·
              refine ⟨1497793807107214581785233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1997058409476286109046977 1497793807107214581785233)
              ·
                refine ⟨1123345355330410936338925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1497793807107214581785233 1123345355330410936338925)
                ·
                  refine ⟨421254508248904101127097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1123345355330410936338925 421254508248904101127097)
                  ·
                    rfl

theorem cell21_1845878_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 4, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 4, 1, 2, 2, 3].length) (baseStart_1845878 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1845878 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1845878 prefixEnd_1845878 := by exact prefixLift 1845878
  have htrace : WordTrace (prefixWord ++ tailWord_1845878) baseStart_1845878 baseEnd_1845878 := by
    simpa [prefixWord, tailWord_1845878, baseEnd_1845878] using wordTrace_append hprefix tailTrace_1845878
  have hstable : (prefixWord ++ tailWord_1845878).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1845878).length < 2 ^ (prefixWord ++ tailWord_1845878).sum := by decide
  have hdescent : baseEnd_1845878 < baseStart_1845878 := by decide
  rcases family_descends (prefixWord ++ tailWord_1845878) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1845934 : List Nat := [4, 1, 4, 1, 1, 1, 3, 2, 4]
def baseStart_1845934 : Nat := 118140960795 + 1845934 * 2 ^ 59
def prefixEnd_1845934 : Nat := 4983230072969 + 3 ^ 40 * 1845934 * 2
def baseEnd_1845934 : Nat := 421267288211860448193649

theorem tailTrace_1845934 : CollatzResearch.WordTrace tailWord_1845934 prefixEnd_1845934 421267288211860448193649 := by
  unfold tailWord_1845934
  simp only [CollatzResearch.WordTrace]
  refine ⟨8415843011812981659143107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 44884496063002568848763237 8415843011812981659143107)
  ·
    refine ⟨12623764517719472488714661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8415843011812981659143107 12623764517719472488714661)
    ·
      refine ⟨2366955847072401091633999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 12623764517719472488714661 2366955847072401091633999)
      ·
        refine ⟨3550433770608601637450999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2366955847072401091633999 3550433770608601637450999)
        ·
          refine ⟨5325650655912902456176499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3550433770608601637450999 5325650655912902456176499)
          ·
            refine ⟨7988475983869353684264749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5325650655912902456176499 7988475983869353684264749)
            ·
              refine ⟨2995678493951007631599281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7988475983869353684264749 2995678493951007631599281)
              ·
                refine ⟨2246758870463255723699461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2995678493951007631599281 2246758870463255723699461)
                ·
                  refine ⟨421267288211860448193649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2246758870463255723699461 421267288211860448193649)
                  ·
                    rfl

theorem cell21_1845934_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 1, 3, 2, 4].length) (baseStart_1845934 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1845934 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1845934 prefixEnd_1845934 := by exact prefixLift 1845934
  have htrace : WordTrace (prefixWord ++ tailWord_1845934) baseStart_1845934 baseEnd_1845934 := by
    simpa [prefixWord, tailWord_1845934, baseEnd_1845934] using wordTrace_append hprefix tailTrace_1845934
  have hstable : (prefixWord ++ tailWord_1845934).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1845934).length < 2 ^ (prefixWord ++ tailWord_1845934).sum := by decide
  have hdescent : baseEnd_1845934 < baseStart_1845934 := by decide
  rcases family_descends (prefixWord ++ tailWord_1845934) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1846111 : List Nat := [1, 1, 2, 3, 1, 3, 3, 1, 6]
def baseStart_1846111 : Nat := 118140960795 + 1846111 * 2 ^ 59
def prefixEnd_1846111 : Nat := 4983230072969 + 3 ^ 40 * 1846111 * 2
def baseEnd_1846111 : Nat := 421307682023347473743287

theorem tailTrace_1846111 : CollatzResearch.WordTrace tailWord_1846111 prefixEnd_1846111 421307682023347473743287 := by
  unfold tailWord_1846111
  simp only [CollatzResearch.WordTrace]
  refine ⟨67333199814862612502338187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44888799876575075001558791 67333199814862612502338187)
  ·
    refine ⟨100999799722293918753507281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67333199814862612502338187 100999799722293918753507281)
    ·
      refine ⟨75749849791720439065130461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 100999799722293918753507281 75749849791720439065130461)
      ·
        refine ⟨28406193671895164649423923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 75749849791720439065130461 28406193671895164649423923)
        ·
          refine ⟨42609290507842746974135885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28406193671895164649423923 42609290507842746974135885)
          ·
            refine ⟨15978483940441030115300957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 42609290507842746974135885 15978483940441030115300957)
            ·
              refine ⟨5991931477665386293237859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15978483940441030115300957 5991931477665386293237859)
              ·
                refine ⟨8987897216498079439856789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5991931477665386293237859 8987897216498079439856789)
                ·
                  refine ⟨421307682023347473743287, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8987897216498079439856789 421307682023347473743287)
                  ·
                    rfl

theorem cell21_1846111_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 3, 1, 6].length) (baseStart_1846111 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1846111 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1846111 prefixEnd_1846111 := by exact prefixLift 1846111
  have htrace : WordTrace (prefixWord ++ tailWord_1846111) baseStart_1846111 baseEnd_1846111 := by
    simpa [prefixWord, tailWord_1846111, baseEnd_1846111] using wordTrace_append hprefix tailTrace_1846111
  have hstable : (prefixWord ++ tailWord_1846111).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1846111).length < 2 ^ (prefixWord ++ tailWord_1846111).sum := by decide
  have hdescent : baseEnd_1846111 < baseStart_1846111 := by decide
  rcases family_descends (prefixWord ++ tailWord_1846111) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1846156 : List Nat := [2, 2, 1, 2, 1, 2, 2, 2, 7]
def baseStart_1846156 : Nat := 118140960795 + 1846156 * 2 ^ 59
def prefixEnd_1846156 : Nat := 4983230072969 + 3 ^ 40 * 1846156 * 2
def baseEnd_1846156 : Nat := 421317951636437395493195

theorem tailTrace_1846156 : CollatzResearch.WordTrace tailWord_1846156 prefixEnd_1846156 421317951636437395493195 := by
  unfold tailWord_1846156
  simp only [CollatzResearch.WordTrace]
  refine ⟨33667420549849792593863161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44889894066466390125150881 33667420549849792593863161)
  ·
    refine ⟨25250565412387344445397371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33667420549849792593863161 25250565412387344445397371)
    ·
      refine ⟨37875848118581016668096057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25250565412387344445397371 37875848118581016668096057)
      ·
        refine ⟨28406886088935762501072043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37875848118581016668096057 28406886088935762501072043)
        ·
          refine ⟨42610329133403643751608065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28406886088935762501072043 42610329133403643751608065)
          ·
            refine ⟨31957746850052732813706049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42610329133403643751608065 31957746850052732813706049)
            ·
              refine ⟨23968310137539549610279537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31957746850052732813706049 23968310137539549610279537)
              ·
                refine ⟨17976232603154662207709653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23968310137539549610279537 17976232603154662207709653)
                ·
                  refine ⟨421317951636437395493195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 17976232603154662207709653 421317951636437395493195)
                  ·
                    rfl

theorem cell21_1846156_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 2, 2, 7].length) (baseStart_1846156 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1846156 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1846156 prefixEnd_1846156 := by exact prefixLift 1846156
  have htrace : WordTrace (prefixWord ++ tailWord_1846156) baseStart_1846156 baseEnd_1846156 := by
    simpa [prefixWord, tailWord_1846156, baseEnd_1846156] using wordTrace_append hprefix tailTrace_1846156
  have hstable : (prefixWord ++ tailWord_1846156).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1846156).length < 2 ^ (prefixWord ++ tailWord_1846156).sum := by decide
  have hdescent : baseEnd_1846156 < baseStart_1846156 := by decide
  rcases family_descends (prefixWord ++ tailWord_1846156) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1846187 : List Nat := [1, 1, 1, 1, 2, 1, 1, 9, 4]
def baseStart_1846187 : Nat := 118140960795 + 1846187 * 2 ^ 59
def prefixEnd_1846187 : Nat := 4983230072969 + 3 ^ 40 * 1846187 * 2
def baseEnd_1846187 : Nat := 421325026258788230476465

theorem tailTrace_1846187 : CollatzResearch.WordTrace tailWord_1846187 prefixEnd_1846187 421325026258788230476465 := by
  unfold tailWord_1846187
  simp only [CollatzResearch.WordTrace]
  refine ⟨67335971762587277482104815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44890647841724851654736543 67335971762587277482104815)
  ·
    refine ⟨101003957643880916223157223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67335971762587277482104815 101003957643880916223157223)
    ·
      refine ⟨151505936465821374334735835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101003957643880916223157223 151505936465821374334735835)
      ·
        refine ⟨227258904698732061502103753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 151505936465821374334735835 227258904698732061502103753)
        ·
          refine ⟨170444178524049046126577815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 227258904698732061502103753 170444178524049046126577815)
          ·
            refine ⟨255666267786073569189866723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 170444178524049046126577815 255666267786073569189866723)
            ·
              refine ⟨383499401679110353784800085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 255666267786073569189866723 383499401679110353784800085)
              ·
                refine ⟨2247066806713537229207813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 383499401679110353784800085 2247066806713537229207813)
                ·
                  refine ⟨421325026258788230476465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2247066806713537229207813 421325026258788230476465)
                  ·
                    rfl

theorem cell21_1846187_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 9, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 9, 4].length) (baseStart_1846187 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1846187 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1846187 prefixEnd_1846187 := by exact prefixLift 1846187
  have htrace : WordTrace (prefixWord ++ tailWord_1846187) baseStart_1846187 baseEnd_1846187 := by
    simpa [prefixWord, tailWord_1846187, baseEnd_1846187] using wordTrace_append hprefix tailTrace_1846187
  have hstable : (prefixWord ++ tailWord_1846187).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1846187).length < 2 ^ (prefixWord ++ tailWord_1846187).sum := by decide
  have hdescent : baseEnd_1846187 < baseStart_1846187 := by decide
  rcases family_descends (prefixWord ++ tailWord_1846187) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1846277 : List Nat := [1, 3, 1, 1, 2, 3, 10]
def baseStart_1846277 : Nat := 118140960795 + 1846277 * 2 ^ 59
def prefixEnd_1846277 : Nat := 4983230072969 + 3 ^ 40 * 1846277 * 2
def baseEnd_1846277 : Nat := 46816173942774230441809

theorem tailTrace_1846277 : CollatzResearch.WordTrace tailWord_1846277 prefixEnd_1846277 46816173942774230441809 := by
  unfold tailWord_1846277
  simp only [CollatzResearch.WordTrace]
  refine ⟨67339254332261222852881085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44892836221507481901920723 67339254332261222852881085)
  ·
    refine ⟨25252220374597958569830407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 67339254332261222852881085 25252220374597958569830407)
    ·
      refine ⟨37878330561896937854745611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25252220374597958569830407 37878330561896937854745611)
      ·
        refine ⟨56817495842845406782118417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37878330561896937854745611 56817495842845406782118417)
        ·
          refine ⟨42613121882134055086588813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56817495842845406782118417 42613121882134055086588813)
          ·
            refine ⟨15979920705800270657470805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 42613121882134055086588813 15979920705800270657470805)
            ·
              refine ⟨46816173942774230441809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 15979920705800270657470805 46816173942774230441809)
              ·
                rfl

theorem cell21_1846277_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 10].length) (baseStart_1846277 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1846277 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1846277 prefixEnd_1846277 := by exact prefixLift 1846277
  have htrace : WordTrace (prefixWord ++ tailWord_1846277) baseStart_1846277 baseEnd_1846277 := by
    simpa [prefixWord, tailWord_1846277, baseEnd_1846277] using wordTrace_append hprefix tailTrace_1846277
  have hstable : (prefixWord ++ tailWord_1846277).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1846277).length < 2 ^ (prefixWord ++ tailWord_1846277).sum := by decide
  have hdescent : baseEnd_1846277 < baseStart_1846277 := by decide
  rcases family_descends (prefixWord ++ tailWord_1846277) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1846280 : List Nat := [2, 1, 3, 2, 1, 3, 3, 2, 4]
def baseStart_1846280 : Nat := 118140960795 + 1846280 * 2 ^ 59
def prefixEnd_1846280 : Nat := 4983230072969 + 3 ^ 40 * 1846280 * 2
def baseEnd_1846280 : Nat := 421346250125840735426275

theorem tailTrace_1846280 : CollatzResearch.WordTrace tailWord_1846280 prefixEnd_1846280 421346250125840735426275 := by
  unfold tailWord_1846280
  simp only [CollatzResearch.WordTrace]
  refine ⟨33669681875625177182620147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44892909167500236243493529 33669681875625177182620147)
  ·
    refine ⟨50504522813437765773930221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33669681875625177182620147 50504522813437765773930221)
    ·
      refine ⟨18939196055039162165223833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 50504522813437765773930221 18939196055039162165223833)
      ·
        refine ⟨14204397041279371623917875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18939196055039162165223833 14204397041279371623917875)
        ·
          refine ⟨21306595561919057435876813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14204397041279371623917875 21306595561919057435876813)
          ·
            refine ⟨7989973335719646538453805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21306595561919057435876813 7989973335719646538453805)
            ·
              refine ⟨2996240000894867451920177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7989973335719646538453805 2996240000894867451920177)
              ·
                refine ⟨2247180000671150588940133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2996240000894867451920177 2247180000671150588940133)
                ·
                  refine ⟨421346250125840735426275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2247180000671150588940133 421346250125840735426275)
                  ·
                    rfl

theorem cell21_1846280_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 3, 3, 2, 4].length) (baseStart_1846280 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1846280 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1846280 prefixEnd_1846280 := by exact prefixLift 1846280
  have htrace : WordTrace (prefixWord ++ tailWord_1846280) baseStart_1846280 baseEnd_1846280 := by
    simpa [prefixWord, tailWord_1846280, baseEnd_1846280] using wordTrace_append hprefix tailTrace_1846280
  have hstable : (prefixWord ++ tailWord_1846280).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1846280).length < 2 ^ (prefixWord ++ tailWord_1846280).sum := by decide
  have hdescent : baseEnd_1846280 < baseStart_1846280 := by decide
  rcases family_descends (prefixWord ++ tailWord_1846280) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1846311 : List Nat := [1, 1, 7, 1, 1, 2, 1, 7]
def baseStart_1846311 : Nat := 118140960795 + 1846311 * 2 ^ 59
def prefixEnd_1846311 : Nat := 4983230072969 + 3 ^ 40 * 1846311 * 2
def baseEnd_1846311 : Nat := 140451108249397190136515

theorem tailTrace_1846311 : CollatzResearch.WordTrace tailWord_1846311 prefixEnd_1846311 140451108249397190136515 := by
  unfold tailWord_1846311
  simp only [CollatzResearch.WordTrace]
  refine ⟨67340494414138046659618787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44893662942758697773079191 67340494414138046659618787)
  ·
    refine ⟨101010741621207069989428181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67340494414138046659618787 101010741621207069989428181)
    ·
      refine ⟨2367439256747040702877223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 101010741621207069989428181 2367439256747040702877223)
      ·
        refine ⟨3551158885120561054315835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2367439256747040702877223 3551158885120561054315835)
        ·
          refine ⟨5326738327680841581473753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3551158885120561054315835 5326738327680841581473753)
          ·
            refine ⟨3995053745760631186105315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5326738327680841581473753 3995053745760631186105315)
            ·
              refine ⟨5992580618640946779157973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3995053745760631186105315 5992580618640946779157973)
              ·
                refine ⟨140451108249397190136515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5992580618640946779157973 140451108249397190136515)
                ·
                  rfl

theorem cell21_1846311_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 2, 1, 7].length) (baseStart_1846311 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1846311 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1846311 prefixEnd_1846311 := by exact prefixLift 1846311
  have htrace : WordTrace (prefixWord ++ tailWord_1846311) baseStart_1846311 baseEnd_1846311 := by
    simpa [prefixWord, tailWord_1846311, baseEnd_1846311] using wordTrace_append hprefix tailTrace_1846311
  have hstable : (prefixWord ++ tailWord_1846311).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1846311).length < 2 ^ (prefixWord ++ tailWord_1846311).sum := by decide
  have hdescent : baseEnd_1846311 < baseStart_1846311 := by decide
  rcases family_descends (prefixWord ++ tailWord_1846311) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1846339 : List Nat := [1, 1, 1, 3, 1, 2, 4, 4, 4]
def baseStart_1846339 : Nat := 118140960795 + 1846339 * 2 ^ 59
def prefixEnd_1846339 : Nat := 4983230072969 + 3 ^ 40 * 1846339 * 2
def baseEnd_1846339 : Nat := 421359714729669743942821

theorem tailTrace_1846339 : CollatzResearch.WordTrace tailWord_1846339 prefixEnd_1846339 421359714729669743942821 := by
  unfold tailWord_1846339
  simp only [CollatzResearch.WordTrace]
  refine ⟨67341515658036607441638071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44894343772024404961092047 67341515658036607441638071)
  ·
    refine ⟨101012273487054911162457107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67341515658036607441638071 101012273487054911162457107)
    ·
      refine ⟨151518410230582366743685661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101012273487054911162457107 151518410230582366743685661)
      ·
        refine ⟨56819403836468387528882123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 151518410230582366743685661 56819403836468387528882123)
        ·
          refine ⟨85229105754702581293323185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56819403836468387528882123 85229105754702581293323185)
          ·
            refine ⟨63921829316026935969992389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 85229105754702581293323185 63921829316026935969992389)
            ·
              refine ⟨11985342996755050494373573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 63921829316026935969992389 11985342996755050494373573)
              ·
                refine ⟨2247251811891571967695045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11985342996755050494373573 2247251811891571967695045)
                ·
                  refine ⟨421359714729669743942821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2247251811891571967695045 421359714729669743942821)
                  ·
                    rfl

theorem cell21_1846339_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 4, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 4, 4, 4].length) (baseStart_1846339 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1846339 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1846339 prefixEnd_1846339 := by exact prefixLift 1846339
  have htrace : WordTrace (prefixWord ++ tailWord_1846339) baseStart_1846339 baseEnd_1846339 := by
    simpa [prefixWord, tailWord_1846339, baseEnd_1846339] using wordTrace_append hprefix tailTrace_1846339
  have hstable : (prefixWord ++ tailWord_1846339).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1846339).length < 2 ^ (prefixWord ++ tailWord_1846339).sum := by decide
  have hdescent : baseEnd_1846339 < baseStart_1846339 := by decide
  rcases family_descends (prefixWord ++ tailWord_1846339) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1846353 : List Nat := [1, 2, 2, 1, 3, 1, 3, 8]
def baseStart_1846353 : Nat := 118140960795 + 1846353 * 2 ^ 59
def prefixEnd_1846353 : Nat := 4983230072969 + 3 ^ 40 * 1846353 * 2
def baseEnd_1846353 : Nat := 140454303240136276903153

theorem tailTrace_1846353 : CollatzResearch.WordTrace tailWord_1846353 prefixEnd_1846353 140454303240136276903153 := by
  unfold tailWord_1846353
  simp only [CollatzResearch.WordTrace]
  refine ⟨67342026279985887832647713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44894684186657258555098475 67342026279985887832647713)
  ·
    refine ⟨50506519709989415874485785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67342026279985887832647713 50506519709989415874485785)
    ·
      refine ⟨37879889782492061905864339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50506519709989415874485785 37879889782492061905864339)
      ·
        refine ⟨56819834673738092858796509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37879889782492061905864339 56819834673738092858796509)
        ·
          refine ⟨21307438002651784822048691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 56819834673738092858796509 21307438002651784822048691)
          ·
            refine ⟨31961157003977677233073037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21307438002651784822048691 31961157003977677233073037)
            ·
              refine ⟨11985433876491628962402389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31961157003977677233073037 11985433876491628962402389)
              ·
                refine ⟨140454303240136276903153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 11985433876491628962402389 140454303240136276903153)
                ·
                  rfl

theorem cell21_1846353_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 3, 8].length) (baseStart_1846353 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1846353 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1846353 prefixEnd_1846353 := by exact prefixLift 1846353
  have htrace : WordTrace (prefixWord ++ tailWord_1846353) baseStart_1846353 baseEnd_1846353 := by
    simpa [prefixWord, tailWord_1846353, baseEnd_1846353] using wordTrace_append hprefix tailTrace_1846353
  have hstable : (prefixWord ++ tailWord_1846353).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1846353).length < 2 ^ (prefixWord ++ tailWord_1846353).sum := by decide
  have hdescent : baseEnd_1846353 < baseStart_1846353 := by decide
  rcases family_descends (prefixWord ++ tailWord_1846353) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1846449 : List Nat := [1, 2, 2, 5, 1, 3, 1, 2, 4]
def baseStart_1846449 : Nat := 118140960795 + 1846449 * 2 ^ 59
def prefixEnd_1846449 : Nat := 4983230072969 + 3 ^ 40 * 1846449 * 2
def baseEnd_1846449 : Nat := 421384818228333997109263

theorem tailTrace_1846449 : CollatzResearch.WordTrace tailWord_1846449 prefixEnd_1846449 421384818228333997109263 := by
  unfold tailWord_1846449
  simp only [CollatzResearch.WordTrace]
  refine ⟨67345527687638096228142401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44897018458425397485428267 67345527687638096228142401)
  ·
    refine ⟨50509145765728572171106801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67345527687638096228142401 50509145765728572171106801)
    ·
      refine ⟨37881859324296429128330101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50509145765728572171106801 37881859324296429128330101)
      ·
        refine ⟨3551424311652790230780947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 37881859324296429128330101 3551424311652790230780947)
        ·
          refine ⟨5327136467479185346171421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3551424311652790230780947 5327136467479185346171421)
          ·
            refine ⟨1997676175304694504814283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5327136467479185346171421 1997676175304694504814283)
            ·
              refine ⟨2996514262957041757221425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1997676175304694504814283 2996514262957041757221425)
              ·
                refine ⟨2247385697217781317916069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2996514262957041757221425 2247385697217781317916069)
                ·
                  refine ⟨421384818228333997109263, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2247385697217781317916069 421384818228333997109263)
                  ·
                    rfl

theorem cell21_1846449_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 3, 1, 2, 4].length) (baseStart_1846449 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1846449 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1846449 prefixEnd_1846449 := by exact prefixLift 1846449
  have htrace : WordTrace (prefixWord ++ tailWord_1846449) baseStart_1846449 baseEnd_1846449 := by
    simpa [prefixWord, tailWord_1846449, baseEnd_1846449] using wordTrace_append hprefix tailTrace_1846449
  have hstable : (prefixWord ++ tailWord_1846449).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1846449).length < 2 ^ (prefixWord ++ tailWord_1846449).sum := by decide
  have hdescent : baseEnd_1846449 < baseStart_1846449 := by decide
  rcases family_descends (prefixWord ++ tailWord_1846449) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1846511 : List Nat := [1, 1, 2, 1, 7, 1, 3, 2, 3]
def baseStart_1846511 : Nat := 118140960795 + 1846511 * 2 ^ 59
def prefixEnd_1846511 : Nat := 4983230072969 + 3 ^ 40 * 1846511 * 2
def baseEnd_1846511 : Nat := 421398967473035667075803

theorem tailTrace_1846511 : CollatzResearch.WordTrace tailWord_1846511 prefixEnd_1846511 421398967473035667075803 := by
  unfold tailWord_1846511
  simp only [CollatzResearch.WordTrace]
  refine ⟨67347789013413480816899387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44898526008942320544599591 67347789013413480816899387)
  ·
    refine ⟨101021683520120221225349081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67347789013413480816899387 101021683520120221225349081)
    ·
      refine ⟨75766262640090165919011811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 101021683520120221225349081 75766262640090165919011811)
      ·
        refine ⟨113649393960135248878517717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75766262640090165919011811 113649393960135248878517717)
        ·
          refine ⟨2663657670940669895590259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 113649393960135248878517717 2663657670940669895590259)
          ·
            refine ⟨3995486506411004843385389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2663657670940669895590259 3995486506411004843385389)
            ·
              refine ⟨1498307439904126816269521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3995486506411004843385389 1498307439904126816269521)
              ·
                refine ⟨1123730579928095112202141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1498307439904126816269521 1123730579928095112202141)
                ·
                  refine ⟨421398967473035667075803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1123730579928095112202141 421398967473035667075803)
                  ·
                    rfl

theorem cell21_1846511_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 7, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 7, 1, 3, 2, 3].length) (baseStart_1846511 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1846511 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1846511 prefixEnd_1846511 := by exact prefixLift 1846511
  have htrace : WordTrace (prefixWord ++ tailWord_1846511) baseStart_1846511 baseEnd_1846511 := by
    simpa [prefixWord, tailWord_1846511, baseEnd_1846511] using wordTrace_append hprefix tailTrace_1846511
  have hstable : (prefixWord ++ tailWord_1846511).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1846511).length < 2 ^ (prefixWord ++ tailWord_1846511).sum := by decide
  have hdescent : baseEnd_1846511 < baseStart_1846511 := by decide
  rcases family_descends (prefixWord ++ tailWord_1846511) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1846612 : List Nat := [2, 4, 1, 1, 2, 1, 1, 2, 7]
def baseStart_1846612 : Nat := 118140960795 + 1846612 * 2 ^ 59
def prefixEnd_1846612 : Nat := 4983230072969 + 3 ^ 40 * 1846612 * 2
def baseEnd_1846612 : Nat := 421422017049081935892263

theorem tailTrace_1846612 : CollatzResearch.WordTrace tailWord_1846612 prefixEnd_1846612 421422017049081935892263 := by
  unfold tailWord_1846612
  simp only [CollatzResearch.WordTrace]
  refine ⟨33675736393023787533163045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44900981857365050044217393 33675736393023787533163045)
  ·
    refine ⟨6314200573691960162468071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 33675736393023787533163045 6314200573691960162468071)
    ·
      refine ⟨9471300860537940243702107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6314200573691960162468071 9471300860537940243702107)
      ·
        refine ⟨14206951290806910365553161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9471300860537940243702107 14206951290806910365553161)
        ·
          refine ⟨10655213468105182774164871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14206951290806910365553161 10655213468105182774164871)
          ·
            refine ⟨15982820202157774161247307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10655213468105182774164871 15982820202157774161247307)
            ·
              refine ⟨23974230303236661241870961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15982820202157774161247307 23974230303236661241870961)
              ·
                refine ⟨17980672727427495931403221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23974230303236661241870961 17980672727427495931403221)
                ·
                  refine ⟨421422017049081935892263, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 17980672727427495931403221 421422017049081935892263)
                  ·
                    rfl

theorem cell21_1846612_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 1, 2, 7].length) (baseStart_1846612 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1846612 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1846612 prefixEnd_1846612 := by exact prefixLift 1846612
  have htrace : WordTrace (prefixWord ++ tailWord_1846612) baseStart_1846612 baseEnd_1846612 := by
    simpa [prefixWord, tailWord_1846612, baseEnd_1846612] using wordTrace_append hprefix tailTrace_1846612
  have hstable : (prefixWord ++ tailWord_1846612).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1846612).length < 2 ^ (prefixWord ++ tailWord_1846612).sum := by decide
  have hdescent : baseEnd_1846612 < baseStart_1846612 := by decide
  rcases family_descends (prefixWord ++ tailWord_1846612) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1846629 : List Nat := [1, 3, 1, 3, 1, 2, 1, 6, 3]
def baseStart_1846629 : Nat := 118140960795 + 1846629 * 2 ^ 59
def prefixEnd_1846629 : Nat := 4983230072969 + 3 ^ 40 * 1846629 * 2
def baseEnd_1846629 : Nat := 421425896680693684108895

theorem tailTrace_1846629 : CollatzResearch.WordTrace tailWord_1846629 prefixEnd_1846629 421425896680693684108895 := by
  unfold tailWord_1846629
  simp only [CollatzResearch.WordTrace]
  refine ⟨67352092826985986969694941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44901395217990657979796627 67352092826985986969694941)
  ·
    refine ⟨25257034810119745113635603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 67352092826985986969694941 25257034810119745113635603)
    ·
      refine ⟨37885552215179617670453405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25257034810119745113635603 37885552215179617670453405)
      ·
        refine ⟨14207082080692356626420027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 37885552215179617670453405 14207082080692356626420027)
        ·
          refine ⟨21310623121038534939630041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14207082080692356626420027 21310623121038534939630041)
          ·
            refine ⟨15982967340778901204722531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21310623121038534939630041 15982967340778901204722531)
            ·
              refine ⟨23974451011168351807083797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15982967340778901204722531 23974451011168351807083797)
              ·
                refine ⟨1123802391148516490957053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 23974451011168351807083797 1123802391148516490957053)
                ·
                  refine ⟨421425896680693684108895, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1123802391148516490957053 421425896680693684108895)
                  ·
                    rfl

theorem cell21_1846629_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 1, 6, 3].length) (baseStart_1846629 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1846629 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1846629 prefixEnd_1846629 := by exact prefixLift 1846629
  have htrace : WordTrace (prefixWord ++ tailWord_1846629) baseStart_1846629 baseEnd_1846629 := by
    simpa [prefixWord, tailWord_1846629, baseEnd_1846629] using wordTrace_append hprefix tailTrace_1846629
  have hstable : (prefixWord ++ tailWord_1846629).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1846629).length < 2 ^ (prefixWord ++ tailWord_1846629).sum := by decide
  have hdescent : baseEnd_1846629 < baseStart_1846629 := by decide
  rcases family_descends (prefixWord ++ tailWord_1846629) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1846778 : List Nat := [3, 1, 1, 1, 1, 2, 4, 2, 6]
def baseStart_1846778 : Nat := 118140960795 + 1846778 * 2 ^ 59
def prefixEnd_1846778 : Nat := 4983230072969 + 3 ^ 40 * 1846778 * 2
def baseEnd_1846778 : Nat := 421459900510702536125257

theorem tailTrace_1846778 : CollatzResearch.WordTrace tailWord_1846778 prefixEnd_1846778 421459900510702536125257 := by
  unfold tailWord_1846778
  simp only [CollatzResearch.WordTrace]
  refine ⟨16839381825861546354217247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 44905018202297456944579325 16839381825861546354217247)
  ·
    refine ⟨25259072738792319531325871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16839381825861546354217247 25259072738792319531325871)
    ·
      refine ⟨37888609108188479296988807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25259072738792319531325871 37888609108188479296988807)
      ·
        refine ⟨56832913662282718945483211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37888609108188479296988807 56832913662282718945483211)
        ·
          refine ⟨85249370493424078418224817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56832913662282718945483211 85249370493424078418224817)
          ·
            refine ⟨63937027870068058813668613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 85249370493424078418224817 63937027870068058813668613)
            ·
              refine ⟨11988192725637761027562865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 63937027870068058813668613 11988192725637761027562865)
              ·
                refine ⟨8991144544228320770672149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11988192725637761027562865 8991144544228320770672149)
                ·
                  refine ⟨421459900510702536125257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8991144544228320770672149 421459900510702536125257)
                  ·
                    rfl

theorem cell21_1846778_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 4, 2, 6].length) (baseStart_1846778 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1846778 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1846778 prefixEnd_1846778 := by exact prefixLift 1846778
  have htrace : WordTrace (prefixWord ++ tailWord_1846778) baseStart_1846778 baseEnd_1846778 := by
    simpa [prefixWord, tailWord_1846778, baseEnd_1846778] using wordTrace_append hprefix tailTrace_1846778
  have hstable : (prefixWord ++ tailWord_1846778).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1846778).length < 2 ^ (prefixWord ++ tailWord_1846778).sum := by decide
  have hdescent : baseEnd_1846778 < baseStart_1846778 := by decide
  rcases family_descends (prefixWord ++ tailWord_1846778) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1846781 : List Nat := [1, 4, 1, 1, 1, 4, 1, 5, 3]
def baseStart_1846781 : Nat := 118140960795 + 1846781 * 2 ^ 59
def prefixEnd_1846781 : Nat := 4983230072969 + 3 ^ 40 * 1846781 * 2
def baseEnd_1846781 : Nat := 421460585151575197575251

theorem tailTrace_1846781 : CollatzResearch.WordTrace tailWord_1846781 prefixEnd_1846781 421460585151575197575251 := by
  unfold tailWord_1846781
  simp only [CollatzResearch.WordTrace]
  refine ⟨67357636722435316929228197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44905091148290211286152131 67357636722435316929228197)
  ·
    refine ⟨12629556885456621924230287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 67357636722435316929228197 12629556885456621924230287)
    ·
      refine ⟨18944335328184932886345431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12629556885456621924230287 18944335328184932886345431)
      ·
        refine ⟨28416502992277399329518147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18944335328184932886345431 28416502992277399329518147)
        ·
          refine ⟨42624754488416098994277221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28416502992277399329518147 42624754488416098994277221)
          ·
            refine ⟨7992141466578018561426979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 42624754488416098994277221 7992141466578018561426979)
            ·
              refine ⟨11988212199867027842140469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7992141466578018561426979 11988212199867027842140469)
              ·
                refine ⟨1123894893737533860200669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 11988212199867027842140469 1123894893737533860200669)
                ·
                  refine ⟨421460585151575197575251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1123894893737533860200669 421460585151575197575251)
                  ·
                    rfl

theorem cell21_1846781_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 4, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 4, 1, 5, 3].length) (baseStart_1846781 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1846781 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1846781 prefixEnd_1846781 := by exact prefixLift 1846781
  have htrace : WordTrace (prefixWord ++ tailWord_1846781) baseStart_1846781 baseEnd_1846781 := by
    simpa [prefixWord, tailWord_1846781, baseEnd_1846781] using wordTrace_append hprefix tailTrace_1846781
  have hstable : (prefixWord ++ tailWord_1846781).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1846781).length < 2 ^ (prefixWord ++ tailWord_1846781).sum := by decide
  have hdescent : baseEnd_1846781 < baseStart_1846781 := by decide
  rcases family_descends (prefixWord ++ tailWord_1846781) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1846795 : List Nat := [1, 1, 1, 1, 8, 1, 1, 1, 6]
def baseStart_1846795 : Nat := 118140960795 + 1846795 * 2 ^ 59
def prefixEnd_1846795 : Nat := 4983230072969 + 3 ^ 40 * 1846795 * 2
def baseEnd_1846795 : Nat := 421463780142314284341889

theorem tailTrace_1846795 : CollatzResearch.WordTrace tailWord_1846795 prefixEnd_1846795 421463780142314284341889 := by
  unfold tailWord_1846795
  simp only [CollatzResearch.WordTrace]
  refine ⟨67358147344384597320237839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44905431562923064880158559 67358147344384597320237839)
  ·
    refine ⟨101037221016576895980356759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67358147344384597320237839 101037221016576895980356759)
    ·
      refine ⟨151555831524865343970535139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101037221016576895980356759 151555831524865343970535139)
      ·
        refine ⟨227333747287298015955802709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 151555831524865343970535139 227333747287298015955802709)
        ·
          refine ⟨2664067351023023624482063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 8 227333747287298015955802709 2664067351023023624482063)
          ·
            refine ⟨3996101026534535436723095, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2664067351023023624482063 3996101026534535436723095)
            ·
              refine ⟨5994151539801803155084643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3996101026534535436723095 5994151539801803155084643)
              ·
                refine ⟨8991227309702704732626965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5994151539801803155084643 8991227309702704732626965)
                ·
                  refine ⟨421463780142314284341889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8991227309702704732626965 421463780142314284341889)
                  ·
                    rfl

theorem cell21_1846795_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 8, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 8, 1, 1, 1, 6].length) (baseStart_1846795 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1846795 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1846795 prefixEnd_1846795 := by exact prefixLift 1846795
  have htrace : WordTrace (prefixWord ++ tailWord_1846795) baseStart_1846795 baseEnd_1846795 := by
    simpa [prefixWord, tailWord_1846795, baseEnd_1846795] using wordTrace_append hprefix tailTrace_1846795
  have hstable : (prefixWord ++ tailWord_1846795).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1846795).length < 2 ^ (prefixWord ++ tailWord_1846795).sum := by decide
  have hdescent : baseEnd_1846795 < baseStart_1846795 := by decide
  rcases family_descends (prefixWord ++ tailWord_1846795) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1846812 : List Nat := [2, 2, 3, 1, 2, 1, 5, 1, 4]
def baseStart_1846812 : Nat := 118140960795 + 1846812 * 2 ^ 59
def prefixEnd_1846812 : Nat := 4983230072969 + 3 ^ 40 * 1846812 * 2
def baseEnd_1846812 : Nat := 421467659773926032558521

theorem tailTrace_1846812 : CollatzResearch.WordTrace tailWord_1846812 prefixEnd_1846812 421467659773926032558521 := by
  unfold tailWord_1846812
  simp only [CollatzResearch.WordTrace]
  refine ⟨33679383692661504611803345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44905844923548672815737793 33679383692661504611803345)
  ·
    refine ⟨25259537769496128458852509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33679383692661504611803345 25259537769496128458852509)
    ·
      refine ⟨9472326663561048172069691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25259537769496128458852509 9472326663561048172069691)
      ·
        refine ⟨14208489995341572258104537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9472326663561048172069691 14208489995341572258104537)
        ·
          refine ⟨10656367496506179193578403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14208489995341572258104537 10656367496506179193578403)
          ·
            refine ⟨15984551244759268790367605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10656367496506179193578403 15984551244759268790367605)
            ·
              refine ⟨1498551679196181449096963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 15984551244759268790367605 1498551679196181449096963)
              ·
                refine ⟨2247827518794272173645445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1498551679196181449096963 2247827518794272173645445)
                ·
                  refine ⟨421467659773926032558521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2247827518794272173645445 421467659773926032558521)
                  ·
                    rfl

theorem cell21_1846812_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 5, 1, 4].length) (baseStart_1846812 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1846812 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1846812 prefixEnd_1846812 := by exact prefixLift 1846812
  have htrace : WordTrace (prefixWord ++ tailWord_1846812) baseStart_1846812 baseEnd_1846812 := by
    simpa [prefixWord, tailWord_1846812, baseEnd_1846812] using wordTrace_append hprefix tailTrace_1846812
  have hstable : (prefixWord ++ tailWord_1846812).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1846812).length < 2 ^ (prefixWord ++ tailWord_1846812).sum := by decide
  have hdescent : baseEnd_1846812 < baseStart_1846812 := by decide
  rcases family_descends (prefixWord ++ tailWord_1846812) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1846871 : List Nat := [1, 1, 3, 2, 2, 4, 1, 3, 4]
def baseStart_1846871 : Nat := 118140960795 + 1846871 * 2 ^ 59
def prefixEnd_1846871 : Nat := 4983230072969 + 3 ^ 40 * 1846871 * 2
def baseEnd_1846871 : Nat := 421481124377755041075067

theorem tailTrace_1846871 : CollatzResearch.WordTrace tailWord_1846871 prefixEnd_1846871 421481124377755041075067 := by
  unfold tailWord_1846871
  simp only [CollatzResearch.WordTrace]
  refine ⟨67360919292109262300004467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44907279528072841533336311 67360919292109262300004467)
  ·
    refine ⟨101041378938163893450006701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67360919292109262300004467 101041378938163893450006701)
    ·
      refine ⟨37890517101811460043752513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 101041378938163893450006701 37890517101811460043752513)
      ·
        refine ⟨28417887826358595032814385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37890517101811460043752513 28417887826358595032814385)
        ·
          refine ⟨21313415869768946274610789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28417887826358595032814385 21313415869768946274610789)
          ·
            refine ⟨3996265475581677426489523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 21313415869768946274610789 3996265475581677426489523)
            ·
              refine ⟨5994398213372516139734285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3996265475581677426489523 5994398213372516139734285)
              ·
                refine ⟨2247899330014693552400357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5994398213372516139734285 2247899330014693552400357)
                ·
                  refine ⟨421481124377755041075067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2247899330014693552400357 421481124377755041075067)
                  ·
                    rfl

theorem cell21_1846871_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 4, 1, 3, 4].length) (baseStart_1846871 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1846871 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1846871 prefixEnd_1846871 := by exact prefixLift 1846871
  have htrace : WordTrace (prefixWord ++ tailWord_1846871) baseStart_1846871 baseEnd_1846871 := by
    simpa [prefixWord, tailWord_1846871, baseEnd_1846871] using wordTrace_append hprefix tailTrace_1846871
  have hstable : (prefixWord ++ tailWord_1846871).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1846871).length < 2 ^ (prefixWord ++ tailWord_1846871).sum := by decide
  have hdescent : baseEnd_1846871 < baseStart_1846871 := by decide
  rcases family_descends (prefixWord ++ tailWord_1846871) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1846885 : List Nat := [1, 3, 1, 3, 3, 1, 2, 7]
def baseStart_1846885 : Nat := 118140960795 + 1846885 * 2 ^ 59
def prefixEnd_1846885 : Nat := 4983230072969 + 3 ^ 40 * 1846885 * 2
def baseEnd_1846885 : Nat := 140494773122831375947235

theorem tailTrace_1846885 : CollatzResearch.WordTrace tailWord_1846885 prefixEnd_1846885 140494773122831375947235 := by
  unfold tailWord_1846885
  simp only [CollatzResearch.WordTrace]
  refine ⟨67361429914058542691014109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44907619942705695127342739 67361429914058542691014109)
  ·
    refine ⟨25260536217771953509130291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 67361429914058542691014109 25260536217771953509130291)
    ·
      refine ⟨37890804326657930263695437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25260536217771953509130291 37890804326657930263695437)
      ·
        refine ⟨14209051622496723848885789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 37890804326657930263695437 14209051622496723848885789)
        ·
          refine ⟨5328394358436271443332171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14209051622496723848885789 5328394358436271443332171)
          ·
            refine ⟨7992591537654407164998257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5328394358436271443332171 7992591537654407164998257)
            ·
              refine ⟨5994443653240805373748693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7992591537654407164998257 5994443653240805373748693)
              ·
                refine ⟨140494773122831375947235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5994443653240805373748693 140494773122831375947235)
                ·
                  rfl

theorem cell21_1846885_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 1, 2, 7].length) (baseStart_1846885 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1846885 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1846885 prefixEnd_1846885 := by exact prefixLift 1846885
  have htrace : WordTrace (prefixWord ++ tailWord_1846885) baseStart_1846885 baseEnd_1846885 := by
    simpa [prefixWord, tailWord_1846885, baseEnd_1846885] using wordTrace_append hprefix tailTrace_1846885
  have hstable : (prefixWord ++ tailWord_1846885).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1846885).length < 2 ^ (prefixWord ++ tailWord_1846885).sum := by decide
  have hdescent : baseEnd_1846885 < baseStart_1846885 := by decide
  rcases family_descends (prefixWord ++ tailWord_1846885) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1847020 : List Nat := [2, 2, 1, 1, 2, 2, 11]
def baseStart_1847020 : Nat := 118140960795 + 1847020 * 2 ^ 59
def prefixEnd_1847020 : Nat := 4983230072969 + 3 ^ 40 * 1847020 * 2
def baseEnd_1847020 : Nat := 46835014245307099232381

theorem tailTrace_1847020 : CollatzResearch.WordTrace tailWord_1847020 prefixEnd_1847020 46835014245307099232381 := by
  unfold tailWord_1847020
  simp only [CollatzResearch.WordTrace]
  refine ⟨33683176884284730373589257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44910902512379640498119009 33683176884284730373589257)
  ·
    refine ⟨25262382663213547780191943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33683176884284730373589257 25262382663213547780191943)
    ·
      refine ⟨37893573994820321670287915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25262382663213547780191943 37893573994820321670287915)
      ·
        refine ⟨56840360992230482505431873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37893573994820321670287915 56840360992230482505431873)
        ·
          refine ⟨42630270744172861879073905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56840360992230482505431873 42630270744172861879073905)
          ·
            refine ⟨31972703058129646409305429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42630270744172861879073905 31972703058129646409305429)
            ·
              refine ⟨46835014245307099232381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 31972703058129646409305429 46835014245307099232381)
              ·
                rfl

theorem cell21_1847020_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 11].length) (baseStart_1847020 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1847020 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1847020 prefixEnd_1847020 := by exact prefixLift 1847020
  have htrace : WordTrace (prefixWord ++ tailWord_1847020) baseStart_1847020 baseEnd_1847020 := by
    simpa [prefixWord, tailWord_1847020, baseEnd_1847020] using wordTrace_append hprefix tailTrace_1847020
  have hstable : (prefixWord ++ tailWord_1847020).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1847020).length < 2 ^ (prefixWord ++ tailWord_1847020).sum := by decide
  have hdescent : baseEnd_1847020 < baseStart_1847020 := by decide
  rcases family_descends (prefixWord ++ tailWord_1847020) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1847026 : List Nat := [3, 2, 1, 3, 1, 1, 5, 2, 3]
def baseStart_1847026 : Nat := 118140960795 + 1847026 * 2 ^ 59
def prefixEnd_1847026 : Nat := 4983230072969 + 3 ^ 40 * 1847026 * 2
def baseEnd_1847026 : Nat := 421516497489509215991417

theorem tailTrace_1847026 : CollatzResearch.WordTrace tailWord_1847026 prefixEnd_1847026 421516497489509215991417 := by
  unfold tailWord_1847026
  simp only [CollatzResearch.WordTrace]
  refine ⟨16841643151636930942974233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 44911048404365149181264621 16841643151636930942974233)
  ·
    refine ⟨12631232363727698207230675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16841643151636930942974233 12631232363727698207230675)
    ·
      refine ⟨18946848545591547310846013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12631232363727698207230675 18946848545591547310846013)
      ·
        refine ⟨7105068204596830241567255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18946848545591547310846013 7105068204596830241567255)
        ·
          refine ⟨10657602306895245362350883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7105068204596830241567255 10657602306895245362350883)
          ·
            refine ⟨15986403460342868043526325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10657602306895245362350883 15986403460342868043526325)
            ·
              refine ⟨1498725324407143879080593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 15986403460342868043526325 1498725324407143879080593)
              ·
                refine ⟨1124043993305357909310445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1498725324407143879080593 1124043993305357909310445)
                ·
                  refine ⟨421516497489509215991417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1124043993305357909310445 421516497489509215991417)
                  ·
                    rfl

theorem cell21_1847026_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 5, 2, 3].length) (baseStart_1847026 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1847026 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1847026 prefixEnd_1847026 := by exact prefixLift 1847026
  have htrace : WordTrace (prefixWord ++ tailWord_1847026) baseStart_1847026 baseEnd_1847026 := by
    simpa [prefixWord, tailWord_1847026, baseEnd_1847026] using wordTrace_append hprefix tailTrace_1847026
  have hstable : (prefixWord ++ tailWord_1847026).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1847026).length < 2 ^ (prefixWord ++ tailWord_1847026).sum := by decide
  have hdescent : baseEnd_1847026 < baseStart_1847026 := by decide
  rcases family_descends (prefixWord ++ tailWord_1847026) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1847051 : List Nat := [1, 1, 1, 1, 5, 1, 2, 4, 5]
def baseStart_1847051 : Nat := 118140960795 + 1847051 * 2 ^ 59
def prefixEnd_1847051 : Nat := 4983230072969 + 3 ^ 40 * 1847051 * 2
def baseEnd_1847051 : Nat := 421522202830114728074699

theorem tailTrace_1847051 : CollatzResearch.WordTrace tailWord_1847051 prefixEnd_1847051 421522202830114728074699 := by
  unfold tailWord_1847051
  simp only [CollatzResearch.WordTrace]
  refine ⟨67367484431457153041557007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44911656287638102027704671 67367484431457153041557007)
  ·
    refine ⟨101051226647185729562335511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67367484431457153041557007 101051226647185729562335511)
    ·
      refine ⟨151576839970778594343503267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101051226647185729562335511 151576839970778594343503267)
      ·
        refine ⟨227365259956167891515254901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 151576839970778594343503267 227365259956167891515254901)
        ·
          refine ⟨21315493120890739829555147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 227365259956167891515254901 21315493120890739829555147)
          ·
            refine ⟨31973239681336109744332721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21315493120890739829555147 31973239681336109744332721)
            ·
              refine ⟨23979929761002082308249541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31973239681336109744332721 23979929761002082308249541)
              ·
                refine ⟨4496236830187890432796789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 23979929761002082308249541 4496236830187890432796789)
                ·
                  refine ⟨421522202830114728074699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4496236830187890432796789 421522202830114728074699)
                  ·
                    rfl

theorem cell21_1847051_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 2, 4, 5].length) (baseStart_1847051 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1847051 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1847051 prefixEnd_1847051 := by exact prefixLift 1847051
  have htrace : WordTrace (prefixWord ++ tailWord_1847051) baseStart_1847051 baseEnd_1847051 := by
    simpa [prefixWord, tailWord_1847051, baseEnd_1847051] using wordTrace_append hprefix tailTrace_1847051
  have hstable : (prefixWord ++ tailWord_1847051).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1847051).length < 2 ^ (prefixWord ++ tailWord_1847051).sum := by decide
  have hdescent : baseEnd_1847051 < baseStart_1847051 := by decide
  rcases family_descends (prefixWord ++ tailWord_1847051) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1847113 : List Nat := [1, 2, 1, 1, 2, 4, 5, 5]
def baseStart_1847113 : Nat := 118140960795 + 1847113 * 2 ^ 59
def prefixEnd_1847113 : Nat := 4983230072969 + 3 ^ 40 * 1847113 * 2
def baseEnd_1847113 : Nat := 140512117358272132680413

theorem tailTrace_1847113 : CollatzResearch.WordTrace tailWord_1847113 prefixEnd_1847113 140512117358272132680413 := by
  unfold tailWord_1847113
  simp only [CollatzResearch.WordTrace]
  refine ⟨67369745757232537630313993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44913163838155025086875995 67369745757232537630313993)
  ·
    refine ⟨50527309317924403222735495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67369745757232537630313993 50527309317924403222735495)
    ·
      refine ⟨75790963976886604834103243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50527309317924403222735495 75790963976886604834103243)
      ·
        refine ⟨113686445965329907251154865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75790963976886604834103243 113686445965329907251154865)
        ·
          refine ⟨85264834473997430438366149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 113686445965329907251154865 85264834473997430438366149)
          ·
            refine ⟨15987156463874518207193653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 85264834473997430438366149 15987156463874518207193653)
            ·
              refine ⟨1498795918488236081924405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 15987156463874518207193653 1498795918488236081924405)
              ·
                refine ⟨140512117358272132680413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1498795918488236081924405 140512117358272132680413)
                ·
                  rfl

theorem cell21_1847113_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 5, 5].length) (baseStart_1847113 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1847113 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1847113 prefixEnd_1847113 := by exact prefixLift 1847113
  have htrace : WordTrace (prefixWord ++ tailWord_1847113) baseStart_1847113 baseEnd_1847113 := by
    simpa [prefixWord, tailWord_1847113, baseEnd_1847113] using wordTrace_append hprefix tailTrace_1847113
  have hstable : (prefixWord ++ tailWord_1847113).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1847113).length < 2 ^ (prefixWord ++ tailWord_1847113).sum := by decide
  have hdescent : baseEnd_1847113 < baseStart_1847113 := by decide
  rcases family_descends (prefixWord ++ tailWord_1847113) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1847144 : List Nat := [2, 1, 4, 2, 1, 1, 4, 1, 5]
def baseStart_1847144 : Nat := 118140960795 + 1847144 * 2 ^ 59
def prefixEnd_1847144 : Nat := 4983230072969 + 3 ^ 40 * 1847144 * 2
def baseEnd_1847144 : Nat := 421543426697167233024509

theorem tailTrace_1847144 : CollatzResearch.WordTrace tailWord_1847144 prefixEnd_1847144 421543426697167233024509 := by
  unfold tailWord_1847144
  simp only [CollatzResearch.WordTrace]
  refine ⟨33685438210060114962346243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44913917613413486616461657 33685438210060114962346243)
  ·
    refine ⟨50528157315090172443519365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33685438210060114962346243 50528157315090172443519365)
    ·
      refine ⟨9474029496579407333159881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 50528157315090172443519365 9474029496579407333159881)
      ·
        refine ⟨7105522122434555499869911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9474029496579407333159881 7105522122434555499869911)
        ·
          refine ⟨10658283183651833249804867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7105522122434555499869911 10658283183651833249804867)
          ·
            refine ⟨15987424775477749874707301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10658283183651833249804867 15987424775477749874707301)
            ·
              refine ⟨2997642145402078101507619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15987424775477749874707301 2997642145402078101507619)
              ·
                refine ⟨4496463218103117152261429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2997642145402078101507619 4496463218103117152261429)
                ·
                  refine ⟨421543426697167233024509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4496463218103117152261429 421543426697167233024509)
                  ·
                    rfl

theorem cell21_1847144_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 4, 1, 5].length) (baseStart_1847144 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1847144 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1847144 prefixEnd_1847144 := by exact prefixLift 1847144
  have htrace : WordTrace (prefixWord ++ tailWord_1847144) baseStart_1847144 baseEnd_1847144 := by
    simpa [prefixWord, tailWord_1847144, baseEnd_1847144] using wordTrace_append hprefix tailTrace_1847144
  have hstable : (prefixWord ++ tailWord_1847144).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1847144).length < 2 ^ (prefixWord ++ tailWord_1847144).sum := by decide
  have hdescent : baseEnd_1847144 < baseStart_1847144 := by decide
  rcases family_descends (prefixWord ++ tailWord_1847144) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1847279 : List Nat := [1, 1, 2, 1, 4, 2, 3, 2, 5]
def baseStart_1847279 : Nat := 118140960795 + 1847279 * 2 ^ 59
def prefixEnd_1847279 : Nat := 4983230072969 + 3 ^ 40 * 1847279 * 2
def baseEnd_1847279 : Nat := 421574235536436998274233

theorem tailTrace_1847279 : CollatzResearch.WordTrace tailWord_1847279 prefixEnd_1847279 421574235536436998274233 := by
  unfold tailWord_1847279
  simp only [CollatzResearch.WordTrace]
  refine ⟨67375800274631147980856891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44917200183087431987237927 67375800274631147980856891)
  ·
    refine ⟨101063700411946721971285337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67375800274631147980856891 101063700411946721971285337)
    ·
      refine ⟨75797775308960041478464003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 101063700411946721971285337 75797775308960041478464003)
      ·
        refine ⟨113696662963440062217696005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75797775308960041478464003 113696662963440062217696005)
        ·
          refine ⟨21318124305645011665818001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 113696662963440062217696005 21318124305645011665818001)
          ·
            refine ⟨15988593229233758749363501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21318124305645011665818001 15988593229233758749363501)
            ·
              refine ⟨5995722460962659531011313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15988593229233758749363501 5995722460962659531011313)
              ·
                refine ⟨4496791845721994648258485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5995722460962659531011313 4496791845721994648258485)
                ·
                  refine ⟨421574235536436998274233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4496791845721994648258485 421574235536436998274233)
                  ·
                    rfl

theorem cell21_1847279_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 3, 2, 5].length) (baseStart_1847279 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1847279 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1847279 prefixEnd_1847279 := by exact prefixLift 1847279
  have htrace : WordTrace (prefixWord ++ tailWord_1847279) baseStart_1847279 baseEnd_1847279 := by
    simpa [prefixWord, tailWord_1847279, baseEnd_1847279] using wordTrace_append hprefix tailTrace_1847279
  have hstable : (prefixWord ++ tailWord_1847279).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1847279).length < 2 ^ (prefixWord ++ tailWord_1847279).sum := by decide
  have hdescent : baseEnd_1847279 < baseStart_1847279 := by decide
  rcases family_descends (prefixWord ++ tailWord_1847279) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1847302 : List Nat := [6, 2, 1, 2, 1, 1, 1, 1, 6]
def baseStart_1847302 : Nat := 118140960795 + 1847302 * 2 ^ 59
def prefixEnd_1847302 : Nat := 4983230072969 + 3 ^ 40 * 1847302 * 2
def baseEnd_1847302 : Nat := 421579484449794069390853

theorem tailTrace_1847302 : CollatzResearch.WordTrace tailWord_1847302 prefixEnd_1847302 421579484449794069390853 := by
  unfold tailWord_1847302
  simp only [CollatzResearch.WordTrace]
  refine ⟨2105519973548369465904505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 44917759435698548605962773 2105519973548369465904505)
  ·
    refine ⟨1579139980161277099428379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2105519973548369465904505 1579139980161277099428379)
    ·
      refine ⟨2368709970241915649142569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1579139980161277099428379 2368709970241915649142569)
      ·
        refine ⟨1776532477681436736856927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2368709970241915649142569 1776532477681436736856927)
        ·
          refine ⟨2664798716522155105285391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1776532477681436736856927 2664798716522155105285391)
          ·
            refine ⟨3997198074783232657928087, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2664798716522155105285391 3997198074783232657928087)
            ·
              refine ⟨5995797112174848986892131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3997198074783232657928087 5995797112174848986892131)
              ·
                refine ⟨8993695668262273480338197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5995797112174848986892131 8993695668262273480338197)
                ·
                  refine ⟨421579484449794069390853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8993695668262273480338197 421579484449794069390853)
                  ·
                    rfl

theorem cell21_1847302_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 2, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 2, 1, 1, 1, 1, 6].length) (baseStart_1847302 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1847302 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1847302 prefixEnd_1847302 := by exact prefixLift 1847302
  have htrace : WordTrace (prefixWord ++ tailWord_1847302) baseStart_1847302 baseEnd_1847302 := by
    simpa [prefixWord, tailWord_1847302, baseEnd_1847302] using wordTrace_append hprefix tailTrace_1847302
  have hstable : (prefixWord ++ tailWord_1847302).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1847302).length < 2 ^ (prefixWord ++ tailWord_1847302).sum := by decide
  have hdescent : baseEnd_1847302 < baseStart_1847302 := by decide
  rcases family_descends (prefixWord ++ tailWord_1847302) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1847310 : List Nat := [4, 1, 1, 2, 2, 1, 3, 1, 6]
def baseStart_1847310 : Nat := 118140960795 + 1847310 * 2 ^ 59
def prefixEnd_1847310 : Nat := 4983230072969 + 3 ^ 40 * 1847310 * 2
def baseEnd_1847310 : Nat := 421581310158787833257503

theorem tailTrace_1847310 : CollatzResearch.WordTrace tailWord_1847310 prefixEnd_1847310 421581310158787833257503 := by
  unfold tailWord_1847310
  simp only [CollatzResearch.WordTrace]
  refine ⟨8422116367189855034404423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 44917953958345893516823589 8422116367189855034404423)
  ·
    refine ⟨12633174550784782551606635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8422116367189855034404423 12633174550784782551606635)
    ·
      refine ⟨18949761826177173827409953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12633174550784782551606635 18949761826177173827409953)
      ·
        refine ⟨14212321369632880370557465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18949761826177173827409953 14212321369632880370557465)
        ·
          refine ⟨10659241027224660277918099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14212321369632880370557465 10659241027224660277918099)
          ·
            refine ⟨15988861540836990416877149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10659241027224660277918099 15988861540836990416877149)
            ·
              refine ⟨5995823077813871406328931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15988861540836990416877149 5995823077813871406328931)
              ·
                refine ⟨8993734616720807109493397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5995823077813871406328931 8993734616720807109493397)
                ·
                  refine ⟨421581310158787833257503, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8993734616720807109493397 421581310158787833257503)
                  ·
                    rfl

theorem cell21_1847310_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 3, 1, 6].length) (baseStart_1847310 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1847310 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1847310 prefixEnd_1847310 := by exact prefixLift 1847310
  have htrace : WordTrace (prefixWord ++ tailWord_1847310) baseStart_1847310 baseEnd_1847310 := by
    simpa [prefixWord, tailWord_1847310, baseEnd_1847310] using wordTrace_append hprefix tailTrace_1847310
  have hstable : (prefixWord ++ tailWord_1847310).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1847310).length < 2 ^ (prefixWord ++ tailWord_1847310).sum := by decide
  have hdescent : baseEnd_1847310 < baseStart_1847310 := by decide
  rcases family_descends (prefixWord ++ tailWord_1847310) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1847327 : List Nat := [1, 1, 2, 4, 1, 2, 5, 1, 4]
def baseStart_1847327 : Nat := 118140960795 + 1847327 * 2 ^ 59
def prefixEnd_1847327 : Nat := 4983230072969 + 3 ^ 40 * 1847327 * 2
def baseEnd_1847327 : Nat := 421585189790399581474135

theorem tailTrace_1847327 : CollatzResearch.WordTrace tailWord_1847327 prefixEnd_1847327 421585189790399581474135 := by
  unfold tailWord_1847327
  simp only [CollatzResearch.WordTrace]
  refine ⟨67377550978457252178604235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44918367318971501452402823 67377550978457252178604235)
  ·
    refine ⟨101066326467685878267906353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67377550978457252178604235 101066326467685878267906353)
    ·
      refine ⟨75799744850764408700929765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 101066326467685878267906353 75799744850764408700929765)
      ·
        refine ⟨14212452159518326631424331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 75799744850764408700929765 14212452159518326631424331)
        ·
          refine ⟨21318678239277489947136497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14212452159518326631424331 21318678239277489947136497)
          ·
            refine ⟨15989008679458117460352373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21318678239277489947136497 15989008679458117460352373)
            ·
              refine ⟨1498969563699198511908035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 15989008679458117460352373 1498969563699198511908035)
              ·
                refine ⟨2248454345548797767862053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1498969563699198511908035 2248454345548797767862053)
                ·
                  refine ⟨421585189790399581474135, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2248454345548797767862053 421585189790399581474135)
                  ·
                    rfl

theorem cell21_1847327_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 5, 1, 4].length) (baseStart_1847327 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1847327 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1847327 prefixEnd_1847327 := by exact prefixLift 1847327
  have htrace : WordTrace (prefixWord ++ tailWord_1847327) baseStart_1847327 baseEnd_1847327 := by
    simpa [prefixWord, tailWord_1847327, baseEnd_1847327] using wordTrace_append hprefix tailTrace_1847327
  have hstable : (prefixWord ++ tailWord_1847327).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1847327).length < 2 ^ (prefixWord ++ tailWord_1847327).sum := by decide
  have hdescent : baseEnd_1847327 < baseStart_1847327 := by decide
  rcases family_descends (prefixWord ++ tailWord_1847327) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1847358 : List Nat := [4, 2, 1, 3, 2, 2, 7]
def baseStart_1847358 : Nat := 118140960795 + 1847358 * 2 ^ 59
def prefixEnd_1847358 : Nat := 4983230072969 + 3 ^ 40 * 1847358 * 2
def baseEnd_1847358 : Nat := 46843584934750046273045

theorem tailTrace_1847358 : CollatzResearch.WordTrace tailWord_1847358 prefixEnd_1847358 46843584934750046273045 := by
  unfold tailWord_1847358
  simp only [CollatzResearch.WordTrace]
  refine ⟨8422335205168118059122841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 44919121094229962981988485 8422335205168118059122841)
  ·
    refine ⟨6316751403876088544342131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8422335205168118059122841 6316751403876088544342131)
    ·
      refine ⟨9475127105814132816513197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6316751403876088544342131 9475127105814132816513197)
      ·
        refine ⟨3553172664680299806192449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9475127105814132816513197 3553172664680299806192449)
        ·
          refine ⟨2664879498510224854644337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3553172664680299806192449 2664879498510224854644337)
          ·
            refine ⟨1998659623882668640983253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2664879498510224854644337 1998659623882668640983253)
            ·
              refine ⟨46843584934750046273045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1998659623882668640983253 46843584934750046273045)
              ·
                rfl

theorem cell21_1847358_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 2, 2, 7].length) (baseStart_1847358 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1847358 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1847358 prefixEnd_1847358 := by exact prefixLift 1847358
  have htrace : WordTrace (prefixWord ++ tailWord_1847358) baseStart_1847358 baseEnd_1847358 := by
    simpa [prefixWord, tailWord_1847358, baseEnd_1847358] using wordTrace_append hprefix tailTrace_1847358
  have hstable : (prefixWord ++ tailWord_1847358).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1847358).length < 2 ^ (prefixWord ++ tailWord_1847358).sum := by decide
  have hdescent : baseEnd_1847358 < baseStart_1847358 := by decide
  rcases family_descends (prefixWord ++ tailWord_1847358) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1847369 : List Nat := [1, 2, 1, 1, 2, 2, 3, 3, 6]
def baseStart_1847369 : Nat := 118140960795 + 1847369 * 2 ^ 59
def prefixEnd_1847369 : Nat := 4983230072969 + 3 ^ 40 * 1847369 * 2
def baseEnd_1847369 : Nat := 421594774762616841774049

theorem tailTrace_1847369 : CollatzResearch.WordTrace tailWord_1847369 prefixEnd_1847369 421594774762616841774049 := by
  unfold tailWord_1847369
  simp only [CollatzResearch.WordTrace]
  refine ⟨67379082844305093351633161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44919388562870062234422107 67379082844305093351633161)
  ·
    refine ⟨50534312133228820013724871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67379082844305093351633161 50534312133228820013724871)
    ·
      refine ⟨75801468199843230020587307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50534312133228820013724871 75801468199843230020587307)
      ·
        refine ⟨113702202299764845030880961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75801468199843230020587307 113702202299764845030880961)
        ·
          refine ⟨85276651724823633773160721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 113702202299764845030880961 85276651724823633773160721)
          ·
            refine ⟨63957488793617725329870541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 85276651724823633773160721 63957488793617725329870541)
            ·
              refine ⟨23984058297606646998701453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 63957488793617725329870541 23984058297606646998701453)
              ·
                refine ⟨8994021861602492624513045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23984058297606646998701453 8994021861602492624513045)
                ·
                  refine ⟨421594774762616841774049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8994021861602492624513045 421594774762616841774049)
                  ·
                    rfl

theorem cell21_1847369_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 3, 3, 6].length) (baseStart_1847369 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1847369 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1847369 prefixEnd_1847369 := by exact prefixLift 1847369
  have htrace : WordTrace (prefixWord ++ tailWord_1847369) baseStart_1847369 baseEnd_1847369 := by
    simpa [prefixWord, tailWord_1847369, baseEnd_1847369] using wordTrace_append hprefix tailTrace_1847369
  have hstable : (prefixWord ++ tailWord_1847369).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1847369).length < 2 ^ (prefixWord ++ tailWord_1847369).sum := by decide
  have hdescent : baseEnd_1847369 < baseStart_1847369 := by decide
  rcases family_descends (prefixWord ++ tailWord_1847369) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1847372 : List Nat := [2, 2, 1, 3, 1, 1, 2, 6, 3]
def baseStart_1847372 : Nat := 118140960795 + 1847372 * 2 ^ 59
def prefixEnd_1847372 : Nat := 4983230072969 + 3 ^ 40 * 1847372 * 2
def baseEnd_1847372 : Nat := 421595459403489503224043

theorem tailTrace_1847372 : CollatzResearch.WordTrace tailWord_1847372 prefixEnd_1847372 421595459403489503224043 := by
  unfold tailWord_1847372
  simp only [CollatzResearch.WordTrace]
  refine ⟨33689596131647112431996185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44919461508862816575994913 33689596131647112431996185)
  ·
    refine ⟨25267197098735334323997139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33689596131647112431996185 25267197098735334323997139)
    ·
      refine ⟨37900795648103001485995709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25267197098735334323997139 37900795648103001485995709)
      ·
        refine ⟨14212798368038625557248391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 37900795648103001485995709 14212798368038625557248391)
        ·
          refine ⟨21319197552057938335872587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14212798368038625557248391 21319197552057938335872587)
          ·
            refine ⟨31978796328086907503808881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21319197552057938335872587 31978796328086907503808881)
            ·
              refine ⟨23984097246065180627856661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31978796328086907503808881 23984097246065180627856661)
              ·
                refine ⟨1124254558409305341930781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 23984097246065180627856661 1124254558409305341930781)
                ·
                  refine ⟨421595459403489503224043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1124254558409305341930781 421595459403489503224043)
                  ·
                    rfl

theorem cell21_1847372_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 2, 6, 3].length) (baseStart_1847372 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1847372 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1847372 prefixEnd_1847372 := by exact prefixLift 1847372
  have htrace : WordTrace (prefixWord ++ tailWord_1847372) baseStart_1847372 baseEnd_1847372 := by
    simpa [prefixWord, tailWord_1847372, baseEnd_1847372] using wordTrace_append hprefix tailTrace_1847372
  have hstable : (prefixWord ++ tailWord_1847372).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1847372).length < 2 ^ (prefixWord ++ tailWord_1847372).sum := by decide
  have hdescent : baseEnd_1847372 < baseStart_1847372 := by decide
  rcases family_descends (prefixWord ++ tailWord_1847372) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1847386 : List Nat := [3, 1, 1, 2, 1, 1, 5, 3, 4]
def baseStart_1847386 : Nat := 118140960795 + 1847386 * 2 ^ 59
def prefixEnd_1847386 : Nat := 4983230072969 + 3 ^ 40 * 1847386 * 2
def baseEnd_1847386 : Nat := 421598654394228589990681

theorem tailTrace_1847386 : CollatzResearch.WordTrace tailWord_1847386 prefixEnd_1847386 421598654394228589990681 := by
  unfold tailWord_1847386
  simp only [CollatzResearch.WordTrace]
  refine ⟨16844925721310876313750503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 44919801923495670170001341 16844925721310876313750503)
  ·
    refine ⟨25267388581966314470625755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16844925721310876313750503 25267388581966314470625755)
    ·
      refine ⟨37901082872949471705938633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25267388581966314470625755 37901082872949471705938633)
      ·
        refine ⟨28425812154712103779453975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37901082872949471705938633 28425812154712103779453975)
        ·
          refine ⟨42638718232068155669180963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28425812154712103779453975 42638718232068155669180963)
          ·
            refine ⟨63958077348102233503771445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42638718232068155669180963 63958077348102233503771445)
            ·
              refine ⟨5996069751384584390978573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 63958077348102233503771445 5996069751384584390978573)
              ·
                refine ⟨2248526156769219146616965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5996069751384584390978573 2248526156769219146616965)
                ·
                  refine ⟨421598654394228589990681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2248526156769219146616965 421598654394228589990681)
                  ·
                    rfl

theorem cell21_1847386_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 5, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 5, 3, 4].length) (baseStart_1847386 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1847386 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1847386 prefixEnd_1847386 := by exact prefixLift 1847386
  have htrace : WordTrace (prefixWord ++ tailWord_1847386) baseStart_1847386 baseEnd_1847386 := by
    simpa [prefixWord, tailWord_1847386, baseEnd_1847386] using wordTrace_append hprefix tailTrace_1847386
  have hstable : (prefixWord ++ tailWord_1847386).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1847386).length < 2 ^ (prefixWord ++ tailWord_1847386).sum := by decide
  have hdescent : baseEnd_1847386 < baseStart_1847386 := by decide
  rcases family_descends (prefixWord ++ tailWord_1847386) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1847448 : List Nat := [2, 1, 2, 4, 3, 1, 1, 2, 5]
def baseStart_1847448 : Nat := 118140960795 + 1847448 * 2 ^ 59
def prefixEnd_1847448 : Nat := 4983230072969 + 3 ^ 40 * 1847448 * 2
def baseEnd_1847448 : Nat := 421612803638930259957221

theorem tailTrace_1847448 : CollatzResearch.WordTrace tailWord_1847448 prefixEnd_1847448 421612803638930259957221 := by
  unfold tailWord_1847448
  simp only [CollatzResearch.WordTrace]
  refine ⟨33690982105509444921879499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44921309474012593229172665 33690982105509444921879499)
  ·
    refine ⟨50536473158264167382819249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33690982105509444921879499 50536473158264167382819249)
    ·
      refine ⟨37902354868698125537114437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50536473158264167382819249 37902354868698125537114437)
      ·
        refine ⟨7106691537880898538208957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 37902354868698125537114437 7106691537880898538208957)
        ·
          refine ⟨2665009326705336951828359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7106691537880898538208957 2665009326705336951828359)
          ·
            refine ⟨3997513990058005427742539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2665009326705336951828359 3997513990058005427742539)
            ·
              refine ⟨5996270985087008141613809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3997513990058005427742539 5996270985087008141613809)
              ·
                refine ⟨4497203238815256106210357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5996270985087008141613809 4497203238815256106210357)
                ·
                  refine ⟨421612803638930259957221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4497203238815256106210357 421612803638930259957221)
                  ·
                    rfl

theorem cell21_1847448_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 3, 1, 1, 2, 5].length) (baseStart_1847448 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1847448 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1847448 prefixEnd_1847448 := by exact prefixLift 1847448
  have htrace : WordTrace (prefixWord ++ tailWord_1847448) baseStart_1847448 baseEnd_1847448 := by
    simpa [prefixWord, tailWord_1847448, baseEnd_1847448] using wordTrace_append hprefix tailTrace_1847448
  have hstable : (prefixWord ++ tailWord_1847448).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1847448).length < 2 ^ (prefixWord ++ tailWord_1847448).sum := by decide
  have hdescent : baseEnd_1847448 < baseStart_1847448 := by decide
  rcases family_descends (prefixWord ++ tailWord_1847448) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1847479 : List Nat := [1, 1, 3, 1, 4, 4, 1, 2, 4]
def baseStart_1847479 : Nat := 118140960795 + 1847479 * 2 ^ 59
def prefixEnd_1847479 : Nat := 4983230072969 + 3 ^ 40 * 1847479 * 2
def baseEnd_1847479 : Nat := 421619878261281094940491

theorem tailTrace_1847479 : CollatzResearch.WordTrace tailWord_1847479 prefixEnd_1847479 421619878261281094940491 := by
  unfold tailWord_1847479
  simp only [CollatzResearch.WordTrace]
  refine ⟨67383094873906582138137491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44922063249271054758758327 67383094873906582138137491)
  ·
    refine ⟨101074642310859873207206237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67383094873906582138137491 101074642310859873207206237)
    ·
      refine ⟨37902990866572452452702339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 101074642310859873207206237 37902990866572452452702339)
      ·
        refine ⟨56854486299858678679053509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37902990866572452452702339 56854486299858678679053509)
        ·
          refine ⟨10660216181223502252322533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 56854486299858678679053509 10660216181223502252322533)
          ·
            refine ⟨1998790533979406672310475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 10660216181223502252322533 1998790533979406672310475)
            ·
              refine ⟨2998185800969110008465713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1998790533979406672310475 2998185800969110008465713)
              ·
                refine ⟨2248639350726832506349285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2998185800969110008465713 2248639350726832506349285)
                ·
                  refine ⟨421619878261281094940491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2248639350726832506349285 421619878261281094940491)
                  ·
                    rfl

theorem cell21_1847479_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 4, 1, 2, 4].length) (baseStart_1847479 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1847479 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1847479 prefixEnd_1847479 := by exact prefixLift 1847479
  have htrace : WordTrace (prefixWord ++ tailWord_1847479) baseStart_1847479 baseEnd_1847479 := by
    simpa [prefixWord, tailWord_1847479, baseEnd_1847479] using wordTrace_append hprefix tailTrace_1847479
  have hstable : (prefixWord ++ tailWord_1847479).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1847479).length < 2 ^ (prefixWord ++ tailWord_1847479).sum := by decide
  have hdescent : baseEnd_1847479 < baseStart_1847479 := by decide
  rcases family_descends (prefixWord ++ tailWord_1847479) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1847510 : List Nat := [5, 2, 1, 2, 1, 2, 1, 7]
def baseStart_1847510 : Nat := 118140960795 + 1847510 * 2 ^ 59
def prefixEnd_1847510 : Nat := 4983230072969 + 3 ^ 40 * 1847510 * 2
def baseEnd_1847510 : Nat := 140542317627877309974587

theorem tailTrace_1847510 : CollatzResearch.WordTrace tailWord_1847510 prefixEnd_1847510 140542317627877309974587 := by
  unfold tailWord_1847510
  simp only [CollatzResearch.WordTrace]
  refine ⟨4211514096049642152032249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 44922817024529516288343989 4211514096049642152032249)
  ·
    refine ⟨3158635572037231614024187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4211514096049642152032249 3158635572037231614024187)
    ·
      refine ⟨4737953358055847421036281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3158635572037231614024187 4737953358055847421036281)
      ·
        refine ⟨3553465018541885565777211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4737953358055847421036281 3553465018541885565777211)
        ·
          refine ⟨5330197527812828348665817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3553465018541885565777211 5330197527812828348665817)
          ·
            refine ⟨3997648145859621261499363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5330197527812828348665817 3997648145859621261499363)
            ·
              refine ⟨5996472218789431892249045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3997648145859621261499363 5996472218789431892249045)
              ·
                refine ⟨140542317627877309974587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5996472218789431892249045 140542317627877309974587)
                ·
                  rfl

theorem cell21_1847510_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 2, 1, 7].length) (baseStart_1847510 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1847510 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1847510 prefixEnd_1847510 := by exact prefixLift 1847510
  have htrace : WordTrace (prefixWord ++ tailWord_1847510) baseStart_1847510 baseEnd_1847510 := by
    simpa [prefixWord, tailWord_1847510, baseEnd_1847510] using wordTrace_append hprefix tailTrace_1847510
  have hstable : (prefixWord ++ tailWord_1847510).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1847510).length < 2 ^ (prefixWord ++ tailWord_1847510).sum := by decide
  have hdescent : baseEnd_1847510 < baseStart_1847510 := by decide
  rcases family_descends (prefixWord ++ tailWord_1847510) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1847516 : List Nat := [2, 2, 5, 2, 2, 1, 1, 3, 3]
def baseStart_1847516 : Nat := 118140960795 + 1847516 * 2 ^ 59
def prefixEnd_1847516 : Nat := 4983230072969 + 3 ^ 40 * 1847516 * 2
def baseEnd_1847516 : Nat := 421628322165377252823749

theorem tailTrace_1847516 : CollatzResearch.WordTrace tailWord_1847516 prefixEnd_1847516 421628322165377252823749 := by
  unfold tailWord_1847516
  simp only [CollatzResearch.WordTrace]
  refine ⟨33692222187386268728617201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44922962916515024971489601 33692222187386268728617201)
  ·
    refine ⟨25269166640539701546462901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33692222187386268728617201 25269166640539701546462901)
    ·
      refine ⟨2368984372550597019980897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 25269166640539701546462901 2368984372550597019980897)
      ·
        refine ⟨1776738279412947764985673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2368984372550597019980897 1776738279412947764985673)
        ·
          refine ⟨1332553709559710823739255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1776738279412947764985673 1332553709559710823739255)
          ·
            refine ⟨1998830564339566235608883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1332553709559710823739255 1998830564339566235608883)
            ·
              refine ⟨2998245846509349353413325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1998830564339566235608883 2998245846509349353413325)
              ·
                refine ⟨1124342192441006007529997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2998245846509349353413325 1124342192441006007529997)
                ·
                  refine ⟨421628322165377252823749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1124342192441006007529997 421628322165377252823749)
                  ·
                    rfl

theorem cell21_1847516_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 2, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 2, 2, 1, 1, 3, 3].length) (baseStart_1847516 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1847516 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1847516 prefixEnd_1847516 := by exact prefixLift 1847516
  have htrace : WordTrace (prefixWord ++ tailWord_1847516) baseStart_1847516 baseEnd_1847516 := by
    simpa [prefixWord, tailWord_1847516, baseEnd_1847516] using wordTrace_append hprefix tailTrace_1847516
  have hstable : (prefixWord ++ tailWord_1847516).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1847516).length < 2 ^ (prefixWord ++ tailWord_1847516).sum := by decide
  have hdescent : baseEnd_1847516 < baseStart_1847516 := by decide
  rcases family_descends (prefixWord ++ tailWord_1847516) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1847521 : List Nat := [1, 2, 3, 1, 3, 1, 1, 1, 8]
def baseStart_1847521 : Nat := 118140960795 + 1847521 * 2 ^ 59
def prefixEnd_1847521 : Nat := 4983230072969 + 3 ^ 40 * 1847521 * 2
def baseEnd_1847521 : Nat := 421629463233498355240405

theorem tailTrace_1847521 : CollatzResearch.WordTrace tailWord_1847521 prefixEnd_1847521 421629463233498355240405 := by
  unfold tailWord_1847521
  simp only [CollatzResearch.WordTrace]
  refine ⟨67384626739754423311166417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44923084493169615540777611 67384626739754423311166417)
  ·
    refine ⟨50538470054815817483374813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67384626739754423311166417 50538470054815817483374813)
    ·
      refine ⟨18951926270555931556265555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 50538470054815817483374813 18951926270555931556265555)
      ·
        refine ⟨28427889405833897334398333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18951926270555931556265555 28427889405833897334398333)
        ·
          refine ⟨10660458527187711500399375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28427889405833897334398333 10660458527187711500399375)
          ·
            refine ⟨15990687790781567250599063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10660458527187711500399375 15990687790781567250599063)
            ·
              refine ⟨23986031686172350875898595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15990687790781567250599063 23986031686172350875898595)
              ·
                refine ⟨35979047529258526313847893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23986031686172350875898595 35979047529258526313847893)
                ·
                  refine ⟨421629463233498355240405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 35979047529258526313847893 421629463233498355240405)
                  ·
                    rfl

theorem cell21_1847521_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 1, 1, 8].length) (baseStart_1847521 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1847521 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1847521 prefixEnd_1847521 := by exact prefixLift 1847521
  have htrace : WordTrace (prefixWord ++ tailWord_1847521) baseStart_1847521 baseEnd_1847521 := by
    simpa [prefixWord, tailWord_1847521, baseEnd_1847521] using wordTrace_append hprefix tailTrace_1847521
  have hstable : (prefixWord ++ tailWord_1847521).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1847521).length < 2 ^ (prefixWord ++ tailWord_1847521).sum := by decide
  have hdescent : baseEnd_1847521 < baseStart_1847521 := by decide
  rcases family_descends (prefixWord ++ tailWord_1847521) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1847538 : List Nat := [3, 2, 1, 3, 2, 1, 2, 1, 6]
def baseStart_1847538 : Nat := 118140960795 + 1847538 * 2 ^ 59
def prefixEnd_1847538 : Nat := 4983230072969 + 3 ^ 40 * 1847538 * 2
def baseEnd_1847538 : Nat := 421633342865110103457037

theorem tailTrace_1847538 : CollatzResearch.WordTrace tailWord_1847538 prefixEnd_1847538 421633342865110103457037 := by
  unfold tailWord_1847538
  simp only [CollatzResearch.WordTrace]
  refine ⟨16846311695173208803633817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 44923497853795223476356845 16846311695173208803633817)
  ·
    refine ⟨12634733771379906602725363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16846311695173208803633817 12634733771379906602725363)
    ·
      refine ⟨18952100657069859904088045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12634733771379906602725363 18952100657069859904088045)
      ·
        refine ⟨7107037746401197464033017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18952100657069859904088045 7107037746401197464033017)
        ·
          refine ⟨5330278309800898098024763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7107037746401197464033017 5330278309800898098024763)
          ·
            refine ⟨7995417464701347147037145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5330278309800898098024763 7995417464701347147037145)
            ·
              refine ⟨5996563098526010360277859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7995417464701347147037145 5996563098526010360277859)
              ·
                refine ⟨8994844647789015540416789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5996563098526010360277859 8994844647789015540416789)
                ·
                  refine ⟨421633342865110103457037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8994844647789015540416789 421633342865110103457037)
                  ·
                    rfl

theorem cell21_1847538_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 1, 2, 1, 6].length) (baseStart_1847538 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1847538 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1847538 prefixEnd_1847538 := by exact prefixLift 1847538
  have htrace : WordTrace (prefixWord ++ tailWord_1847538) baseStart_1847538 baseEnd_1847538 := by
    simpa [prefixWord, tailWord_1847538, baseEnd_1847538] using wordTrace_append hprefix tailTrace_1847538
  have hstable : (prefixWord ++ tailWord_1847538).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1847538).length < 2 ^ (prefixWord ++ tailWord_1847538).sum := by decide
  have hdescent : baseEnd_1847538 < baseStart_1847538 := by decide
  rcases family_descends (prefixWord ++ tailWord_1847538) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1847642 : List Nat := [3, 1, 1, 2, 1, 2, 1, 1, 9]
def baseStart_1847642 : Nat := 118140960795 + 1847642 * 2 ^ 59
def prefixEnd_1847642 : Nat := 4983230072969 + 3 ^ 40 * 1847642 * 2
def baseEnd_1847642 : Nat := 421657077082029033723491

theorem tailTrace_1847642 : CollatzResearch.WordTrace tailWord_1847642 prefixEnd_1847642 421657077082029033723491 := by
  unfold tailWord_1847642
  simp only [CollatzResearch.WordTrace]
  refine ⟨16847259993079015244080295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 44926026648210707317547453 16847259993079015244080295)
  ·
    refine ⟨25270889989618522866120443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16847259993079015244080295 25270889989618522866120443)
    ·
      refine ⟨37906334984427784299180665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25270889989618522866120443 37906334984427784299180665)
      ·
        refine ⟨28429751238320838224385499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37906334984427784299180665 28429751238320838224385499)
        ·
          refine ⟨42644626857481257336578249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28429751238320838224385499 42644626857481257336578249)
          ·
            refine ⟨31983470143110943002433687, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42644626857481257336578249 31983470143110943002433687)
            ·
              refine ⟨47975205214666414503650531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31983470143110943002433687 47975205214666414503650531)
              ·
                refine ⟨71962807821999621755475797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47975205214666414503650531 71962807821999621755475797)
                ·
                  refine ⟨421657077082029033723491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 71962807821999621755475797 421657077082029033723491)
                  ·
                    rfl

theorem cell21_1847642_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 1, 1, 9].length) (baseStart_1847642 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1847642 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1847642 prefixEnd_1847642 := by exact prefixLift 1847642
  have htrace : WordTrace (prefixWord ++ tailWord_1847642) baseStart_1847642 baseEnd_1847642 := by
    simpa [prefixWord, tailWord_1847642, baseEnd_1847642] using wordTrace_append hprefix tailTrace_1847642
  have hstable : (prefixWord ++ tailWord_1847642).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1847642).length < 2 ^ (prefixWord ++ tailWord_1847642).sum := by decide
  have hdescent : baseEnd_1847642 < baseStart_1847642 := by decide
  rcases family_descends (prefixWord ++ tailWord_1847642) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1847648 : List Nat := [2, 1, 1, 3, 6, 1, 1, 2, 4]
def baseStart_1847648 : Nat := 118140960795 + 1847648 * 2 ^ 59
def prefixEnd_1847648 : Nat := 4983230072969 + 3 ^ 40 * 1847648 * 2
def baseEnd_1847648 : Nat := 421658446363774356623479

theorem tailTrace_1847648 : CollatzResearch.WordTrace tailWord_1847648 prefixEnd_1847648 421658446363774356623479 := by
  unfold tailWord_1847648
  simp only [CollatzResearch.WordTrace]
  refine ⟨33694629405147162000519799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44926172540196216000693065 33694629405147162000519799)
  ·
    refine ⟨50541944107720743000779699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33694629405147162000519799 50541944107720743000779699)
    ·
      refine ⟨75812916161581114501169549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50541944107720743000779699 75812916161581114501169549)
      ·
        refine ⟨28429843560592917937938581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 75812916161581114501169549 28429843560592917937938581)
        ·
          refine ⟨1332648916902793028340871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 28429843560592917937938581 1332648916902793028340871)
          ·
            refine ⟨1998973375354189542511307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1332648916902793028340871 1998973375354189542511307)
            ·
              refine ⟨2998460063031284313766961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1998973375354189542511307 2998460063031284313766961)
              ·
                refine ⟨2248845047273463235325221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2998460063031284313766961 2248845047273463235325221)
                ·
                  refine ⟨421658446363774356623479, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2248845047273463235325221 421658446363774356623479)
                  ·
                    rfl

theorem cell21_1847648_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 6, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 6, 1, 1, 2, 4].length) (baseStart_1847648 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1847648 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1847648 prefixEnd_1847648 := by exact prefixLift 1847648
  have htrace : WordTrace (prefixWord ++ tailWord_1847648) baseStart_1847648 baseEnd_1847648 := by
    simpa [prefixWord, tailWord_1847648, baseEnd_1847648] using wordTrace_append hprefix tailTrace_1847648
  have hstable : (prefixWord ++ tailWord_1847648).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1847648).length < 2 ^ (prefixWord ++ tailWord_1847648).sum := by decide
  have hdescent : baseEnd_1847648 < baseStart_1847648 := by decide
  rcases family_descends (prefixWord ++ tailWord_1847648) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1847704 : List Nat := [2, 1, 2, 5, 1, 1, 9]
def baseStart_1847704 : Nat := 118140960795 + 1847704 * 2 ^ 59
def prefixEnd_1847704 : Nat := 4983230072969 + 3 ^ 40 * 1847704 * 2
def baseEnd_1847704 : Nat := 46852358480747855965559

theorem tailTrace_1847704 : CollatzResearch.WordTrace tailWord_1847704 prefixEnd_1847704 46852358480747855965559 := by
  unfold tailWord_1847704
  simp only [CollatzResearch.WordTrace]
  refine ⟨33695650649045722782539083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44927534198727630376718777 33695650649045722782539083)
  ·
    refine ⟨50543475973568584173808625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33695650649045722782539083 50543475973568584173808625)
    ·
      refine ⟨37907606980176438130356469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50543475973568584173808625 37907606980176438130356469)
      ·
        refine ⟨3553838154391541074720919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 37907606980176438130356469 3553838154391541074720919)
        ·
          refine ⟨5330757231587311612081379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3553838154391541074720919 5330757231587311612081379)
          ·
            refine ⟨7996135847380967418122069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5330757231587311612081379 7996135847380967418122069)
            ·
              refine ⟨46852358480747855965559, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 7996135847380967418122069 46852358480747855965559)
              ·
                rfl

theorem cell21_1847704_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 1, 9].length) (baseStart_1847704 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1847704 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1847704 prefixEnd_1847704 := by exact prefixLift 1847704
  have htrace : WordTrace (prefixWord ++ tailWord_1847704) baseStart_1847704 baseEnd_1847704 := by
    simpa [prefixWord, tailWord_1847704, baseEnd_1847704] using wordTrace_append hprefix tailTrace_1847704
  have hstable : (prefixWord ++ tailWord_1847704).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1847704).length < 2 ^ (prefixWord ++ tailWord_1847704).sum := by decide
  have hdescent : baseEnd_1847704 < baseStart_1847704 := by decide
  rcases family_descends (prefixWord ++ tailWord_1847704) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1847825 : List Nat := [1, 2, 2, 1, 1, 2, 2, 6, 4]
def baseStart_1847825 : Nat := 118140960795 + 1847825 * 2 ^ 59
def prefixEnd_1847825 : Nat := 4983230072969 + 3 ^ 40 * 1847825 * 2
def baseEnd_1847825 : Nat := 421698840175261382173117

theorem tailTrace_1847825 : CollatzResearch.WordTrace tailWord_1847825 prefixEnd_1847825 421698840175261382173117 := by
  unfold tailWord_1847825
  simp only [CollatzResearch.WordTrace]
  refine ⟨67395714530653083230232929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44930476353768722153488619 67395714530653083230232929)
  ·
    refine ⟨50546785897989812422674697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67395714530653083230232929 50546785897989812422674697)
    ·
      refine ⟨37910089423492359317006023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50546785897989812422674697 37910089423492359317006023)
      ·
        refine ⟨56865134135238538975509035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37910089423492359317006023 56865134135238538975509035)
        ·
          refine ⟨85297701202857808463263553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56865134135238538975509035 85297701202857808463263553)
          ·
            refine ⟨63973275902143356347447665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 85297701202857808463263553 63973275902143356347447665)
            ·
              refine ⟨47979956926607517260585749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 63973275902143356347447665 47979956926607517260585749)
              ·
                refine ⟨2249060480934727371589957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 47979956926607517260585749 2249060480934727371589957)
                ·
                  refine ⟨421698840175261382173117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2249060480934727371589957 421698840175261382173117)
                  ·
                    rfl

theorem cell21_1847825_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 2, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 2, 6, 4].length) (baseStart_1847825 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1847825 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1847825 prefixEnd_1847825 := by exact prefixLift 1847825
  have htrace : WordTrace (prefixWord ++ tailWord_1847825) baseStart_1847825 baseEnd_1847825 := by
    simpa [prefixWord, tailWord_1847825, baseEnd_1847825] using wordTrace_append hprefix tailTrace_1847825
  have hstable : (prefixWord ++ tailWord_1847825).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1847825).length < 2 ^ (prefixWord ++ tailWord_1847825).sum := by decide
  have hdescent : baseEnd_1847825 < baseStart_1847825 := by decide
  rcases family_descends (prefixWord ++ tailWord_1847825) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1847828 : List Nat := [2, 4, 3, 1, 1, 1, 1, 3, 5]
def baseStart_1847828 : Nat := 118140960795 + 1847828 * 2 ^ 59
def prefixEnd_1847828 : Nat := 4983230072969 + 3 ^ 40 * 1847828 * 2
def baseEnd_1847828 : Nat := 421699524816134043623111

theorem tailTrace_1847828 : CollatzResearch.WordTrace tailWord_1847828 prefixEnd_1847828 421699524816134043623111 := by
  unfold tailWord_1847828
  simp only [CollatzResearch.WordTrace]
  refine ⟨33697911974821107371296069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44930549299761476495061425 33697911974821107371296069)
  ·
    refine ⟨6318358495278957632118013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 33697911974821107371296069 6318358495278957632118013)
    ·
      refine ⟨2369384435729609112044255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6318358495278957632118013 2369384435729609112044255)
      ·
        refine ⟨3554076653594413668066383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2369384435729609112044255 3554076653594413668066383)
        ·
          refine ⟨5331114980391620502099575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3554076653594413668066383 5331114980391620502099575)
          ·
            refine ⟨7996672470587430753149363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5331114980391620502099575 7996672470587430753149363)
            ·
              refine ⟨11995008705881146129724045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7996672470587430753149363 11995008705881146129724045)
              ·
                refine ⟨4498128264705429798646517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11995008705881146129724045 4498128264705429798646517)
                ·
                  refine ⟨421699524816134043623111, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4498128264705429798646517 421699524816134043623111)
                  ·
                    rfl

theorem cell21_1847828_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 1, 1, 3, 5].length) (baseStart_1847828 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1847828 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1847828 prefixEnd_1847828 := by exact prefixLift 1847828
  have htrace : WordTrace (prefixWord ++ tailWord_1847828) baseStart_1847828 baseEnd_1847828 := by
    simpa [prefixWord, tailWord_1847828, baseEnd_1847828] using wordTrace_append hprefix tailTrace_1847828
  have hstable : (prefixWord ++ tailWord_1847828).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1847828).length < 2 ^ (prefixWord ++ tailWord_1847828).sum := by decide
  have hdescent : baseEnd_1847828 < baseStart_1847828 := by decide
  rcases family_descends (prefixWord ++ tailWord_1847828) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1847839 : List Nat := [1, 1, 2, 4, 1, 1, 1, 10]
def baseStart_1847839 : Nat := 118140960795 + 1847839 * 2 ^ 59
def prefixEnd_1847839 : Nat := 4983230072969 + 3 ^ 40 * 1847839 * 2
def baseEnd_1847839 : Nat := 140567345055333489646585

theorem tailTrace_1847839 : CollatzResearch.WordTrace tailWord_1847839 prefixEnd_1847839 140567345055333489646585 := by
  unfold tailWord_1847839
  simp only [CollatzResearch.WordTrace]
  refine ⟨67396225152602363621242571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44930816768401575747495047 67396225152602363621242571)
  ·
    refine ⟨101094337728903545431863857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67396225152602363621242571 101094337728903545431863857)
    ·
      refine ⟨75820753296677659073897893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 101094337728903545431863857 75820753296677659073897893)
      ·
        refine ⟨14216391243127061076355855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 75820753296677659073897893 14216391243127061076355855)
        ·
          refine ⟨21324586864690591614533783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14216391243127061076355855 21324586864690591614533783)
          ·
            refine ⟨31986880297035887421800675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21324586864690591614533783 31986880297035887421800675)
            ·
              refine ⟨47980320445553831132701013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31986880297035887421800675 47980320445553831132701013)
              ·
                refine ⟨140567345055333489646585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 47980320445553831132701013 140567345055333489646585)
                ·
                  rfl

theorem cell21_1847839_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 1, 10].length) (baseStart_1847839 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1847839 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1847839 prefixEnd_1847839 := by exact prefixLift 1847839
  have htrace : WordTrace (prefixWord ++ tailWord_1847839) baseStart_1847839 baseEnd_1847839 := by
    simpa [prefixWord, tailWord_1847839, baseEnd_1847839] using wordTrace_append hprefix tailTrace_1847839
  have hstable : (prefixWord ++ tailWord_1847839).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1847839).length < 2 ^ (prefixWord ++ tailWord_1847839).sum := by decide
  have hdescent : baseEnd_1847839 < baseStart_1847839 := by decide
  rcases family_descends (prefixWord ++ tailWord_1847839) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1847856 : List Nat := [2, 1, 1, 1, 2, 3, 6, 5]
def baseStart_1847856 : Nat := 118140960795 + 1847856 * 2 ^ 59
def prefixEnd_1847856 : Nat := 4983230072969 + 3 ^ 40 * 1847856 * 2
def baseEnd_1847856 : Nat := 140568638265870739052129

theorem tailTrace_1847856 : CollatzResearch.WordTrace tailWord_1847856 prefixEnd_1847856 140568638265870739052129 := by
  unfold tailWord_1847856
  simp only [CollatzResearch.WordTrace]
  refine ⟨33698422596770387762305711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44931230129027183683074281 33698422596770387762305711)
  ·
    refine ⟨50547633895155581643458567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33698422596770387762305711 50547633895155581643458567)
    ·
      refine ⟨75821450842733372465187851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50547633895155581643458567 75821450842733372465187851)
      ·
        refine ⟨113732176264100058697781777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75821450842733372465187851 113732176264100058697781777)
        ·
          refine ⟨85299132198075044023336333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 113732176264100058697781777 85299132198075044023336333)
          ·
            refine ⟨31987174574278141508751125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 85299132198075044023336333 31987174574278141508751125)
            ·
              refine ⟨1499398808169287883222709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 31987174574278141508751125 1499398808169287883222709)
              ·
                refine ⟨140568638265870739052129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1499398808169287883222709 140568638265870739052129)
                ·
                  rfl

theorem cell21_1847856_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 6, 5].length) (baseStart_1847856 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1847856 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1847856 prefixEnd_1847856 := by exact prefixLift 1847856
  have htrace : WordTrace (prefixWord ++ tailWord_1847856) baseStart_1847856 baseEnd_1847856 := by
    simpa [prefixWord, tailWord_1847856, baseEnd_1847856] using wordTrace_append hprefix tailTrace_1847856
  have hstable : (prefixWord ++ tailWord_1847856).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1847856).length < 2 ^ (prefixWord ++ tailWord_1847856).sum := by decide
  have hdescent : baseEnd_1847856 < baseStart_1847856 := by decide
  rcases family_descends (prefixWord ++ tailWord_1847856) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1847862 : List Nat := [5, 1, 2, 1, 2, 3, 1, 3, 3]
def baseStart_1847862 : Nat := 118140960795 + 1847862 * 2 ^ 59
def prefixEnd_1847862 : Nat := 4983230072969 + 3 ^ 40 * 1847862 * 2
def baseEnd_1847862 : Nat := 421707284079357540056375

theorem tailTrace_1847862 : CollatzResearch.WordTrace tailWord_1847862 prefixEnd_1847862 421707284079357540056375 := by
  unfold tailWord_1847862
  simp only [CollatzResearch.WordTrace]
  refine ⟨4212316501969939909333115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 44931376021012692366219893 4212316501969939909333115)
  ·
    refine ⟨6318474752954909863999673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4212316501969939909333115 6318474752954909863999673)
    ·
      refine ⟨4738856064716182397999755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6318474752954909863999673 4738856064716182397999755)
      ·
        refine ⟨7108284097074273596999633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4738856064716182397999755 7108284097074273596999633)
        ·
          refine ⟨5331213072805705197749725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7108284097074273596999633 5331213072805705197749725)
          ·
            refine ⟨1999204902302139449156147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5331213072805705197749725 1999204902302139449156147)
            ·
              refine ⟨2998807353453209173734221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1999204902302139449156147 2998807353453209173734221)
              ·
                refine ⟨1124552757544953440150333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2998807353453209173734221 1124552757544953440150333)
                ·
                  refine ⟨421707284079357540056375, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1124552757544953440150333 421707284079357540056375)
                  ·
                    rfl

theorem cell21_1847862_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 3, 1, 3, 3].length) (baseStart_1847862 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1847862 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1847862 prefixEnd_1847862 := by exact prefixLift 1847862
  have htrace : WordTrace (prefixWord ++ tailWord_1847862) baseStart_1847862 baseEnd_1847862 := by
    simpa [prefixWord, tailWord_1847862, baseEnd_1847862] using wordTrace_append hprefix tailTrace_1847862
  have hstable : (prefixWord ++ tailWord_1847862).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1847862).length < 2 ^ (prefixWord ++ tailWord_1847862).sum := by decide
  have hdescent : baseEnd_1847862 < baseStart_1847862 := by decide
  rcases family_descends (prefixWord ++ tailWord_1847862) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1847887 : List Nat := [1, 1, 2, 1, 1, 2, 4, 6, 3]
def baseStart_1847887 : Nat := 118140960795 + 1847887 * 2 ^ 59
def prefixEnd_1847887 : Nat := 4983230072969 + 3 ^ 40 * 1847887 * 2
def baseEnd_1847887 : Nat := 421712989419963052139657

theorem tailTrace_1847887 : CollatzResearch.WordTrace tailWord_1847887 prefixEnd_1847887 421712989419963052139657 := by
  unfold tailWord_1847887
  simp only [CollatzResearch.WordTrace]
  refine ⟨67397975856428467818989915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44931983904285645212659943 67397975856428467818989915)
  ·
    refine ⟨101096963784642701728484873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67397975856428467818989915 101096963784642701728484873)
    ·
      refine ⟨75822722838482026296363655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 101096963784642701728484873 75822722838482026296363655)
      ·
        refine ⟨113734084257723039444545483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75822722838482026296363655 113734084257723039444545483)
        ·
          refine ⟨170601126386584559166818225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 113734084257723039444545483 170601126386584559166818225)
          ·
            refine ⟨127950844789938419375113669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 170601126386584559166818225 127950844789938419375113669)
            ·
              refine ⟨23990783398113453632833813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 127950844789938419375113669 23990783398113453632833813)
              ·
                refine ⟨1124567971786568139039085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 23990783398113453632833813 1124567971786568139039085)
                ·
                  refine ⟨421712989419963052139657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1124567971786568139039085 421712989419963052139657)
                  ·
                    rfl

theorem cell21_1847887_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 4, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 4, 6, 3].length) (baseStart_1847887 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1847887 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1847887 prefixEnd_1847887 := by exact prefixLift 1847887
  have htrace : WordTrace (prefixWord ++ tailWord_1847887) baseStart_1847887 baseEnd_1847887 := by
    simpa [prefixWord, tailWord_1847887, baseEnd_1847887] using wordTrace_append hprefix tailTrace_1847887
  have hstable : (prefixWord ++ tailWord_1847887).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1847887).length < 2 ^ (prefixWord ++ tailWord_1847887).sum := by decide
  have hdescent : baseEnd_1847887 < baseStart_1847887 := by decide
  rcases family_descends (prefixWord ++ tailWord_1847887) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1848056 : List Nat := [2, 1, 2, 1, 1, 2, 7, 2, 3]
def baseStart_1848056 : Nat := 118140960795 + 1848056 * 2 ^ 59
def prefixEnd_1848056 : Nat := 4983230072969 + 3 ^ 40 * 1848056 * 2
def baseEnd_1848056 : Nat := 421751557522456313822645

theorem tailTrace_1848056 : CollatzResearch.WordTrace tailWord_1848056 prefixEnd_1848056 421751557522456313822645 := by
  unfold tailWord_1848056
  simp only [CollatzResearch.WordTrace]
  refine ⟨33702069896408104840946011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44936093195210806454594681 33702069896408104840946011)
  ·
    refine ⟨50553104844612157261419017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33702069896408104840946011 50553104844612157261419017)
    ·
      refine ⟨37914828633459117946064263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50553104844612157261419017 37914828633459117946064263)
      ·
        refine ⟨56872242950188676919096395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37914828633459117946064263 56872242950188676919096395)
        ·
          refine ⟨85308364425283015378644593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56872242950188676919096395 85308364425283015378644593)
          ·
            refine ⟨63981273318962261533983445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 85308364425283015378644593 63981273318962261533983445)
            ·
              refine ⟨1499561093413178004702737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 63981273318962261533983445 1499561093413178004702737)
              ·
                refine ⟨1124670820059883503527053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1499561093413178004702737 1124670820059883503527053)
                ·
                  refine ⟨421751557522456313822645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1124670820059883503527053 421751557522456313822645)
                  ·
                    rfl

theorem cell21_1848056_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 7, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 7, 2, 3].length) (baseStart_1848056 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1848056 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1848056 prefixEnd_1848056 := by exact prefixLift 1848056
  have htrace : WordTrace (prefixWord ++ tailWord_1848056) baseStart_1848056 baseEnd_1848056 := by
    simpa [prefixWord, tailWord_1848056, baseEnd_1848056] using wordTrace_append hprefix tailTrace_1848056
  have hstable : (prefixWord ++ tailWord_1848056).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1848056).length < 2 ^ (prefixWord ++ tailWord_1848056).sum := by decide
  have hdescent : baseEnd_1848056 < baseStart_1848056 := by decide
  rcases family_descends (prefixWord ++ tailWord_1848056) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1848112 : List Nat := [2, 1, 1, 1, 2, 2, 1, 5, 6]
def baseStart_1848112 : Nat := 118140960795 + 1848112 * 2 ^ 59
def prefixEnd_1848112 : Nat := 4983230072969 + 3 ^ 40 * 1848112 * 2
def baseEnd_1848112 : Nat := 421764337485412660889197

theorem tailTrace_1848112 : CollatzResearch.WordTrace tailWord_1848112 prefixEnd_1848112 421764337485412660889197 := by
  unfold tailWord_1848112
  simp only [CollatzResearch.WordTrace]
  refine ⟨33703091140306665622965295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44937454853742220830620393 33703091140306665622965295)
  ·
    refine ⟨50554636710459998434447943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33703091140306665622965295 50554636710459998434447943)
    ·
      refine ⟨75831955065689997651671915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50554636710459998434447943 75831955065689997651671915)
      ·
        refine ⟨113747932598534996477507873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75831955065689997651671915 113747932598534996477507873)
        ·
          refine ⟨85310949448901247358130905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 113747932598534996477507873 85310949448901247358130905)
          ·
            refine ⟨63983212086675935518598179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 85310949448901247358130905 63983212086675935518598179)
            ·
              refine ⟨95974818130013903277897269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63983212086675935518598179 95974818130013903277897269)
              ·
                refine ⟨8997639199688803432302869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 95974818130013903277897269 8997639199688803432302869)
                ·
                  refine ⟨421764337485412660889197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8997639199688803432302869 421764337485412660889197)
                  ·
                    rfl

theorem cell21_1848112_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 1, 5, 6].length) (baseStart_1848112 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1848112 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1848112 prefixEnd_1848112 := by exact prefixLift 1848112
  have htrace : WordTrace (prefixWord ++ tailWord_1848112) baseStart_1848112 baseEnd_1848112 := by
    simpa [prefixWord, tailWord_1848112, baseEnd_1848112] using wordTrace_append hprefix tailTrace_1848112
  have hstable : (prefixWord ++ tailWord_1848112).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1848112).length < 2 ^ (prefixWord ++ tailWord_1848112).sum := by decide
  have hdescent : baseEnd_1848112 < baseStart_1848112 := by decide
  rcases family_descends (prefixWord ++ tailWord_1848112) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1848118 : List Nat := [5, 1, 2, 2, 2, 2, 1, 6]
def baseStart_1848118 : Nat := 118140960795 + 1848118 * 2 ^ 59
def prefixEnd_1848118 : Nat := 4983230072969 + 3 ^ 40 * 1848118 * 2
def baseEnd_1848118 : Nat := 140588568922385994596395

theorem tailTrace_1848118 : CollatzResearch.WordTrace tailWord_1848118 prefixEnd_1848118 140588568922385994596395 := by
  unfold tailWord_1848118
  simp only [CollatzResearch.WordTrace]
  refine ⟨4212900069911974641915563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 44937600745727729513766005 4212900069911974641915563)
  ·
    refine ⟨6319350104867961962873345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4212900069911974641915563 6319350104867961962873345)
    ·
      refine ⟨4739512578650971472155009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6319350104867961962873345 4739512578650971472155009)
      ·
        refine ⟨3554634433988228604116257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4739512578650971472155009 3554634433988228604116257)
        ·
          refine ⟨2665975825491171453087193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3554634433988228604116257 2665975825491171453087193)
          ·
            refine ⟨1999481869118378589815395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2665975825491171453087193 1999481869118378589815395)
            ·
              refine ⟨2999222803677567884723093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1999481869118378589815395 2999222803677567884723093)
              ·
                refine ⟨140588568922385994596395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2999222803677567884723093 140588568922385994596395)
                ·
                  rfl

theorem cell21_1848118_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 2, 2, 1, 6].length) (baseStart_1848118 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1848118 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1848118 prefixEnd_1848118 := by exact prefixLift 1848118
  have htrace : WordTrace (prefixWord ++ tailWord_1848118) baseStart_1848118 baseEnd_1848118 := by
    simpa [prefixWord, tailWord_1848118, baseEnd_1848118] using wordTrace_append hprefix tailTrace_1848118
  have hstable : (prefixWord ++ tailWord_1848118).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1848118).length < 2 ^ (prefixWord ++ tailWord_1848118).sum := by decide
  have hdescent : baseEnd_1848118 < baseStart_1848118 := by decide
  rcases family_descends (prefixWord ++ tailWord_1848118) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1848194 : List Nat := [3, 4, 2, 2, 1, 1, 1, 7]
def baseStart_1848194 : Nat := 118140960795 + 1848194 * 2 ^ 59
def prefixEnd_1848194 : Nat := 4983230072969 + 3 ^ 40 * 1848194 * 2
def baseEnd_1848194 : Nat := 140594350334199580174121

theorem tailTrace_1848194 : CollatzResearch.WordTrace tailWord_1848194 prefixEnd_1848194 140594350334199580174121 := by
  unfold tailWord_1848194
  simp only [CollatzResearch.WordTrace]
  refine ⟨16852293266579064812603909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 44939448710877506166943757 16852293266579064812603909)
  ·
    refine ⟨3159804987483574652363233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 16852293266579064812603909 3159804987483574652363233)
    ·
      refine ⟨2369853740612680989272425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3159804987483574652363233 2369853740612680989272425)
      ·
        refine ⟨1777390305459510741954319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2369853740612680989272425 1777390305459510741954319)
        ·
          refine ⟨2666085458189266112931479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1777390305459510741954319 2666085458189266112931479)
          ·
            refine ⟨3999128187283899169397219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2666085458189266112931479 3999128187283899169397219)
            ·
              refine ⟨5998692280925848754095829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3999128187283899169397219 5998692280925848754095829)
              ·
                refine ⟨140594350334199580174121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5998692280925848754095829 140594350334199580174121)
                ·
                  rfl

theorem cell21_1848194_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 2, 1, 1, 1, 7].length) (baseStart_1848194 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1848194 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1848194 prefixEnd_1848194 := by exact prefixLift 1848194
  have htrace : WordTrace (prefixWord ++ tailWord_1848194) baseStart_1848194 baseEnd_1848194 := by
    simpa [prefixWord, tailWord_1848194, baseEnd_1848194] using wordTrace_append hprefix tailTrace_1848194
  have hstable : (prefixWord ++ tailWord_1848194).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1848194).length < 2 ^ (prefixWord ++ tailWord_1848194).sum := by decide
  have hdescent : baseEnd_1848194 < baseStart_1848194 := by decide
  rcases family_descends (prefixWord ++ tailWord_1848194) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1848225 : List Nat := [1, 2, 3, 4, 1, 2, 3, 2, 3]
def baseStart_1848225 : Nat := 118140960795 + 1848225 * 2 ^ 59
def prefixEnd_1848225 : Nat := 4983230072969 + 3 ^ 40 * 1848225 * 2
def baseEnd_1848225 : Nat := 421790125624949575505633

theorem tailTrace_1848225 : CollatzResearch.WordTrace tailWord_1848225 prefixEnd_1848225 421790125624949575505633 := by
  unfold tailWord_1848225
  simp only [CollatzResearch.WordTrace]
  refine ⟨67410303729203951544794129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44940202486135967696529419 67410303729203951544794129)
  ·
    refine ⟨50557727796902963658595597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67410303729203951544794129 50557727796902963658595597)
    ·
      refine ⟨18959147923838611371973349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 50557727796902963658595597 18959147923838611371973349)
      ·
        refine ⟨3554840235719739632245003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 18959147923838611371973349 3554840235719739632245003)
        ·
          refine ⟨5332260353579609448367505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3554840235719739632245003 5332260353579609448367505)
          ·
            refine ⟨3999195265184707086275629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5332260353579609448367505 3999195265184707086275629)
            ·
              refine ⟨1499698224444265157353361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3999195265184707086275629 1499698224444265157353361)
              ·
                refine ⟨1124773668333198868015021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1499698224444265157353361 1124773668333198868015021)
                ·
                  refine ⟨421790125624949575505633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1124773668333198868015021 421790125624949575505633)
                  ·
                    rfl

theorem cell21_1848225_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 2, 3, 2, 3].length) (baseStart_1848225 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1848225 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1848225 prefixEnd_1848225 := by exact prefixLift 1848225
  have htrace : WordTrace (prefixWord ++ tailWord_1848225) baseStart_1848225 baseEnd_1848225 := by
    simpa [prefixWord, tailWord_1848225, baseEnd_1848225] using wordTrace_append hprefix tailTrace_1848225
  have hstable : (prefixWord ++ tailWord_1848225).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1848225).length < 2 ^ (prefixWord ++ tailWord_1848225).sum := by decide
  have hdescent : baseEnd_1848225 < baseStart_1848225 := by decide
  rcases family_descends (prefixWord ++ tailWord_1848225) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1848281 : List Nat := [1, 2, 1, 2, 5, 1, 1, 4, 4]
def baseStart_1848281 : Nat := 118140960795 + 1848281 * 2 ^ 59
def prefixEnd_1848281 : Nat := 4983230072969 + 3 ^ 40 * 1848281 * 2
def baseEnd_1848281 : Nat := 421802905587905922572185

theorem tailTrace_1848281 : CollatzResearch.WordTrace tailWord_1848281 prefixEnd_1848281 421802905587905922572185 := by
  unfold tailWord_1848281
  simp only [CollatzResearch.WordTrace]
  refine ⟨67412346217001073108832697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44941564144667382072555131 67412346217001073108832697)
  ·
    refine ⟨50559259662750804831624523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67412346217001073108832697 50559259662750804831624523)
    ·
      refine ⟨75838889494126207247436785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50559259662750804831624523 75838889494126207247436785)
      ·
        refine ⟨56879167120594655435577589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 75838889494126207247436785 56879167120594655435577589)
        ·
          refine ⟨5332421917555748947085399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 56879167120594655435577589 5332421917555748947085399)
          ·
            refine ⟨7998632876333623420628099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5332421917555748947085399 7998632876333623420628099)
            ·
              refine ⟨11997949314500435130942149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7998632876333623420628099 11997949314500435130942149)
              ·
                refine ⟨2249615496468831587051653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11997949314500435130942149 2249615496468831587051653)
                ·
                  refine ⟨421802905587905922572185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2249615496468831587051653 421802905587905922572185)
                  ·
                    rfl

theorem cell21_1848281_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 1, 1, 4, 4].length) (baseStart_1848281 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1848281 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1848281 prefixEnd_1848281 := by exact prefixLift 1848281
  have htrace : WordTrace (prefixWord ++ tailWord_1848281) baseStart_1848281 baseEnd_1848281 := by
    simpa [prefixWord, tailWord_1848281, baseEnd_1848281] using wordTrace_append hprefix tailTrace_1848281
  have hstable : (prefixWord ++ tailWord_1848281).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1848281).length < 2 ^ (prefixWord ++ tailWord_1848281).sum := by decide
  have hdescent : baseEnd_1848281 < baseStart_1848281 := by decide
  rcases family_descends (prefixWord ++ tailWord_1848281) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1848343 : List Nat := [1, 1, 3, 5, 1, 2, 2, 1, 5]
def baseStart_1848343 : Nat := 118140960795 + 1848343 * 2 ^ 59
def prefixEnd_1848343 : Nat := 4983230072969 + 3 ^ 40 * 1848343 * 2
def baseEnd_1848343 : Nat := 421817054832607592538725

theorem tailTrace_1848343 : CollatzResearch.WordTrace tailWord_1848343 prefixEnd_1848343 421817054832607592538725 := by
  unfold tailWord_1848343
  simp only [CollatzResearch.WordTrace]
  refine ⟨67414607542776457697589683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44943071695184305131726455 67414607542776457697589683)
  ·
    refine ⟨101121911314164686546384525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67414607542776457697589683 101121911314164686546384525)
    ·
      refine ⟨37920716742811757454894197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 101121911314164686546384525 37920716742811757454894197)
      ·
        refine ⟨3555067194638602261396331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 37920716742811757454894197 3555067194638602261396331)
        ·
          refine ⟨5332600791957903392094497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3555067194638602261396331 5332600791957903392094497)
          ·
            refine ⟨3999450593968427544070873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5332600791957903392094497 3999450593968427544070873)
            ·
              refine ⟨2999587945476320658053155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3999450593968427544070873 2999587945476320658053155)
              ·
                refine ⟨4499381918214480987079733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2999587945476320658053155 4499381918214480987079733)
                ·
                  refine ⟨421817054832607592538725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4499381918214480987079733 421817054832607592538725)
                  ·
                    rfl

theorem cell21_1848343_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 2, 2, 1, 5].length) (baseStart_1848343 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1848343 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1848343 prefixEnd_1848343 := by exact prefixLift 1848343
  have htrace : WordTrace (prefixWord ++ tailWord_1848343) baseStart_1848343 baseEnd_1848343 := by
    simpa [prefixWord, tailWord_1848343, baseEnd_1848343] using wordTrace_append hprefix tailTrace_1848343
  have hstable : (prefixWord ++ tailWord_1848343).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1848343).length < 2 ^ (prefixWord ++ tailWord_1848343).sum := by decide
  have hdescent : baseEnd_1848343 < baseStart_1848343 := by decide
  rcases family_descends (prefixWord ++ tailWord_1848343) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1848453 : List Nat := [1, 3, 1, 1, 6, 2, 2, 2, 3]
def baseStart_1848453 : Nat := 118140960795 + 1848453 * 2 ^ 59
def prefixEnd_1848453 : Nat := 4983230072969 + 3 ^ 40 * 1848453 * 2
def baseEnd_1848453 : Nat := 421842158331271845705167

theorem tailTrace_1848453 : CollatzResearch.WordTrace tailWord_1848453 prefixEnd_1848453 421842158331271845705167 := by
  unfold tailWord_1848453
  simp only [CollatzResearch.WordTrace]
  refine ⟨67418619572377946484094013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44945746381585297656062675 67418619572377946484094013)
  ·
    refine ⟨25281982339641729931535255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 67418619572377946484094013 25281982339641729931535255)
    ·
      refine ⟨37922973509462594897302883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25281982339641729931535255 37922973509462594897302883)
      ·
        refine ⟨56884460264193892345954325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37922973509462594897302883 56884460264193892345954325)
        ·
          refine ⟨2666459074884088703716609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 56884460264193892345954325 2666459074884088703716609)
          ·
            refine ⟨1999844306163066527787457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2666459074884088703716609 1999844306163066527787457)
            ·
              refine ⟨1499883229622299895840593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1999844306163066527787457 1499883229622299895840593)
              ·
                refine ⟨1124912422216724921880445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1499883229622299895840593 1124912422216724921880445)
                ·
                  refine ⟨421842158331271845705167, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1124912422216724921880445 421842158331271845705167)
                  ·
                    rfl

theorem cell21_1848453_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 6, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 6, 2, 2, 2, 3].length) (baseStart_1848453 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1848453 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1848453 prefixEnd_1848453 := by exact prefixLift 1848453
  have htrace : WordTrace (prefixWord ++ tailWord_1848453) baseStart_1848453 baseEnd_1848453 := by
    simpa [prefixWord, tailWord_1848453, baseEnd_1848453] using wordTrace_append hprefix tailTrace_1848453
  have hstable : (prefixWord ++ tailWord_1848453).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1848453).length < 2 ^ (prefixWord ++ tailWord_1848453).sum := by decide
  have hdescent : baseEnd_1848453 < baseStart_1848453 := by decide
  rcases family_descends (prefixWord ++ tailWord_1848453) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1848509 : List Nat := [1, 4, 1, 2, 1, 1, 5, 2, 4]
def baseStart_1848509 : Nat := 118140960795 + 1848509 * 2 ^ 59
def prefixEnd_1848509 : Nat := 4983230072969 + 3 ^ 40 * 1848509 * 2
def baseEnd_1848509 : Nat := 421854938294228192771719

theorem tailTrace_1848509 : CollatzResearch.WordTrace tailWord_1848509 prefixEnd_1848509 421854938294228192771719 := by
  unfold tailWord_1848509
  simp only [CollatzResearch.WordTrace]
  refine ⟨67420662060175068048132581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44947108040116712032088387 67420662060175068048132581)
  ·
    refine ⟨12641374136282825259024859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 67420662060175068048132581 12641374136282825259024859)
    ·
      refine ⟨18962061204424237888537289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12641374136282825259024859 18962061204424237888537289)
      ·
        refine ⟨14221545903318178416402967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18962061204424237888537289 14221545903318178416402967)
        ·
          refine ⟨21332318854977267624604451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14221545903318178416402967 21332318854977267624604451)
          ·
            refine ⟨31998478282465901436906677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21332318854977267624604451 31998478282465901436906677)
            ·
              refine ⟨2999857338981178259710001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 31998478282465901436906677 2999857338981178259710001)
              ·
                refine ⟨2249893004235883694782501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2999857338981178259710001 2249893004235883694782501)
                ·
                  refine ⟨421854938294228192771719, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2249893004235883694782501 421854938294228192771719)
                  ·
                    rfl

theorem cell21_1848509_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 5, 2, 4].length) (baseStart_1848509 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1848509 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1848509 prefixEnd_1848509 := by exact prefixLift 1848509
  have htrace : WordTrace (prefixWord ++ tailWord_1848509) baseStart_1848509 baseEnd_1848509 := by
    simpa [prefixWord, tailWord_1848509, baseEnd_1848509] using wordTrace_append hprefix tailTrace_1848509
  have hstable : (prefixWord ++ tailWord_1848509).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1848509).length < 2 ^ (prefixWord ++ tailWord_1848509).sum := by decide
  have hdescent : baseEnd_1848509 < baseStart_1848509 := by decide
  rcases family_descends (prefixWord ++ tailWord_1848509) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1848633 : List Nat := [1, 2, 1, 6, 3, 1, 1, 6]
def baseStart_1848633 : Nat := 118140960795 + 1848633 * 2 ^ 59
def prefixEnd_1848633 : Nat := 4983230072969 + 3 ^ 40 * 1848633 * 2
def baseEnd_1848633 : Nat := 140627745594543844234933

theorem tailTrace_1848633 : CollatzResearch.WordTrace tailWord_1848633 prefixEnd_1848633 140627745594543844234933 := by
  unfold tailWord_1848633
  simp only [CollatzResearch.WordTrace]
  refine ⟨67425184711725837225646553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44950123141150558150431035 67425184711725837225646553)
  ·
    refine ⟨50568888533794377919234915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67425184711725837225646553 50568888533794377919234915)
    ·
      refine ⟨75853332800691566878852373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50568888533794377919234915 75853332800691566878852373)
      ·
        refine ⟨3555624975032417197446205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 75853332800691566878852373 3555624975032417197446205)
        ·
          refine ⟨1333359365637156449042327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3555624975032417197446205 1333359365637156449042327)
          ·
            refine ⟨2000039048455734673563491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1333359365637156449042327 2000039048455734673563491)
            ·
              refine ⟨3000058572683602010345237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2000039048455734673563491 3000058572683602010345237)
              ·
                refine ⟨140627745594543844234933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3000058572683602010345237 140627745594543844234933)
                ·
                  rfl

theorem cell21_1848633_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 3, 1, 1, 6].length) (baseStart_1848633 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1848633 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1848633 prefixEnd_1848633 := by exact prefixLift 1848633
  have htrace : WordTrace (prefixWord ++ tailWord_1848633) baseStart_1848633 baseEnd_1848633 := by
    simpa [prefixWord, tailWord_1848633, baseEnd_1848633] using wordTrace_append hprefix tailTrace_1848633
  have hstable : (prefixWord ++ tailWord_1848633).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1848633).length < 2 ^ (prefixWord ++ tailWord_1848633).sum := by decide
  have hdescent : baseEnd_1848633 < baseStart_1848633 := by decide
  rcases family_descends (prefixWord ++ tailWord_1848633) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1848689 : List Nat := [1, 2, 2, 2, 1, 2, 3, 3, 5]
def baseStart_1848689 : Nat := 118140960795 + 1848689 * 2 ^ 59
def prefixEnd_1848689 : Nat := 4983230072969 + 3 ^ 40 * 1848689 * 2
def baseEnd_1848689 : Nat := 421896016746587879771351

theorem tailTrace_1848689 : CollatzResearch.WordTrace tailWord_1848689 prefixEnd_1848689 421896016746587879771351 := by
  unfold tailWord_1848689
  simp only [CollatzResearch.WordTrace]
  refine ⟨67427227199522958789685121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44951484799681972526456747 67427227199522958789685121)
  ·
    refine ⟨50570420399642219092263841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67427227199522958789685121 50570420399642219092263841)
    ·
      refine ⟨37927815299731664319197881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50570420399642219092263841 37927815299731664319197881)
      ·
        refine ⟨28445861474798748239398411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37927815299731664319197881 28445861474798748239398411)
        ·
          refine ⟨42668792212198122359097617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28445861474798748239398411 42668792212198122359097617)
          ·
            refine ⟨32001594159148591769323213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42668792212198122359097617 32001594159148591769323213)
            ·
              refine ⟨12000597809680721913496205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32001594159148591769323213 12000597809680721913496205)
              ·
                refine ⟨4500224178630270717561077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12000597809680721913496205 4500224178630270717561077)
                ·
                  refine ⟨421896016746587879771351, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4500224178630270717561077 421896016746587879771351)
                  ·
                    rfl

theorem cell21_1848689_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 3, 3, 5].length) (baseStart_1848689 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1848689 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1848689 prefixEnd_1848689 := by exact prefixLift 1848689
  have htrace : WordTrace (prefixWord ++ tailWord_1848689) baseStart_1848689 baseEnd_1848689 := by
    simpa [prefixWord, tailWord_1848689, baseEnd_1848689] using wordTrace_append hprefix tailTrace_1848689
  have hstable : (prefixWord ++ tailWord_1848689).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1848689).length < 2 ^ (prefixWord ++ tailWord_1848689).sum := by decide
  have hdescent : baseEnd_1848689 < baseStart_1848689 := by decide
  rcases family_descends (prefixWord ++ tailWord_1848689) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1848703 : List Nat := [1, 1, 2, 2, 1, 1, 2, 1, 10]
def baseStart_1848703 : Nat := 118140960795 + 1848703 * 2 ^ 59
def prefixEnd_1848703 : Nat := 4983230072969 + 3 ^ 40 * 1848703 * 2
def baseEnd_1848703 : Nat := 421899211737326966537989

theorem tailTrace_1848703 : CollatzResearch.WordTrace tailWord_1848703 prefixEnd_1848703 421899211737326966537989 := by
  unfold tailWord_1848703
  simp only [CollatzResearch.WordTrace]
  refine ⟨67427737821472239180694763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44951825214314826120463175 67427737821472239180694763)
  ·
    refine ⟨101141606732208358771042145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67427737821472239180694763 101141606732208358771042145)
    ·
      refine ⟨75856205049156269078281609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 101141606732208358771042145 75856205049156269078281609)
      ·
        refine ⟨56892153786867201808711207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 75856205049156269078281609 56892153786867201808711207)
        ·
          refine ⟨85338230680300802713066811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56892153786867201808711207 85338230680300802713066811)
          ·
            refine ⟨128007346020451204069600217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 85338230680300802713066811 128007346020451204069600217)
            ·
              refine ⟨96005509515338403052200163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 128007346020451204069600217 96005509515338403052200163)
              ·
                refine ⟨144008264273007604578300245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 96005509515338403052200163 144008264273007604578300245)
                ·
                  refine ⟨421899211737326966537989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 144008264273007604578300245 421899211737326966537989)
                  ·
                    rfl

theorem cell21_1848703_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 2, 1, 10].length) (baseStart_1848703 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1848703 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1848703 prefixEnd_1848703 := by exact prefixLift 1848703
  have htrace : WordTrace (prefixWord ++ tailWord_1848703) baseStart_1848703 baseEnd_1848703 := by
    simpa [prefixWord, tailWord_1848703, baseEnd_1848703] using wordTrace_append hprefix tailTrace_1848703
  have hstable : (prefixWord ++ tailWord_1848703).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1848703).length < 2 ^ (prefixWord ++ tailWord_1848703).sum := by decide
  have hdescent : baseEnd_1848703 < baseStart_1848703 := by decide
  rcases family_descends (prefixWord ++ tailWord_1848703) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1848765 : List Nat := [1, 4, 1, 2, 2, 1, 2, 1, 7]
def baseStart_1848765 : Nat := 118140960795 + 1848765 * 2 ^ 59
def prefixEnd_1848765 : Nat := 4983230072969 + 3 ^ 40 * 1848765 * 2
def baseEnd_1848765 : Nat := 421913360982028636504529

theorem tailTrace_1848765 : CollatzResearch.WordTrace tailWord_1848765 prefixEnd_1848765 421913360982028636504529 := by
  unfold tailWord_1848765
  simp only [CollatzResearch.WordTrace]
  refine ⟨67429999147247623769451749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44953332764831749179634499 67429999147247623769451749)
  ·
    refine ⟨12643124840108929456772203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 67429999147247623769451749 12643124840108929456772203)
    ·
      refine ⟨18964687260163394185158305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12643124840108929456772203 18964687260163394185158305)
      ·
        refine ⟨14223515445122545638868729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18964687260163394185158305 14223515445122545638868729)
        ·
          refine ⟨10667636583841909229151547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14223515445122545638868729 10667636583841909229151547)
          ·
            refine ⟨16001454875762863843727321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10667636583841909229151547 16001454875762863843727321)
            ·
              refine ⟨12001091156822147882795491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16001454875762863843727321 12001091156822147882795491)
              ·
                refine ⟨18001636735233221824193237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12001091156822147882795491 18001636735233221824193237)
                ·
                  refine ⟨421913360982028636504529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 18001636735233221824193237 421913360982028636504529)
                  ·
                    rfl

theorem cell21_1848765_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 2, 1, 7].length) (baseStart_1848765 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1848765 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1848765 prefixEnd_1848765 := by exact prefixLift 1848765
  have htrace : WordTrace (prefixWord ++ tailWord_1848765) baseStart_1848765 baseEnd_1848765 := by
    simpa [prefixWord, tailWord_1848765, baseEnd_1848765] using wordTrace_append hprefix tailTrace_1848765
  have hstable : (prefixWord ++ tailWord_1848765).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1848765).length < 2 ^ (prefixWord ++ tailWord_1848765).sum := by decide
  have hdescent : baseEnd_1848765 < baseStart_1848765 := by decide
  rcases family_descends (prefixWord ++ tailWord_1848765) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1848779 : List Nat := [1, 1, 1, 1, 3, 3, 2, 1, 8]
def baseStart_1848779 : Nat := 118140960795 + 1848779 * 2 ^ 59
def prefixEnd_1848779 : Nat := 4983230072969 + 3 ^ 40 * 1848779 * 2
def baseEnd_1848779 : Nat := 421916555972767723271167

theorem tailTrace_1848779 : CollatzResearch.WordTrace tailWord_1848779 prefixEnd_1848779 421916555972767723271167 := by
  unfold tailWord_1848779
  simp only [CollatzResearch.WordTrace]
  refine ⟨67430509769196904160461391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44953673179464602773640927 67430509769196904160461391)
  ·
    refine ⟨101145764653795356240692087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67430509769196904160461391 101145764653795356240692087)
    ·
      refine ⟨151718646980693034361038131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101145764653795356240692087 151718646980693034361038131)
      ·
        refine ⟨227577970471039551541557197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 151718646980693034361038131 227577970471039551541557197)
        ·
          refine ⟨85341738926639831828083949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 227577970471039551541557197 85341738926639831828083949)
          ·
            refine ⟨32003152097489936935531481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 85341738926639831828083949 32003152097489936935531481)
            ·
              refine ⟨24002364073117452701648611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32003152097489936935531481 24002364073117452701648611)
              ·
                refine ⟨36003546109676179052472917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24002364073117452701648611 36003546109676179052472917)
                ·
                  refine ⟨421916555972767723271167, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 36003546109676179052472917 421916555972767723271167)
                  ·
                    rfl

theorem cell21_1848779_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 2, 1, 8].length) (baseStart_1848779 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1848779 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1848779 prefixEnd_1848779 := by exact prefixLift 1848779
  have htrace : WordTrace (prefixWord ++ tailWord_1848779) baseStart_1848779 baseEnd_1848779 := by
    simpa [prefixWord, tailWord_1848779, baseEnd_1848779] using wordTrace_append hprefix tailTrace_1848779
  have hstable : (prefixWord ++ tailWord_1848779).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1848779).length < 2 ^ (prefixWord ++ tailWord_1848779).sum := by decide
  have hdescent : baseEnd_1848779 < baseStart_1848779 := by decide
  rcases family_descends (prefixWord ++ tailWord_1848779) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1848892 : List Nat := [2, 2, 2, 2, 4, 2, 1, 3, 3]
def baseStart_1848892 : Nat := 118140960795 + 1848892 * 2 ^ 59
def prefixEnd_1848892 : Nat := 4983230072969 + 3 ^ 40 * 1848892 * 2
def baseEnd_1848892 : Nat := 421942344112304637887603

theorem tailTrace_1848892 : CollatzResearch.WordTrace tailWord_1848892 prefixEnd_1848892 421942344112304637887603 := by
  unfold tailWord_1848892
  simp only [CollatzResearch.WordTrace]
  refine ⟨33717315608893762229662465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44956420811858349639549953 33717315608893762229662465)
  ·
    refine ⟨25287986706670321672246849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33717315608893762229662465 25287986706670321672246849)
    ·
      refine ⟨18965990030002741254185137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25287986706670321672246849 18965990030002741254185137)
      ·
        refine ⟨14224492522502055940638853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18965990030002741254185137 14224492522502055940638853)
        ·
          refine ⟨2667092347969135488869785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 14224492522502055940638853 2667092347969135488869785)
          ·
            refine ⟨2000319260976851616652339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2667092347969135488869785 2000319260976851616652339)
            ·
              refine ⟨3000478891465277424978509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2000319260976851616652339 3000478891465277424978509)
              ·
                refine ⟨1125179584299479034366941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3000478891465277424978509 1125179584299479034366941)
                ·
                  refine ⟨421942344112304637887603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1125179584299479034366941 421942344112304637887603)
                  ·
                    rfl

theorem cell21_1848892_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 4, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 4, 2, 1, 3, 3].length) (baseStart_1848892 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1848892 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1848892 prefixEnd_1848892 := by exact prefixLift 1848892
  have htrace : WordTrace (prefixWord ++ tailWord_1848892) baseStart_1848892 baseEnd_1848892 := by
    simpa [prefixWord, tailWord_1848892, baseEnd_1848892] using wordTrace_append hprefix tailTrace_1848892
  have hstable : (prefixWord ++ tailWord_1848892).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1848892).length < 2 ^ (prefixWord ++ tailWord_1848892).sum := by decide
  have hdescent : baseEnd_1848892 < baseStart_1848892 := by decide
  rcases family_descends (prefixWord ++ tailWord_1848892) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1848903 : List Nat := [1, 1, 4, 1, 5, 2, 7]
def baseStart_1848903 : Nat := 118140960795 + 1848903 * 2 ^ 59
def prefixEnd_1848903 : Nat := 4983230072969 + 3 ^ 40 * 1848903 * 2
def baseEnd_1848903 : Nat := 46882761606907895911583

theorem tailTrace_1848903 : CollatzResearch.WordTrace tailWord_1848903 prefixEnd_1848903 46882761606907895911583 := by
  unfold tailWord_1848903
  simp only [CollatzResearch.WordTrace]
  refine ⟨67435032420747673337975363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44956688280498448891983575 67435032420747673337975363)
  ·
    refine ⟨101152548631121510006963045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67435032420747673337975363 101152548631121510006963045)
    ·
      refine ⟨18966102868335283126305571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 101152548631121510006963045 18966102868335283126305571)
      ·
        refine ⟨28449154302502924689458357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18966102868335283126305571 28449154302502924689458357)
        ·
          refine ⟨2667108215859649189636721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 28449154302502924689458357 2667108215859649189636721)
          ·
            refine ⟨2000331161894736892227541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2667108215859649189636721 2000331161894736892227541)
            ·
              refine ⟨46882761606907895911583, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 2000331161894736892227541 46882761606907895911583)
              ·
                rfl

theorem cell21_1848903_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 5, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 5, 2, 7].length) (baseStart_1848903 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1848903 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1848903 prefixEnd_1848903 := by exact prefixLift 1848903
  have htrace : WordTrace (prefixWord ++ tailWord_1848903) baseStart_1848903 baseEnd_1848903 := by
    simpa [prefixWord, tailWord_1848903, baseEnd_1848903] using wordTrace_append hprefix tailTrace_1848903
  have hstable : (prefixWord ++ tailWord_1848903).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1848903).length < 2 ^ (prefixWord ++ tailWord_1848903).sum := by decide
  have hdescent : baseEnd_1848903 < baseStart_1848903 := by decide
  rcases family_descends (prefixWord ++ tailWord_1848903) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1848909 : List Nat := [1, 6, 1, 1, 3, 1, 3, 2, 3]
def baseStart_1848909 : Nat := 118140960795 + 1848909 * 2 ^ 59
def prefixEnd_1848909 : Nat := 4983230072969 + 3 ^ 40 * 1848909 * 2
def baseEnd_1848909 : Nat := 421946223743916386104235

theorem tailTrace_1848909 : CollatzResearch.WordTrace tailWord_1848909 prefixEnd_1848909 421946223743916386104235 := by
  unfold tailWord_1848909
  simp only [CollatzResearch.WordTrace]
  refine ⟨67435251258725936362693781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44956834172483957575129187 67435251258725936362693781)
  ·
    refine ⟨3161027402752778267001271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 67435251258725936362693781 3161027402752778267001271)
    ·
      refine ⟨4741541104129167400501907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3161027402752778267001271 4741541104129167400501907)
      ·
        refine ⟨7112311656193751100752861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4741541104129167400501907 7112311656193751100752861)
        ·
          refine ⟨2667116871072656662782323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7112311656193751100752861 2667116871072656662782323)
          ·
            refine ⟨4000675306608984994173485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2667116871072656662782323 4000675306608984994173485)
            ·
              refine ⟨1500253239978369372815057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4000675306608984994173485 1500253239978369372815057)
              ·
                refine ⟨1125189929983777029611293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1500253239978369372815057 1125189929983777029611293)
                ·
                  refine ⟨421946223743916386104235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1125189929983777029611293 421946223743916386104235)
                  ·
                    rfl

theorem cell21_1848909_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 3, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 3, 1, 3, 2, 3].length) (baseStart_1848909 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1848909 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1848909 prefixEnd_1848909 := by exact prefixLift 1848909
  have htrace : WordTrace (prefixWord ++ tailWord_1848909) baseStart_1848909 baseEnd_1848909 := by
    simpa [prefixWord, tailWord_1848909, baseEnd_1848909] using wordTrace_append hprefix tailTrace_1848909
  have hstable : (prefixWord ++ tailWord_1848909).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1848909).length < 2 ^ (prefixWord ++ tailWord_1848909).sum := by decide
  have hdescent : baseEnd_1848909 < baseStart_1848909 := by decide
  rcases family_descends (prefixWord ++ tailWord_1848909) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1848968 : List Nat := [2, 1, 3, 5, 1, 1, 1, 4, 3]
def baseStart_1848968 : Nat := 118140960795 + 1848968 * 2 ^ 59
def prefixEnd_1848968 : Nat := 4983230072969 + 3 ^ 40 * 1848968 * 2
def baseEnd_1848968 : Nat := 421959688347745394620781

theorem tailTrace_1848968 : CollatzResearch.WordTrace tailWord_1848968 prefixEnd_1848968 421959688347745394620781 := by
  unfold tailWord_1848968
  simp only [CollatzResearch.WordTrace]
  refine ⟨33718701582756094719545779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44958268777008126292727705 33718701582756094719545779)
  ·
    refine ⟨50578052374134142079318669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33718701582756094719545779 50578052374134142079318669)
    ·
      refine ⟨18966769640300303279744501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 50578052374134142079318669 18966769640300303279744501)
      ·
        refine ⟨1778134653778153432476047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 18966769640300303279744501 1778134653778153432476047)
        ·
          refine ⟨2667201980667230148714071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1778134653778153432476047 2667201980667230148714071)
          ·
            refine ⟨4000802971000845223071107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2667201980667230148714071 4000802971000845223071107)
            ·
              refine ⟨6001204456501267834606661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4000802971000845223071107 6001204456501267834606661)
              ·
                refine ⟨1125225835593987718988749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6001204456501267834606661 1125225835593987718988749)
                ·
                  refine ⟨421959688347745394620781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1125225835593987718988749 421959688347745394620781)
                  ·
                    rfl

theorem cell21_1848968_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 5, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 5, 1, 1, 1, 4, 3].length) (baseStart_1848968 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1848968 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1848968 prefixEnd_1848968 := by exact prefixLift 1848968
  have htrace : WordTrace (prefixWord ++ tailWord_1848968) baseStart_1848968 baseEnd_1848968 := by
    simpa [prefixWord, tailWord_1848968, baseEnd_1848968] using wordTrace_append hprefix tailTrace_1848968
  have hstable : (prefixWord ++ tailWord_1848968).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1848968).length < 2 ^ (prefixWord ++ tailWord_1848968).sum := by decide
  have hdescent : baseEnd_1848968 < baseStart_1848968 := by decide
  rcases family_descends (prefixWord ++ tailWord_1848968) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1848976 : List Nat := [2, 1, 1, 1, 1, 1, 3, 2, 9]
def baseStart_1848976 : Nat := 118140960795 + 1848976 * 2 ^ 59
def prefixEnd_1848976 : Nat := 4983230072969 + 3 ^ 40 * 1848976 * 2
def baseEnd_1848976 : Nat := 421961514056739158487431

theorem tailTrace_1848976 : CollatzResearch.WordTrace tailWord_1848976 prefixEnd_1848976 421961514056739158487431 := by
  unfold tailWord_1848976
  simp only [CollatzResearch.WordTrace]
  refine ⟨33718847474741603402691391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44958463299655471203588521 33718847474741603402691391)
  ·
    refine ⟨50578271212112405104037087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33718847474741603402691391 50578271212112405104037087)
    ·
      refine ⟨75867406818168607656055631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50578271212112405104037087 75867406818168607656055631)
      ·
        refine ⟨113801110227252911484083447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75867406818168607656055631 113801110227252911484083447)
        ·
          refine ⟨170701665340879367226125171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 113801110227252911484083447 170701665340879367226125171)
          ·
            refine ⟨256052498011319050839187757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 170701665340879367226125171 256052498011319050839187757)
            ·
              refine ⟨96019686754244644064695409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 256052498011319050839187757 96019686754244644064695409)
              ·
                refine ⟨72014765065683483048521557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 96019686754244644064695409 72014765065683483048521557)
                ·
                  refine ⟨421961514056739158487431, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 72014765065683483048521557 421961514056739158487431)
                  ·
                    rfl

theorem cell21_1848976_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 3, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 3, 2, 9].length) (baseStart_1848976 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1848976 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1848976 prefixEnd_1848976 := by exact prefixLift 1848976
  have htrace : WordTrace (prefixWord ++ tailWord_1848976) baseStart_1848976 baseEnd_1848976 := by
    simpa [prefixWord, tailWord_1848976, baseEnd_1848976] using wordTrace_append hprefix tailTrace_1848976
  have hstable : (prefixWord ++ tailWord_1848976).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1848976).length < 2 ^ (prefixWord ++ tailWord_1848976).sum := by decide
  have hdescent : baseEnd_1848976 < baseStart_1848976 := by decide
  rcases family_descends (prefixWord ++ tailWord_1848976) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1848993 : List Nat := [1, 2, 3, 3, 2, 1, 1, 1, 7]
def baseStart_1848993 : Nat := 118140960795 + 1848993 * 2 ^ 59
def prefixEnd_1848993 : Nat := 4983230072969 + 3 ^ 40 * 1848993 * 2
def baseEnd_1848993 : Nat := 421965393688350906704063

theorem tailTrace_1848993 : CollatzResearch.WordTrace tailWord_1848993 prefixEnd_1848993 421965393688350906704063 := by
  unfold tailWord_1848993
  simp only [CollatzResearch.WordTrace]
  refine ⟨67438314990421618708751633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44958876660281079139167755 67438314990421618708751633)
  ·
    refine ⟨50578736242816214031563725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67438314990421618708751633 50578736242816214031563725)
    ·
      refine ⟨18967026091056080261836397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 50578736242816214031563725 18967026091056080261836397)
      ·
        refine ⟨7112634784146030098188649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18967026091056080261836397 7112634784146030098188649)
        ·
          refine ⟨5334476088109522573641487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7112634784146030098188649 5334476088109522573641487)
          ·
            refine ⟨8001714132164283860462231, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5334476088109522573641487 8001714132164283860462231)
            ·
              refine ⟨12002571198246425790693347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8001714132164283860462231 12002571198246425790693347)
              ·
                refine ⟨18003856797369638686040021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12002571198246425790693347 18003856797369638686040021)
                ·
                  refine ⟨421965393688350906704063, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 18003856797369638686040021 421965393688350906704063)
                  ·
                    rfl

theorem cell21_1848993_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 1, 1, 1, 7].length) (baseStart_1848993 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1848993 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1848993 prefixEnd_1848993 := by exact prefixLift 1848993
  have htrace : WordTrace (prefixWord ++ tailWord_1848993) baseStart_1848993 baseEnd_1848993 := by
    simpa [prefixWord, tailWord_1848993, baseEnd_1848993] using wordTrace_append hprefix tailTrace_1848993
  have hstable : (prefixWord ++ tailWord_1848993).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1848993).length < 2 ^ (prefixWord ++ tailWord_1848993).sum := by decide
  have hdescent : baseEnd_1848993 < baseStart_1848993 := by decide
  rcases family_descends (prefixWord ++ tailWord_1848993) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1849007 : List Nat := [1, 1, 2, 1, 2, 4, 2, 2, 6]
def baseStart_1849007 : Nat := 118140960795 + 1849007 * 2 ^ 59
def prefixEnd_1849007 : Nat := 4983230072969 + 3 ^ 40 * 1849007 * 2
def baseEnd_1849007 : Nat := 421968588679089993470701

theorem tailTrace_1849007 : CollatzResearch.WordTrace tailWord_1849007 prefixEnd_1849007 421968588679089993470701 := by
  unfold tailWord_1849007
  simp only [CollatzResearch.WordTrace]
  refine ⟨67438825612370899099761275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44959217074913932733174183 67438825612370899099761275)
  ·
    refine ⟨101158238418556348649641913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67438825612370899099761275 101158238418556348649641913)
    ·
      refine ⟨75868678813917261487231435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 101158238418556348649641913 75868678813917261487231435)
      ·
        refine ⟨113803018220875892230847153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75868678813917261487231435 113803018220875892230847153)
        ·
          refine ⟨85352263665656919173135365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 113803018220875892230847153 85352263665656919173135365)
          ·
            refine ⟨16003549437310672344962881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 85352263665656919173135365 16003549437310672344962881)
            ·
              refine ⟨12002662077983004258722161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16003549437310672344962881 12002662077983004258722161)
              ·
                refine ⟨9001996558487253194041621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12002662077983004258722161 9001996558487253194041621)
                ·
                  refine ⟨421968588679089993470701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9001996558487253194041621 421968588679089993470701)
                  ·
                    rfl

theorem cell21_1849007_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 2, 2, 6].length) (baseStart_1849007 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1849007 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1849007 prefixEnd_1849007 := by exact prefixLift 1849007
  have htrace : WordTrace (prefixWord ++ tailWord_1849007) baseStart_1849007 baseEnd_1849007 := by
    simpa [prefixWord, tailWord_1849007, baseEnd_1849007] using wordTrace_append hprefix tailTrace_1849007
  have hstable : (prefixWord ++ tailWord_1849007).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1849007).length < 2 ^ (prefixWord ++ tailWord_1849007).sum := by decide
  have hdescent : baseEnd_1849007 < baseStart_1849007 := by decide
  rcases family_descends (prefixWord ++ tailWord_1849007) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1849010 : List Nat := [3, 2, 1, 1, 1, 2, 3, 5, 3]
def baseStart_1849010 : Nat := 118140960795 + 1849010 * 2 ^ 59
def prefixEnd_1849010 : Nat := 4983230072969 + 3 ^ 40 * 1849010 * 2
def baseEnd_1849010 : Nat := 421969273319962654920695

theorem tailTrace_1849010 : CollatzResearch.WordTrace tailWord_1849010 prefixEnd_1849010 421969273319962654920695 := by
  unfold tailWord_1849010
  simp only [CollatzResearch.WordTrace]
  refine ⟨16859733757840007653030121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 44959290020906687074746989 16859733757840007653030121)
  ·
    refine ⟨12644800318380005739772591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16859733757840007653030121 12644800318380005739772591)
    ·
      refine ⟨18967200477570008609658887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12644800318380005739772591 18967200477570008609658887)
      ·
        refine ⟨28450800716355012914488331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18967200477570008609658887 28450800716355012914488331)
        ·
          refine ⟨42676201074532519371732497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28450800716355012914488331 42676201074532519371732497)
          ·
            refine ⟨32007150805899389528799373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42676201074532519371732497 32007150805899389528799373)
            ·
              refine ⟨12002681552212271073299765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32007150805899389528799373 12002681552212271073299765)
              ·
                refine ⟨1125251395519900413121853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 12002681552212271073299765 1125251395519900413121853)
                ·
                  refine ⟨421969273319962654920695, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1125251395519900413121853 421969273319962654920695)
                  ·
                    rfl

theorem cell21_1849010_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 3, 5, 3].length) (baseStart_1849010 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1849010 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1849010 prefixEnd_1849010 := by exact prefixLift 1849010
  have htrace : WordTrace (prefixWord ++ tailWord_1849010) baseStart_1849010 baseEnd_1849010 := by
    simpa [prefixWord, tailWord_1849010, baseEnd_1849010] using wordTrace_append hprefix tailTrace_1849010
  have hstable : (prefixWord ++ tailWord_1849010).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1849010).length < 2 ^ (prefixWord ++ tailWord_1849010).sum := by decide
  have hdescent : baseEnd_1849010 < baseStart_1849010 := by decide
  rcases family_descends (prefixWord ++ tailWord_1849010) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1849038 : List Nat := [4, 1, 1, 1, 3, 1, 2, 8]
def baseStart_1849038 : Nat := 118140960795 + 1849038 * 2 ^ 59
def prefixEnd_1849038 : Nat := 4983230072969 + 3 ^ 40 * 1849038 * 2
def baseEnd_1849038 : Nat := 140658554433813609484657

theorem tailTrace_1849038 : CollatzResearch.WordTrace tailWord_1849038 prefixEnd_1849038 140658554433813609484657 := by
  unfold tailWord_1849038
  simp only [CollatzResearch.WordTrace]
  refine ⟨8429994534407323924267471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 44959970850172394262759845 8429994534407323924267471)
  ·
    refine ⟨12644991801610985886401207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8429994534407323924267471 12644991801610985886401207)
    ·
      refine ⟨18967487702416478829601811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12644991801610985886401207 18967487702416478829601811)
      ·
        refine ⟨28451231553624718244402717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18967487702416478829601811 28451231553624718244402717)
        ·
          refine ⟨10669211832609269341651019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28451231553624718244402717 10669211832609269341651019)
          ·
            refine ⟨16003817748913904012476529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10669211832609269341651019 16003817748913904012476529)
            ·
              refine ⟨12002863311685428009357397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16003817748913904012476529 12002863311685428009357397)
              ·
                refine ⟨140658554433813609484657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 12002863311685428009357397 140658554433813609484657)
                ·
                  rfl

theorem cell21_1849038_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 2, 8].length) (baseStart_1849038 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1849038 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1849038 prefixEnd_1849038 := by exact prefixLift 1849038
  have htrace : WordTrace (prefixWord ++ tailWord_1849038) baseStart_1849038 baseEnd_1849038 := by
    simpa [prefixWord, tailWord_1849038, baseEnd_1849038] using wordTrace_append hprefix tailTrace_1849038
  have hstable : (prefixWord ++ tailWord_1849038).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1849038).length < 2 ^ (prefixWord ++ tailWord_1849038).sum := by decide
  have hdescent : baseEnd_1849038 < baseStart_1849038 := by decide
  rcases family_descends (prefixWord ++ tailWord_1849038) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1849041 : List Nat := [1, 2, 2, 1, 2, 5, 3, 1, 4]
def baseStart_1849041 : Nat := 118140960795 + 1849041 * 2 ^ 59
def prefixEnd_1849041 : Nat := 4983230072969 + 3 ^ 40 * 1849041 * 2
def baseEnd_1849041 : Nat := 421976347942313489903965

theorem tailTrace_1849041 : CollatzResearch.WordTrace tailWord_1849041 prefixEnd_1849041 421976347942313489903965 := by
  unfold tailWord_1849041
  simp only [CollatzResearch.WordTrace]
  refine ⟨67440065694247722906498977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44960043796165148604332651 67440065694247722906498977)
  ·
    refine ⟨50580049270685792179874233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67440065694247722906498977 50580049270685792179874233)
    ·
      refine ⟨37935036953014344134905675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50580049270685792179874233 37935036953014344134905675)
      ·
        refine ⟨56902555429521516202358513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37935036953014344134905675 56902555429521516202358513)
        ·
          refine ⟨42676916572141137151768885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56902555429521516202358513 42676916572141137151768885)
          ·
            refine ⟨4000960928638231607978333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 42676916572141137151768885 4000960928638231607978333)
            ·
              refine ⟨1500360348239336852991875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4000960928638231607978333 1500360348239336852991875)
              ·
                refine ⟨2250540522359005279487813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1500360348239336852991875 2250540522359005279487813)
                ·
                  refine ⟨421976347942313489903965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2250540522359005279487813 421976347942313489903965)
                  ·
                    rfl

theorem cell21_1849041_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 5, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 5, 3, 1, 4].length) (baseStart_1849041 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1849041 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1849041 prefixEnd_1849041 := by exact prefixLift 1849041
  have htrace : WordTrace (prefixWord ++ tailWord_1849041) baseStart_1849041 baseEnd_1849041 := by
    simpa [prefixWord, tailWord_1849041, baseEnd_1849041] using wordTrace_append hprefix tailTrace_1849041
  have hstable : (prefixWord ++ tailWord_1849041).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1849041).length < 2 ^ (prefixWord ++ tailWord_1849041).sum := by decide
  have hdescent : baseEnd_1849041 < baseStart_1849041 := by decide
  rcases family_descends (prefixWord ++ tailWord_1849041) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1849114 : List Nat := [3, 1, 1, 3, 2, 2, 2, 7]
def baseStart_1849114 : Nat := 118140960795 + 1849114 * 2 ^ 59
def prefixEnd_1849114 : Nat := 4983230072969 + 3 ^ 40 * 1849114 * 2
def baseEnd_1849114 : Nat := 140664335845627195062383

theorem tailTrace_1849114 : CollatzResearch.WordTrace tailWord_1849114 prefixEnd_1849114 140664335845627195062383 := by
  unfold tailWord_1849114
  simp only [CollatzResearch.WordTrace]
  refine ⟨16860682055745814093476599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 44961818815322170915937597 16860682055745814093476599)
  ·
    refine ⟨25291023083618721140214899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16860682055745814093476599 25291023083618721140214899)
    ·
      refine ⟨37936534625428081710322349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25291023083618721140214899 37936534625428081710322349)
      ·
        refine ⟨14226200484535530641370881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 37936534625428081710322349 14226200484535530641370881)
        ·
          refine ⟨10669650363401647981028161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14226200484535530641370881 10669650363401647981028161)
          ·
            refine ⟨8002237772551235985771121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10669650363401647981028161 8002237772551235985771121)
            ·
              refine ⟨6001678329413426989328341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8002237772551235985771121 6001678329413426989328341)
              ·
                refine ⟨140664335845627195062383, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6001678329413426989328341 140664335845627195062383)
                ·
                  rfl

theorem cell21_1849114_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 2, 2, 7].length) (baseStart_1849114 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1849114 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1849114 prefixEnd_1849114 := by exact prefixLift 1849114
  have htrace : WordTrace (prefixWord ++ tailWord_1849114) baseStart_1849114 baseEnd_1849114 := by
    simpa [prefixWord, tailWord_1849114, baseEnd_1849114] using wordTrace_append hprefix tailTrace_1849114
  have hstable : (prefixWord ++ tailWord_1849114).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1849114).length < 2 ^ (prefixWord ++ tailWord_1849114).sum := by decide
  have hdescent : baseEnd_1849114 < baseStart_1849114 := by decide
  rcases family_descends (prefixWord ++ tailWord_1849114) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1849134 : List Nat := [4, 1, 3, 2, 2, 1, 2, 2, 4]
def baseStart_1849134 : Nat := 118140960795 + 1849134 * 2 ^ 59
def prefixEnd_1849134 : Nat := 4983230072969 + 3 ^ 40 * 1849134 * 2
def baseEnd_1849134 : Nat := 421997571809365994853775

theorem tailTrace_1849134 : CollatzResearch.WordTrace tailWord_1849134 prefixEnd_1849134 421997571809365994853775 := by
  unfold tailWord_1849134
  simp only [CollatzResearch.WordTrace]
  refine ⟨8430432210363849973704307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 44962305121940533193089637 8430432210363849973704307)
  ·
    refine ⟨12645648315545774960556461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8430432210363849973704307 12645648315545774960556461)
    ·
      refine ⟨4742118118329665610208673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12645648315545774960556461 4742118118329665610208673)
      ·
        refine ⟨3556588588747249207656505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4742118118329665610208673 3556588588747249207656505)
        ·
          refine ⟨2667441441560436905742379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3556588588747249207656505 2667441441560436905742379)
          ·
            refine ⟨4001162162340655358613569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2667441441560436905742379 4001162162340655358613569)
            ·
              refine ⟨3000871621755491518960177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4001162162340655358613569 3000871621755491518960177)
              ·
                refine ⟨2250653716316618639220133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3000871621755491518960177 2250653716316618639220133)
                ·
                  refine ⟨421997571809365994853775, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2250653716316618639220133 421997571809365994853775)
                  ·
                    rfl

theorem cell21_1849134_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 2, 1, 2, 2, 4].length) (baseStart_1849134 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1849134 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1849134 prefixEnd_1849134 := by exact prefixLift 1849134
  have htrace : WordTrace (prefixWord ++ tailWord_1849134) baseStart_1849134 baseEnd_1849134 := by
    simpa [prefixWord, tailWord_1849134, baseEnd_1849134] using wordTrace_append hprefix tailTrace_1849134
  have hstable : (prefixWord ++ tailWord_1849134).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1849134).length < 2 ^ (prefixWord ++ tailWord_1849134).sum := by decide
  have hdescent : baseEnd_1849134 < baseStart_1849134 := by decide
  rcases family_descends (prefixWord ++ tailWord_1849134) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1849224 : List Nat := [2, 1, 3, 3, 3, 2, 2, 5]
def baseStart_1849224 : Nat := 118140960795 + 1849224 * 2 ^ 59
def prefixEnd_1849224 : Nat := 4983230072969 + 3 ^ 40 * 1849224 * 2
def baseEnd_1849224 : Nat := 140672703678515279451197

theorem tailTrace_1849224 : CollatzResearch.WordTrace tailWord_1849224 prefixEnd_1849224 140672703678515279451197 := by
  unfold tailWord_1849224
  simp only [CollatzResearch.WordTrace]
  refine ⟨33723370126292372580205363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44964493501723163440273817 33723370126292372580205363)
  ·
    refine ⟨50585055189438558870308045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33723370126292372580205363 50585055189438558870308045)
    ·
      refine ⟨18969395696039459576365517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 50585055189438558870308045 18969395696039459576365517)
      ·
        refine ⟨7113523386014797341137069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18969395696039459576365517 7113523386014797341137069)
        ·
          refine ⟨2667571269755549002926401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7113523386014797341137069 2667571269755549002926401)
          ·
            refine ⟨2000678452316661752194801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2667571269755549002926401 2000678452316661752194801)
            ·
              refine ⟨1500508839237496314146101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2000678452316661752194801 1500508839237496314146101)
              ·
                refine ⟨140672703678515279451197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1500508839237496314146101 140672703678515279451197)
                ·
                  rfl

theorem cell21_1849224_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 3, 2, 2, 5].length) (baseStart_1849224 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1849224 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1849224 prefixEnd_1849224 := by exact prefixLift 1849224
  have htrace : WordTrace (prefixWord ++ tailWord_1849224) baseStart_1849224 baseEnd_1849224 := by
    simpa [prefixWord, tailWord_1849224, baseEnd_1849224] using wordTrace_append hprefix tailTrace_1849224
  have hstable : (prefixWord ++ tailWord_1849224).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1849224).length < 2 ^ (prefixWord ++ tailWord_1849224).sum := by decide
  have hdescent : baseEnd_1849224 < baseStart_1849224 := by decide
  rcases family_descends (prefixWord ++ tailWord_1849224) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1849269 : List Nat := [1, 3, 3, 2, 1, 2, 4, 1, 4]
def baseStart_1849269 : Nat := 118140960795 + 1849269 * 2 ^ 59
def prefixEnd_1849269 : Nat := 4983230072969 + 3 ^ 40 * 1849269 * 2
def baseEnd_1849269 : Nat := 422028380648635760103499

theorem tailTrace_1849269 : CollatzResearch.WordTrace tailWord_1849269 prefixEnd_1849269 422028380648635760103499 := by
  unfold tailWord_1849269
  simp only [CollatzResearch.WordTrace]
  refine ⟨67448381537421717845798861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44965587691614478563865907 67448381537421717845798861)
  ·
    refine ⟨25293143076533144192174573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 67448381537421717845798861 25293143076533144192174573)
    ·
      refine ⟨9484928653699929072065465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25293143076533144192174573 9484928653699929072065465)
      ·
        refine ⟨7113696490274946804049099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9484928653699929072065465 7113696490274946804049099)
        ·
          refine ⟨10670544735412420206073649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7113696490274946804049099 10670544735412420206073649)
          ·
            refine ⟨8002908551559315154555237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10670544735412420206073649 8002908551559315154555237)
            ·
              refine ⟨1500545353417371591479107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8002908551559315154555237 1500545353417371591479107)
              ·
                refine ⟨2250818030126057387218661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1500545353417371591479107 2250818030126057387218661)
                ·
                  refine ⟨422028380648635760103499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2250818030126057387218661 422028380648635760103499)
                  ·
                    rfl

theorem cell21_1849269_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 2, 4, 1, 4].length) (baseStart_1849269 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1849269 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1849269 prefixEnd_1849269 := by exact prefixLift 1849269
  have htrace : WordTrace (prefixWord ++ tailWord_1849269) baseStart_1849269 baseEnd_1849269 := by
    simpa [prefixWord, tailWord_1849269, baseEnd_1849269] using wordTrace_append hprefix tailTrace_1849269
  have hstable : (prefixWord ++ tailWord_1849269).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1849269).length < 2 ^ (prefixWord ++ tailWord_1849269).sum := by decide
  have hdescent : baseEnd_1849269 < baseStart_1849269 := by decide
  rcases family_descends (prefixWord ++ tailWord_1849269) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1849280 : List Nat := [2, 1, 1, 2, 3, 2, 2, 1, 7]
def baseStart_1849280 : Nat := 118140960795 + 1849280 * 2 ^ 59
def prefixEnd_1849280 : Nat := 4983230072969 + 3 ^ 40 * 1849280 * 2
def baseEnd_1849280 : Nat := 422030890998502185420143

theorem tailTrace_1849280 : CollatzResearch.WordTrace tailWord_1849280 prefixEnd_1849280 422030890998502185420143 := by
  unfold tailWord_1849280
  simp only [CollatzResearch.WordTrace]
  refine ⟨33724391370190933362224647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44965855160254577816299529 33724391370190933362224647)
  ·
    refine ⟨50586587055286400043336971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33724391370190933362224647 50586587055286400043336971)
    ·
      refine ⟨75879880582929600065005457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50586587055286400043336971 75879880582929600065005457)
      ·
        refine ⟨56909910437197200048754093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 75879880582929600065005457 56909910437197200048754093)
        ·
          refine ⟨21341216413948950018282785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 56909910437197200048754093 21341216413948950018282785)
          ·
            refine ⟨16005912310461712513712089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21341216413948950018282785 16005912310461712513712089)
            ·
              refine ⟨12004434232846284385284067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16005912310461712513712089 12004434232846284385284067)
              ·
                refine ⟨18006651349269426577926101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12004434232846284385284067 18006651349269426577926101)
                ·
                  refine ⟨422030890998502185420143, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 18006651349269426577926101 422030890998502185420143)
                  ·
                    rfl

theorem cell21_1849280_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 2, 1, 7].length) (baseStart_1849280 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1849280 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1849280 prefixEnd_1849280 := by exact prefixLift 1849280
  have htrace : WordTrace (prefixWord ++ tailWord_1849280) baseStart_1849280 baseEnd_1849280 := by
    simpa [prefixWord, tailWord_1849280, baseEnd_1849280] using wordTrace_append hprefix tailTrace_1849280
  have hstable : (prefixWord ++ tailWord_1849280).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1849280).length < 2 ^ (prefixWord ++ tailWord_1849280).sum := by decide
  have hdescent : baseEnd_1849280 < baseStart_1849280 := by decide
  rcases family_descends (prefixWord ++ tailWord_1849280) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1849348 : List Nat := [2, 3, 2, 4, 1, 1, 2, 3, 3]
def baseStart_1849348 : Nat := 118140960795 + 1849348 * 2 ^ 59
def prefixEnd_1849348 : Nat := 4983230072969 + 3 ^ 40 * 1849348 * 2
def baseEnd_1849348 : Nat := 422046409524949178286671

theorem tailTrace_1849348 : CollatzResearch.WordTrace tailWord_1849348 prefixEnd_1849348 422046409524949178286671 := by
  unfold tailWord_1849348
  simp only [CollatzResearch.WordTrace]
  refine ⟨33725631452067757168962349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44967508602757009558616465 33725631452067757168962349)
  ·
    refine ⟨12647111794525408938360881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 33725631452067757168962349 12647111794525408938360881)
    ·
      refine ⟨9485333845894056703770661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12647111794525408938360881 9485333845894056703770661)
      ·
        refine ⟨1778500096105135631956999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 9485333845894056703770661 1778500096105135631956999)
        ·
          refine ⟨2667750144157703447935499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1778500096105135631956999 2667750144157703447935499)
          ·
            refine ⟨4001625216236555171903249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2667750144157703447935499 4001625216236555171903249)
            ·
              refine ⟨3001218912177416378927437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4001625216236555171903249 3001218912177416378927437)
              ·
                refine ⟨1125457092066531142097789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3001218912177416378927437 1125457092066531142097789)
                ·
                  refine ⟨422046409524949178286671, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1125457092066531142097789 422046409524949178286671)
                  ·
                    rfl

theorem cell21_1849348_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 1, 1, 2, 3, 3].length) (baseStart_1849348 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1849348 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1849348 prefixEnd_1849348 := by exact prefixLift 1849348
  have htrace : WordTrace (prefixWord ++ tailWord_1849348) baseStart_1849348 baseEnd_1849348 := by
    simpa [prefixWord, tailWord_1849348, baseEnd_1849348] using wordTrace_append hprefix tailTrace_1849348
  have hstable : (prefixWord ++ tailWord_1849348).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1849348).length < 2 ^ (prefixWord ++ tailWord_1849348).sum := by decide
  have hdescent : baseEnd_1849348 < baseStart_1849348 := by decide
  rcases family_descends (prefixWord ++ tailWord_1849348) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1849356 : List Nat := [2, 2, 1, 2, 3, 1, 1, 2, 7]
def baseStart_1849356 : Nat := 118140960795 + 1849356 * 2 ^ 59
def prefixEnd_1849356 : Nat := 4983230072969 + 3 ^ 40 * 1849356 * 2
def baseEnd_1849356 : Nat := 422048235233942942153321

theorem tailTrace_1849356 : CollatzResearch.WordTrace tailWord_1849356 prefixEnd_1849356 422048235233942942153321 := by
  unfold tailWord_1849356
  simp only [CollatzResearch.WordTrace]
  refine ⟨33725777344053265852107961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44967703125404354469477281 33725777344053265852107961)
  ·
    refine ⟨25294333008039949389080971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33725777344053265852107961 25294333008039949389080971)
    ·
      refine ⟨37941499512059924083621457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25294333008039949389080971 37941499512059924083621457)
      ·
        refine ⟨28456124634044943062716093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37941499512059924083621457 28456124634044943062716093)
        ·
          refine ⟨10671046737766853648518535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28456124634044943062716093 10671046737766853648518535)
          ·
            refine ⟨16006570106650280472777803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10671046737766853648518535 16006570106650280472777803)
            ·
              refine ⟨24009855159975420709166705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16006570106650280472777803 24009855159975420709166705)
              ·
                refine ⟨18007391369981565531875029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24009855159975420709166705 18007391369981565531875029)
                ·
                  refine ⟨422048235233942942153321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 18007391369981565531875029 422048235233942942153321)
                  ·
                    rfl

theorem cell21_1849356_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 1, 2, 7].length) (baseStart_1849356 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1849356 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1849356 prefixEnd_1849356 := by exact prefixLift 1849356
  have htrace : WordTrace (prefixWord ++ tailWord_1849356) baseStart_1849356 baseEnd_1849356 := by
    simpa [prefixWord, tailWord_1849356, baseEnd_1849356] using wordTrace_append hprefix tailTrace_1849356
  have hstable : (prefixWord ++ tailWord_1849356).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1849356).length < 2 ^ (prefixWord ++ tailWord_1849356).sum := by decide
  have hdescent : baseEnd_1849356 < baseStart_1849356 := by decide
  rcases family_descends (prefixWord ++ tailWord_1849356) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1849373 : List Nat := [1, 4, 2, 2, 2, 1, 1, 3, 5]
def baseStart_1849373 : Nat := 118140960795 + 1849373 * 2 ^ 59
def prefixEnd_1849373 : Nat := 4983230072969 + 3 ^ 40 * 1849373 * 2
def baseEnd_1849373 : Nat := 422052114865554690369953

theorem tailTrace_1849373 : CollatzResearch.WordTrace tailWord_1849373 prefixEnd_1849373 422052114865554690369953 := by
  unfold tailWord_1849373
  simp only [CollatzResearch.WordTrace]
  refine ⟨67452174729044943607584773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44968116486029962405056515 67452174729044943607584773)
  ·
    refine ⟨12647282761695926926422145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 67452174729044943607584773 12647282761695926926422145)
    ·
      refine ⟨9485462071271945194816609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12647282761695926926422145 9485462071271945194816609)
      ·
        refine ⟨7114096553453958896112457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9485462071271945194816609 7114096553453958896112457)
        ·
          refine ⟨5335572415090469172084343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7114096553453958896112457 5335572415090469172084343)
          ·
            refine ⟨8003358622635703758126515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5335572415090469172084343 8003358622635703758126515)
            ·
              refine ⟨12005037933953555637189773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8003358622635703758126515 12005037933953555637189773)
              ·
                refine ⟨4501889225232583363946165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12005037933953555637189773 4501889225232583363946165)
                ·
                  refine ⟨422052114865554690369953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4501889225232583363946165 422052114865554690369953)
                  ·
                    rfl

theorem cell21_1849373_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 1, 1, 3, 5].length) (baseStart_1849373 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1849373 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1849373 prefixEnd_1849373 := by exact prefixLift 1849373
  have htrace : WordTrace (prefixWord ++ tailWord_1849373) baseStart_1849373 baseEnd_1849373 := by
    simpa [prefixWord, tailWord_1849373, baseEnd_1849373] using wordTrace_append hprefix tailTrace_1849373
  have hstable : (prefixWord ++ tailWord_1849373).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1849373).length < 2 ^ (prefixWord ++ tailWord_1849373).sum := by decide
  have hdescent : baseEnd_1849373 < baseStart_1849373 := by decide
  rcases family_descends (prefixWord ++ tailWord_1849373) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1849477 : List Nat := [1, 3, 1, 1, 5, 10]
def baseStart_1849477 : Nat := 118140960795 + 1849477 * 2 ^ 59
def prefixEnd_1849477 : Nat := 4983230072969 + 3 ^ 40 * 1849477 * 2
def baseEnd_1849477 : Nat := 15632438854906430393941

theorem tailTrace_1849477 : CollatzResearch.WordTrace tailWord_1849477 prefixEnd_1849477 15632438854906430393941 := by
  unfold tailWord_1849477
  simp only [CollatzResearch.WordTrace]
  refine ⟨67455967920668169369370685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44970645280445446246247123 67455967920668169369370685)
  ·
    refine ⟨25295987970250563513514007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 67455967920668169369370685 25295987970250563513514007)
    ·
      refine ⟨37943981955375845270271011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25295987970250563513514007 37943981955375845270271011)
      ·
        refine ⟨56915972933063767905406517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37943981955375845270271011 56915972933063767905406517)
        ·
          refine ⟨5335872462474728241131861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 56915972933063767905406517 5335872462474728241131861)
          ·
            refine ⟨15632438854906430393941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 5335872462474728241131861 15632438854906430393941)
            ·
              rfl

theorem cell21_1849477_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 10].length) (baseStart_1849477 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1849477 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1849477 prefixEnd_1849477 := by exact prefixLift 1849477
  have htrace : WordTrace (prefixWord ++ tailWord_1849477) baseStart_1849477 baseEnd_1849477 := by
    simpa [prefixWord, tailWord_1849477, baseEnd_1849477] using wordTrace_append hprefix tailTrace_1849477
  have hstable : (prefixWord ++ tailWord_1849477).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1849477).length < 2 ^ (prefixWord ++ tailWord_1849477).sum := by decide
  have hdescent : baseEnd_1849477 < baseStart_1849477 := by decide
  rcases family_descends (prefixWord ++ tailWord_1849477) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1849480 : List Nat := [2, 1, 3, 4, 1, 1, 1, 4, 4]
def baseStart_1849480 : Nat := 118140960795 + 1849480 * 2 ^ 59
def prefixEnd_1849480 : Nat := 4983230072969 + 3 ^ 40 * 1849480 * 2
def baseEnd_1849480 : Nat := 422076533723346282086401

theorem tailTrace_1849480 : CollatzResearch.WordTrace tailWord_1849480 prefixEnd_1849480 422076533723346282086401 := by
  unfold tailWord_1849480
  simp only [CollatzResearch.WordTrace]
  refine ⟨33728038669828650440864947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44970718226438200587819929 33728038669828650440864947)
  ·
    refine ⟨50592058004742975661297421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33728038669828650440864947 50592058004742975661297421)
    ·
      refine ⟨18972021751778615872986533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 50592058004742975661297421 18972021751778615872986533)
      ·
        refine ⟨3557254078458490476184975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 18972021751778615872986533 3557254078458490476184975)
        ·
          refine ⟨5335881117687735714277463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3557254078458490476184975 5335881117687735714277463)
          ·
            refine ⟨8003821676531603571416195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5335881117687735714277463 8003821676531603571416195)
            ·
              refine ⟨12005732514797405357124293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8003821676531603571416195 12005732514797405357124293)
              ·
                refine ⟨2251074846524513504460805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12005732514797405357124293 2251074846524513504460805)
                ·
                  refine ⟨422076533723346282086401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2251074846524513504460805 422076533723346282086401)
                  ·
                    rfl

theorem cell21_1849480_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 1, 1, 4, 4].length) (baseStart_1849480 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1849480 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1849480 prefixEnd_1849480 := by exact prefixLift 1849480
  have htrace : WordTrace (prefixWord ++ tailWord_1849480) baseStart_1849480 baseEnd_1849480 := by
    simpa [prefixWord, tailWord_1849480, baseEnd_1849480] using wordTrace_append hprefix tailTrace_1849480
  have hstable : (prefixWord ++ tailWord_1849480).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1849480).length < 2 ^ (prefixWord ++ tailWord_1849480).sum := by decide
  have hdescent : baseEnd_1849480 < baseStart_1849480 := by decide
  rcases family_descends (prefixWord ++ tailWord_1849480) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1849607 : List Nat := [1, 1, 4, 5, 2, 1, 2, 1, 4]
def baseStart_1849607 : Nat := 118140960795 + 1849607 * 2 ^ 59
def prefixEnd_1849607 : Nat := 4983230072969 + 3 ^ 40 * 1849607 * 2
def baseEnd_1849607 : Nat := 422105516853622283469475

theorem tailTrace_1849607 : CollatzResearch.WordTrace tailWord_1849607 prefixEnd_1849607 422105516853622283469475 := by
  unfold tailWord_1849607
  simp only [CollatzResearch.WordTrace]
  refine ⟨67460709410197201571603075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44973806273464801047735383 67460709410197201571603075)
  ·
    refine ⟨101191064115295802357404613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67460709410197201571603075 101191064115295802357404613)
    ·
      refine ⟨18973324521617962942013365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 101191064115295802357404613 18973324521617962942013365)
      ·
        refine ⟨1778749173901684025813753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 18973324521617962942013365 1778749173901684025813753)
        ·
          refine ⟨1334061880426263019360315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1778749173901684025813753 1334061880426263019360315)
          ·
            refine ⟨2001092820639394529040473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1334061880426263019360315 2001092820639394529040473)
            ·
              refine ⟨1500819615479545896780355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2001092820639394529040473 1500819615479545896780355)
              ·
                refine ⟨2251229423219318845170533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1500819615479545896780355 2251229423219318845170533)
                ·
                  refine ⟨422105516853622283469475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2251229423219318845170533 422105516853622283469475)
                  ·
                    rfl

theorem cell21_1849607_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 5, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 5, 2, 1, 2, 1, 4].length) (baseStart_1849607 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1849607 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1849607 prefixEnd_1849607 := by exact prefixLift 1849607
  have htrace : WordTrace (prefixWord ++ tailWord_1849607) baseStart_1849607 baseEnd_1849607 := by
    simpa [prefixWord, tailWord_1849607, baseEnd_1849607] using wordTrace_append hprefix tailTrace_1849607
  have hstable : (prefixWord ++ tailWord_1849607).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1849607).length < 2 ^ (prefixWord ++ tailWord_1849607).sum := by decide
  have hdescent : baseEnd_1849607 < baseStart_1849607 := by decide
  rcases family_descends (prefixWord ++ tailWord_1849607) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1849646 : List Nat := [4, 1, 3, 3, 10]
def baseStart_1849646 : Nat := 118140960795 + 1849646 * 2 ^ 59
def prefixEnd_1849646 : Nat := 4983230072969 + 3 ^ 40 * 1849646 * 2
def baseEnd_1849646 : Nat := 5211289101048973855795

theorem tailTrace_1849646 : CollatzResearch.WordTrace tailWord_1849646 prefixEnd_1849646 5211289101048973855795 := by
  unfold tailWord_1849646
  simp only [CollatzResearch.WordTrace]
  refine ⟨8432766482131988904034099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 44974754571370607488181861 8432766482131988904034099)
  ·
    refine ⟨12649149723197983356051149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8432766482131988904034099 12649149723197983356051149)
    ·
      refine ⟨4743431146199243758519181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12649149723197983356051149 4743431146199243758519181)
      ·
        refine ⟨1778786679824716409444693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4743431146199243758519181 1778786679824716409444693)
        ·
          refine ⟨5211289101048973855795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 10 1778786679824716409444693 5211289101048973855795)
          ·
            rfl

theorem cell21_1849646_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 3, 10].length) (baseStart_1849646 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1849646 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1849646 prefixEnd_1849646 := by exact prefixLift 1849646
  have htrace : WordTrace (prefixWord ++ tailWord_1849646) baseStart_1849646 baseEnd_1849646 := by
    simpa [prefixWord, tailWord_1849646, baseEnd_1849646] using wordTrace_append hprefix tailTrace_1849646
  have hstable : (prefixWord ++ tailWord_1849646).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1849646).length < 2 ^ (prefixWord ++ tailWord_1849646).sum := by decide
  have hdescent : baseEnd_1849646 < baseStart_1849646 := by decide
  rcases family_descends (prefixWord ++ tailWord_1849646) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1849652 : List Nat := [2, 5, 1, 1, 1, 4, 2, 2, 3]
def baseStart_1849652 : Nat := 118140960795 + 1849652 * 2 ^ 59
def prefixEnd_1849652 : Nat := 4983230072969 + 3 ^ 40 * 1849652 * 2
def baseEnd_1849652 : Nat := 422115786466712205219383

theorem tailTrace_1849652 : CollatzResearch.WordTrace tailWord_1849652 prefixEnd_1849652 422115786466712205219383 := by
  unfold tailWord_1849652
  simp only [CollatzResearch.WordTrace]
  refine ⟨33731175347517087128495605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44974900463356116171327473 33731175347517087128495605)
  ·
    refine ⟨3162297688829726918296463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 33731175347517087128495605 3162297688829726918296463)
    ·
      refine ⟨4743446533244590377444695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3162297688829726918296463 4743446533244590377444695)
      ·
        refine ⟨7115169799866885566167043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4743446533244590377444695 7115169799866885566167043)
        ·
          refine ⟨10672754699800328349250565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7115169799866885566167043 10672754699800328349250565)
          ·
            refine ⟨2001141506212561565484481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 10672754699800328349250565 2001141506212561565484481)
            ·
              refine ⟨1500856129659421174113361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2001141506212561565484481 1500856129659421174113361)
              ·
                refine ⟨1125642097244565880585021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1500856129659421174113361 1125642097244565880585021)
                ·
                  refine ⟨422115786466712205219383, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1125642097244565880585021 422115786466712205219383)
                  ·
                    rfl

theorem cell21_1849652_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 4, 2, 2, 3].length) (baseStart_1849652 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1849652 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1849652 prefixEnd_1849652 := by exact prefixLift 1849652
  have htrace : WordTrace (prefixWord ++ tailWord_1849652) baseStart_1849652 baseEnd_1849652 := by
    simpa [prefixWord, tailWord_1849652, baseEnd_1849652] using wordTrace_append hprefix tailTrace_1849652
  have hstable : (prefixWord ++ tailWord_1849652).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1849652).length < 2 ^ (prefixWord ++ tailWord_1849652).sum := by decide
  have hdescent : baseEnd_1849652 < baseStart_1849652 := by decide
  rcases family_descends (prefixWord ++ tailWord_1849652) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1849660 : List Nat := [2, 2, 2, 2, 1, 2, 2, 3, 5]
def baseStart_1849660 : Nat := 118140960795 + 1849660 * 2 ^ 59
def prefixEnd_1849660 : Nat := 4983230072969 + 3 ^ 40 * 1849660 * 2
def baseEnd_1849660 : Nat := 422117612175705969086033

theorem tailTrace_1849660 : CollatzResearch.WordTrace tailWord_1849660 prefixEnd_1849660 422117612175705969086033 := by
  unfold tailWord_1849660
  simp only [CollatzResearch.WordTrace]
  refine ⟨33731321239502595811641217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44975094986003461082188289 33731321239502595811641217)
  ·
    refine ⟨25298490929626946858730913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33731321239502595811641217 25298490929626946858730913)
    ·
      refine ⟨18973868197220210144048185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25298490929626946858730913 18973868197220210144048185)
      ·
        refine ⟨14230401147915157608036139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18973868197220210144048185 14230401147915157608036139)
        ·
          refine ⟨21345601721872736412054209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14230401147915157608036139 21345601721872736412054209)
          ·
            refine ⟨16009201291404552309040657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21345601721872736412054209 16009201291404552309040657)
            ·
              refine ⟨12006900968553414231780493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16009201291404552309040657 12006900968553414231780493)
              ·
                refine ⟨4502587863207530336917685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12006900968553414231780493 4502587863207530336917685)
                ·
                  refine ⟨422117612175705969086033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4502587863207530336917685 422117612175705969086033)
                  ·
                    rfl

theorem cell21_1849660_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 2, 3, 5].length) (baseStart_1849660 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1849660 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1849660 prefixEnd_1849660 := by exact prefixLift 1849660
  have htrace : WordTrace (prefixWord ++ tailWord_1849660) baseStart_1849660 baseEnd_1849660 := by
    simpa [prefixWord, tailWord_1849660, baseEnd_1849660] using wordTrace_append hprefix tailTrace_1849660
  have hstable : (prefixWord ++ tailWord_1849660).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1849660).length < 2 ^ (prefixWord ++ tailWord_1849660).sum := by decide
  have hdescent : baseEnd_1849660 < baseStart_1849660 := by decide
  rcases family_descends (prefixWord ++ tailWord_1849660) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1849674 : List Nat := [3, 1, 2, 1, 1, 1, 1, 1, 10]
def baseStart_1849674 : Nat := 118140960795 + 1849674 * 2 ^ 59
def prefixEnd_1849674 : Nat := 4983230072969 + 3 ^ 40 * 1849674 * 2
def baseEnd_1849674 : Nat := 422120807166445055852671

theorem tailTrace_1849674 : CollatzResearch.WordTrace tailWord_1849674 prefixEnd_1849674 422120807166445055852671 := by
  unfold tailWord_1849674
  simp only [CollatzResearch.WordTrace]
  refine ⟨16865788275238618003573019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 44975435400636314676194717 16865788275238618003573019)
  ·
    refine ⟨25298682412857927005359529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16865788275238618003573019 25298682412857927005359529)
    ·
      refine ⟨18974011809643445254019647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25298682412857927005359529 18974011809643445254019647)
      ·
        refine ⟨28461017714465167881029471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18974011809643445254019647 28461017714465167881029471)
        ·
          refine ⟨42691526571697751821544207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28461017714465167881029471 42691526571697751821544207)
          ·
            refine ⟨64037289857546627732316311, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42691526571697751821544207 64037289857546627732316311)
            ·
              refine ⟨96055934786319941598474467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64037289857546627732316311 96055934786319941598474467)
              ·
                refine ⟨144083902179479912397711701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 96055934786319941598474467 144083902179479912397711701)
                ·
                  refine ⟨422120807166445055852671, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 144083902179479912397711701 422120807166445055852671)
                  ·
                    rfl

theorem cell21_1849674_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 10].length) (baseStart_1849674 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1849674 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1849674 prefixEnd_1849674 := by exact prefixLift 1849674
  have htrace : WordTrace (prefixWord ++ tailWord_1849674) baseStart_1849674 baseEnd_1849674 := by
    simpa [prefixWord, tailWord_1849674, baseEnd_1849674] using wordTrace_append hprefix tailTrace_1849674
  have hstable : (prefixWord ++ tailWord_1849674).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1849674).length < 2 ^ (prefixWord ++ tailWord_1849674).sum := by decide
  have hdescent : baseEnd_1849674 < baseStart_1849674 := by decide
  rcases family_descends (prefixWord ++ tailWord_1849674) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1849736 : List Nat := [2, 1, 3, 3, 1, 1, 1, 4, 5]
def baseStart_1849736 : Nat := 118140960795 + 1849736 * 2 ^ 59
def prefixEnd_1849736 : Nat := 4983230072969 + 3 ^ 40 * 1849736 * 2
def baseEnd_1849736 : Nat := 422134956411146725819211

theorem tailTrace_1849736 : CollatzResearch.WordTrace tailWord_1849736 prefixEnd_1849736 422134956411146725819211 := by
  unfold tailWord_1849736
  simp only [CollatzResearch.WordTrace]
  refine ⟨33732707213364928301524531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44976942951153237735366041 33732707213364928301524531)
  ·
    refine ⟨50599060820047392452286797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33732707213364928301524531 50599060820047392452286797)
    ·
      refine ⟨18974647807517772169607549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 50599060820047392452286797 18974647807517772169607549)
      ·
        refine ⟨7115492927819164563602831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18974647807517772169607549 7115492927819164563602831)
        ·
          refine ⟨10673239391728746845404247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7115492927819164563602831 10673239391728746845404247)
          ·
            refine ⟨16009859087593120268106371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10673239391728746845404247 16009859087593120268106371)
            ·
              refine ⟨24014788631389680402159557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16009859087593120268106371 24014788631389680402159557)
              ·
                refine ⟨4502772868385565075404917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 24014788631389680402159557 4502772868385565075404917)
                ·
                  refine ⟨422134956411146725819211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4502772868385565075404917 422134956411146725819211)
                  ·
                    rfl

theorem cell21_1849736_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 1, 4, 5].length) (baseStart_1849736 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1849736 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1849736 prefixEnd_1849736 := by exact prefixLift 1849736
  have htrace : WordTrace (prefixWord ++ tailWord_1849736) baseStart_1849736 baseEnd_1849736 := by
    simpa [prefixWord, tailWord_1849736, baseEnd_1849736] using wordTrace_append hprefix tailTrace_1849736
  have hstable : (prefixWord ++ tailWord_1849736).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1849736).length < 2 ^ (prefixWord ++ tailWord_1849736).sum := by decide
  have hdescent : baseEnd_1849736 < baseStart_1849736 := by decide
  rcases family_descends (prefixWord ++ tailWord_1849736) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1849767 : List Nat := [1, 1, 6, 1, 1, 2, 2, 1, 6]
def baseStart_1849767 : Nat := 118140960795 + 1849767 * 2 ^ 59
def prefixEnd_1849767 : Nat := 4983230072969 + 3 ^ 40 * 1849767 * 2
def baseEnd_1849767 : Nat := 422142031033497560802481

theorem tailTrace_1849767 : CollatzResearch.WordTrace tailWord_1849767 prefixEnd_1849767 422142031033497560802481 := by
  unfold tailWord_1849767
  simp only [CollatzResearch.WordTrace]
  refine ⟨67466545089617548897427555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44977696726411699264951703 67466545089617548897427555)
  ·
    refine ⟨101199817634426323346141333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67466545089617548897427555 101199817634426323346141333)
    ·
      refine ⟨4743741451613733906850375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 101199817634426323346141333 4743741451613733906850375)
      ·
        refine ⟨7115612177420600860275563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4743741451613733906850375 7115612177420600860275563)
        ·
          refine ⟨10673418266130901290413345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7115612177420600860275563 10673418266130901290413345)
          ·
            refine ⟨8005063699598175967810009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10673418266130901290413345 8005063699598175967810009)
            ·
              refine ⟨6003797774698631975857507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8005063699598175967810009 6003797774698631975857507)
              ·
                refine ⟨9005696662047947963786261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6003797774698631975857507 9005696662047947963786261)
                ·
                  refine ⟨422142031033497560802481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9005696662047947963786261 422142031033497560802481)
                  ·
                    rfl

theorem cell21_1849767_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 2, 2, 1, 6].length) (baseStart_1849767 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1849767 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1849767 prefixEnd_1849767 := by exact prefixLift 1849767
  have htrace : WordTrace (prefixWord ++ tailWord_1849767) baseStart_1849767 baseEnd_1849767 := by
    simpa [prefixWord, tailWord_1849767, baseEnd_1849767] using wordTrace_append hprefix tailTrace_1849767
  have hstable : (prefixWord ++ tailWord_1849767).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1849767).length < 2 ^ (prefixWord ++ tailWord_1849767).sum := by decide
  have hdescent : baseEnd_1849767 < baseStart_1849767 := by decide
  rcases family_descends (prefixWord ++ tailWord_1849767) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1849795 : List Nat := [1, 1, 1, 3, 1, 1, 3, 3, 7]
def baseStart_1849795 : Nat := 118140960795 + 1849795 * 2 ^ 59
def prefixEnd_1849795 : Nat := 4983230072969 + 3 ^ 40 * 1849795 * 2
def baseEnd_1849795 : Nat := 422148421014975734335757

theorem tailTrace_1849795 : CollatzResearch.WordTrace tailWord_1849795 prefixEnd_1849795 422148421014975734335757 := by
  unfold tailWord_1849795
  simp only [CollatzResearch.WordTrace]
  refine ⟨67467566333516109679446839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44978377555677406452964559 67467566333516109679446839)
  ·
    refine ⟨101201349500274164519170259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67467566333516109679446839 101201349500274164519170259)
    ·
      refine ⟨151802024250411246778755389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101201349500274164519170259 151802024250411246778755389)
      ·
        refine ⟨56925759093904217542033271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 151802024250411246778755389 56925759093904217542033271)
        ·
          refine ⟨85388638640856326313049907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56925759093904217542033271 85388638640856326313049907)
          ·
            refine ⟨128082957961284489469574861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 85388638640856326313049907 128082957961284489469574861)
            ·
              refine ⟨48031109235481683551090573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 128082957961284489469574861 48031109235481683551090573)
              ·
                refine ⟨18011665963305631331658965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 48031109235481683551090573 18011665963305631331658965)
                ·
                  refine ⟨422148421014975734335757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 18011665963305631331658965 422148421014975734335757)
                  ·
                    rfl

theorem cell21_1849795_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 3, 3, 7].length) (baseStart_1849795 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1849795 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1849795 prefixEnd_1849795 := by exact prefixLift 1849795
  have htrace : WordTrace (prefixWord ++ tailWord_1849795) baseStart_1849795 baseEnd_1849795 := by
    simpa [prefixWord, tailWord_1849795, baseEnd_1849795] using wordTrace_append hprefix tailTrace_1849795
  have hstable : (prefixWord ++ tailWord_1849795).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1849795).length < 2 ^ (prefixWord ++ tailWord_1849795).sum := by decide
  have hdescent : baseEnd_1849795 < baseStart_1849795 := by decide
  rcases family_descends (prefixWord ++ tailWord_1849795) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1849992 : List Nat := [2, 1, 3, 15]
def baseStart_1849992 : Nat := 118140960795 + 1849992 * 2 ^ 59
def prefixEnd_1849992 : Nat := 4983230072969 + 3 ^ 40 * 1849992 * 2
def baseEnd_1849992 : Nat := 1737421313164391644247

theorem tailTrace_1849992 : CollatzResearch.WordTrace tailWord_1849992 prefixEnd_1849992 1737421313164391644247 := by
  unfold tailWord_1849992
  simp only [CollatzResearch.WordTrace]
  refine ⟨33737375756901206162184115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44983167675868274882912153 33737375756901206162184115)
  ·
    refine ⟨50606063635351809243276173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33737375756901206162184115 50606063635351809243276173)
    ·
      refine ⟨18977273863256928466228565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 50606063635351809243276173 18977273863256928466228565)
      ·
        refine ⟨1737421313164391644247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 15 18977273863256928466228565 1737421313164391644247)
        ·
          rfl

theorem cell21_1849992_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 15].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 15].length) (baseStart_1849992 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1849992 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1849992 prefixEnd_1849992 := by exact prefixLift 1849992
  have htrace : WordTrace (prefixWord ++ tailWord_1849992) baseStart_1849992 baseEnd_1849992 := by
    simpa [prefixWord, tailWord_1849992, baseEnd_1849992] using wordTrace_append hprefix tailTrace_1849992
  have hstable : (prefixWord ++ tailWord_1849992).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1849992).length < 2 ^ (prefixWord ++ tailWord_1849992).sum := by decide
  have hdescent : baseEnd_1849992 < baseStart_1849992 := by decide
  rcases family_descends (prefixWord ++ tailWord_1849992) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1850085 : List Nat := [1, 3, 1, 4, 1, 3, 1, 7]
def baseStart_1850085 : Nat := 118140960795 + 1850085 * 2 ^ 59
def prefixEnd_1850085 : Nat := 4983230072969 + 3 ^ 40 * 1850085 * 2
def baseEnd_1850085 : Nat := 140738200988666558167277

theorem tailTrace_1850085 : CollatzResearch.WordTrace tailWord_1850085 prefixEnd_1850085 140738200988666558167277 := by
  unfold tailWord_1850085
  simp only [CollatzResearch.WordTrace]
  refine ⟨67478143502465489207503709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44985429001643659471669139 67478143502465489207503709)
  ·
    refine ⟨25304303813424558452813891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 67478143502465489207503709 25304303813424558452813891)
    ·
      refine ⟨37956455720136837679220837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25304303813424558452813891 37956455720136837679220837)
      ·
        refine ⟨7116835447525657064853907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 37956455720136837679220837 7116835447525657064853907)
        ·
          refine ⟨10675253171288485597280861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7116835447525657064853907 10675253171288485597280861)
          ·
            refine ⟨4003219939233182098980323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10675253171288485597280861 4003219939233182098980323)
            ·
              refine ⟨6004829908849773148470485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4003219939233182098980323 6004829908849773148470485)
              ·
                refine ⟨140738200988666558167277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6004829908849773148470485 140738200988666558167277)
                ·
                  rfl

theorem cell21_1850085_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 3, 1, 7].length) (baseStart_1850085 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1850085 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1850085 prefixEnd_1850085 := by exact prefixLift 1850085
  have htrace : WordTrace (prefixWord ++ tailWord_1850085) baseStart_1850085 baseEnd_1850085 := by
    simpa [prefixWord, tailWord_1850085, baseEnd_1850085] using wordTrace_append hprefix tailTrace_1850085
  have hstable : (prefixWord ++ tailWord_1850085).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1850085).length < 2 ^ (prefixWord ++ tailWord_1850085).sum := by decide
  have hdescent : baseEnd_1850085 < baseStart_1850085 := by decide
  rcases family_descends (prefixWord ++ tailWord_1850085) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1850220 : List Nat := [2, 2, 1, 1, 4, 1, 10]
def baseStart_1850220 : Nat := 118140960795 + 1850220 * 2 ^ 59
def prefixEnd_1850220 : Nat := 4983230072969 + 3 ^ 40 * 1850220 * 2
def baseEnd_1850220 : Nat := 46916156867252159972395

theorem tailTrace_1850220 : CollatzResearch.WordTrace tailWord_1850220 prefixEnd_1850220 46916156867252159972395 := by
  unfold tailWord_1850220
  simp only [CollatzResearch.WordTrace]
  refine ⟨33741533678488203631834057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44988711571317604842445409 33741533678488203631834057)
  ·
    refine ⟨25306150258866152723875543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33741533678488203631834057 25306150258866152723875543)
    ·
      refine ⟨37959225388299229085813315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25306150258866152723875543 37959225388299229085813315)
      ·
        refine ⟨56938838082448843628719973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37959225388299229085813315 56938838082448843628719973)
        ·
          refine ⟨10676032140459158180384995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 56938838082448843628719973 10676032140459158180384995)
          ·
            refine ⟨16014048210688737270577493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10676032140459158180384995 16014048210688737270577493)
            ·
              refine ⟨46916156867252159972395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 16014048210688737270577493 46916156867252159972395)
              ·
                rfl

theorem cell21_1850220_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 10].length) (baseStart_1850220 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1850220 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1850220 prefixEnd_1850220 := by exact prefixLift 1850220
  have htrace : WordTrace (prefixWord ++ tailWord_1850220) baseStart_1850220 baseEnd_1850220 := by
    simpa [prefixWord, tailWord_1850220, baseEnd_1850220] using wordTrace_append hprefix tailTrace_1850220
  have hstable : (prefixWord ++ tailWord_1850220).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1850220).length < 2 ^ (prefixWord ++ tailWord_1850220).sum := by decide
  have hdescent : baseEnd_1850220 < baseStart_1850220 := by decide
  rcases family_descends (prefixWord ++ tailWord_1850220) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1850251 : List Nat := [1, 1, 1, 1, 4, 2, 4, 2, 5]
def baseStart_1850251 : Nat := 118140960795 + 1850251 * 2 ^ 59
def prefixEnd_1850251 : Nat := 4983230072969 + 3 ^ 40 * 1850251 * 2
def baseEnd_1850251 : Nat := 422252486427620274734825

theorem tailTrace_1850251 : CollatzResearch.WordTrace tailWord_1850251 prefixEnd_1850251 422252486427620274734825 := by
  unfold tailWord_1850251
  simp only [CollatzResearch.WordTrace]
  refine ⟨67484198019864099558046607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44989465346576066372031071 67484198019864099558046607)
  ·
    refine ⟨101226297029796149337069911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67484198019864099558046607 101226297029796149337069911)
    ·
      refine ⟨151839445544694224005604867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101226297029796149337069911 151839445544694224005604867)
      ·
        refine ⟨227759168317041336008407301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 151839445544694224005604867 227759168317041336008407301)
        ·
          refine ⟨42704844059445250501576369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 227759168317041336008407301 42704844059445250501576369)
          ·
            refine ⟨32028633044583937876182277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42704844059445250501576369 32028633044583937876182277)
            ·
              refine ⟨6005368695859488351784177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 32028633044583937876182277 6005368695859488351784177)
              ·
                refine ⟨4504026521894616263838133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6005368695859488351784177 4504026521894616263838133)
                ·
                  refine ⟨422252486427620274734825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4504026521894616263838133 422252486427620274734825)
                  ·
                    rfl

theorem cell21_1850251_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 4, 2, 5].length) (baseStart_1850251 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1850251 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1850251 prefixEnd_1850251 := by exact prefixLift 1850251
  have htrace : WordTrace (prefixWord ++ tailWord_1850251) baseStart_1850251 baseEnd_1850251 := by
    simpa [prefixWord, tailWord_1850251, baseEnd_1850251] using wordTrace_append hprefix tailTrace_1850251
  have hstable : (prefixWord ++ tailWord_1850251).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1850251).length < 2 ^ (prefixWord ++ tailWord_1850251).sum := by decide
  have hdescent : baseEnd_1850251 < baseStart_1850251 := by decide
  rcases family_descends (prefixWord ++ tailWord_1850251) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1850296 : List Nat := [2, 1, 2, 1, 2, 4, 1, 8]
def baseStart_1850296 : Nat := 118140960795 + 1850296 * 2 ^ 59
def prefixEnd_1850296 : Nat := 4983230072969 + 3 ^ 40 * 1850296 * 2
def baseEnd_1850296 : Nat := 140754252013570065494911

theorem tailTrace_1850296 : CollatzResearch.WordTrace tailWord_1850296 prefixEnd_1850296 140754252013570065494911 := by
  unfold tailWord_1850296
  simp only [CollatzResearch.WordTrace]
  refine ⟨33742919652350536121717371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44990559536467381495623161 33742919652350536121717371)
  ·
    refine ⟨50614379478525804182576057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33742919652350536121717371 50614379478525804182576057)
    ·
      refine ⟨37960784608894353136932043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50614379478525804182576057 37960784608894353136932043)
      ·
        refine ⟨56941176913341529705398065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37960784608894353136932043 56941176913341529705398065)
        ·
          refine ⟨42705882685006147279048549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56941176913341529705398065 42705882685006147279048549)
          ·
            refine ⟨8007353003438652614821603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 42705882685006147279048549 8007353003438652614821603)
            ·
              refine ⟨12011029505157978922232405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8007353003438652614821603 12011029505157978922232405)
              ·
                refine ⟨140754252013570065494911, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 12011029505157978922232405 140754252013570065494911)
                ·
                  rfl

theorem cell21_1850296_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 4, 1, 8].length) (baseStart_1850296 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1850296 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1850296 prefixEnd_1850296 := by exact prefixLift 1850296
  have htrace : WordTrace (prefixWord ++ tailWord_1850296) baseStart_1850296 baseEnd_1850296 := by
    simpa [prefixWord, tailWord_1850296, baseEnd_1850296] using wordTrace_append hprefix tailTrace_1850296
  have hstable : (prefixWord ++ tailWord_1850296).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1850296).length < 2 ^ (prefixWord ++ tailWord_1850296).sum := by decide
  have hdescent : baseEnd_1850296 < baseStart_1850296 := by decide
  rcases family_descends (prefixWord ++ tailWord_1850296) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1850403 : List Nat := [1, 1, 1, 4, 3, 2, 1, 3, 5]
def baseStart_1850403 : Nat := 118140960795 + 1850403 * 2 ^ 59
def prefixEnd_1850403 : Nat := 4983230072969 + 3 ^ 40 * 1850403 * 2
def baseEnd_1850403 : Nat := 422287174898501788201181

theorem tailTrace_1850403 : CollatzResearch.WordTrace tailWord_1850403 prefixEnd_1850403 422287174898501788201181 := by
  unfold tailWord_1850403
  simp only [CollatzResearch.WordTrace]
  refine ⟨67489741915313429517579863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44993161276875619678386575 67489741915313429517579863)
  ·
    refine ⟨101234612872970144276369795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67489741915313429517579863 101234612872970144276369795)
    ·
      refine ⟨151851919309455216414554693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101234612872970144276369795 151851919309455216414554693)
      ·
        refine ⟨28472234870522853077729005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 151851919309455216414554693 28472234870522853077729005)
        ·
          refine ⟨10677088076446069904148377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28472234870522853077729005 10677088076446069904148377)
          ·
            refine ⟨8007816057334552428111283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10677088076446069904148377 8007816057334552428111283)
            ·
              refine ⟨12011724086001828642166925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8007816057334552428111283 12011724086001828642166925)
              ·
                refine ⟨4504396532250685740812597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12011724086001828642166925 4504396532250685740812597)
                ·
                  refine ⟨422287174898501788201181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4504396532250685740812597 422287174898501788201181)
                  ·
                    rfl

theorem cell21_1850403_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 2, 1, 3, 5].length) (baseStart_1850403 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1850403 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1850403 prefixEnd_1850403 := by exact prefixLift 1850403
  have htrace : WordTrace (prefixWord ++ tailWord_1850403) baseStart_1850403 baseEnd_1850403 := by
    simpa [prefixWord, tailWord_1850403, baseEnd_1850403] using wordTrace_append hprefix tailTrace_1850403
  have hstable : (prefixWord ++ tailWord_1850403).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1850403).length < 2 ^ (prefixWord ++ tailWord_1850403).sum := by decide
  have hdescent : baseEnd_1850403 < baseStart_1850403 := by decide
  rcases family_descends (prefixWord ++ tailWord_1850403) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1850600 : List Nat := [2, 1, 4, 1, 2, 1, 3, 7]
def baseStart_1850600 : Nat := 118140960795 + 1850600 * 2 ^ 59
def prefixEnd_1850600 : Nat := 4983230072969 + 3 ^ 40 * 1850600 * 2
def baseEnd_1850600 : Nat := 140777377660824407805815

theorem tailTrace_1850600 : CollatzResearch.WordTrace tailWord_1850600 prefixEnd_1850600 140777377660824407805815 := by
  unfold tailWord_1850600
  simp only [CollatzResearch.WordTrace]
  refine ⟨33748463547799866081250627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44997951397066488108334169 33748463547799866081250627)
  ·
    refine ⟨50622695321699799121875941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33748463547799866081250627 50622695321699799121875941)
    ·
      refine ⟨9491755372818712335351739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 50622695321699799121875941 9491755372818712335351739)
      ·
        refine ⟨14237633059228068503027609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9491755372818712335351739 14237633059228068503027609)
        ·
          refine ⟨10678224794421051377270707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14237633059228068503027609 10678224794421051377270707)
          ·
            refine ⟨16017337191631577065906061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10678224794421051377270707 16017337191631577065906061)
            ·
              refine ⟨6006501446861841399714773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16017337191631577065906061 6006501446861841399714773)
              ·
                refine ⟨140777377660824407805815, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6006501446861841399714773 140777377660824407805815)
                ·
                  rfl

theorem cell21_1850600_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 3, 7].length) (baseStart_1850600 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1850600 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1850600 prefixEnd_1850600 := by exact prefixLift 1850600
  have htrace : WordTrace (prefixWord ++ tailWord_1850600) baseStart_1850600 baseEnd_1850600 := by
    simpa [prefixWord, tailWord_1850600, baseEnd_1850600] using wordTrace_append hprefix tailTrace_1850600
  have hstable : (prefixWord ++ tailWord_1850600).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1850600).length < 2 ^ (prefixWord ++ tailWord_1850600).sum := by decide
  have hdescent : baseEnd_1850600 < baseStart_1850600 := by decide
  rcases family_descends (prefixWord ++ tailWord_1850600) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1850724 : List Nat := [2, 3, 1, 1, 3, 2, 1, 5, 3]
def baseStart_1850724 : Nat := 118140960795 + 1850724 * 2 ^ 59
def prefixEnd_1850724 : Nat := 4983230072969 + 3 ^ 40 * 1850724 * 2
def baseEnd_1850724 : Nat := 422360431471876563350525

theorem tailTrace_1850724 : CollatzResearch.WordTrace tailWord_1850724 prefixEnd_1850724 422360431471876563350525 := by
  unfold tailWord_1850724
  simp only [CollatzResearch.WordTrace]
  refine ⟨33750724873575250670007613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45000966498100334226676817 33750724873575250670007613)
  ·
    refine ⟨12656521827590719001252855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 33750724873575250670007613 12656521827590719001252855)
    ·
      refine ⟨18984782741386078501879283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12656521827590719001252855 18984782741386078501879283)
      ·
        refine ⟨28477174112079117752818925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18984782741386078501879283 28477174112079117752818925)
        ·
          refine ⟨10678940292029669157307097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28477174112079117752818925 10678940292029669157307097)
          ·
            refine ⟨8009205219022251867980323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10678940292029669157307097 8009205219022251867980323)
            ·
              refine ⟨12013807828533377801970485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8009205219022251867980323 12013807828533377801970485)
              ·
                refine ⟨1126294483925004168934733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 12013807828533377801970485 1126294483925004168934733)
                ·
                  refine ⟨422360431471876563350525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1126294483925004168934733 422360431471876563350525)
                  ·
                    rfl

theorem cell21_1850724_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 2, 1, 5, 3].length) (baseStart_1850724 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1850724 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1850724 prefixEnd_1850724 := by exact prefixLift 1850724
  have htrace : WordTrace (prefixWord ++ tailWord_1850724) baseStart_1850724 baseEnd_1850724 := by
    simpa [prefixWord, tailWord_1850724, baseEnd_1850724] using wordTrace_append hprefix tailTrace_1850724
  have hstable : (prefixWord ++ tailWord_1850724).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1850724).length < 2 ^ (prefixWord ++ tailWord_1850724).sum := by decide
  have hdescent : baseEnd_1850724 < baseStart_1850724 := by decide
  rcases family_descends (prefixWord ++ tailWord_1850724) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1850735 : List Nat := [1, 1, 2, 1, 3, 1, 12]
def baseStart_1850735 : Nat := 118140960795 + 1850735 * 2 ^ 59
def prefixEnd_1850735 : Nat := 4983230072969 + 3 ^ 40 * 1850735 * 2
def baseEnd_1850735 : Nat := 46929215757971443185241

theorem tailTrace_1850735 : CollatzResearch.WordTrace tailWord_1850735 prefixEnd_1850735 46929215757971443185241 := by
  unfold tailWord_1850735
  simp only [CollatzResearch.WordTrace]
  refine ⟨67501850950110650218665659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45001233966740433479110439 67501850950110650218665659)
  ·
    refine ⟨101252776425165975327998489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67501850950110650218665659 101252776425165975327998489)
    ·
      refine ⟨75939582318874481495998867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 101252776425165975327998489 75939582318874481495998867)
      ·
        refine ⟨113909373478311722243998301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75939582318874481495998867 113909373478311722243998301)
        ·
          refine ⟨42716015054366895841499363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 113909373478311722243998301 42716015054366895841499363)
          ·
            refine ⟨64074022581550343762249045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42716015054366895841499363 64074022581550343762249045)
            ·
              refine ⟨46929215757971443185241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 12 64074022581550343762249045 46929215757971443185241)
              ·
                rfl

theorem cell21_1850735_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 12].length) (baseStart_1850735 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1850735 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1850735 prefixEnd_1850735 := by exact prefixLift 1850735
  have htrace : WordTrace (prefixWord ++ tailWord_1850735) baseStart_1850735 baseEnd_1850735 := by
    simpa [prefixWord, tailWord_1850735, baseEnd_1850735] using wordTrace_append hprefix tailTrace_1850735
  have hstable : (prefixWord ++ tailWord_1850735).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1850735).length < 2 ^ (prefixWord ++ tailWord_1850735).sum := by decide
  have hdescent : baseEnd_1850735 < baseStart_1850735 := by decide
  rcases family_descends (prefixWord ++ tailWord_1850735) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1850755 : List Nat := [1, 1, 1, 3, 5, 2, 3, 1, 4]
def baseStart_1850755 : Nat := 118140960795 + 1850755 * 2 ^ 59
def prefixEnd_1850755 : Nat := 4983230072969 + 3 ^ 40 * 1850755 * 2
def baseEnd_1850755 : Nat := 422367506094227398333795

theorem tailTrace_1850755 : CollatzResearch.WordTrace tailWord_1850755 prefixEnd_1850755 422367506094227398333795 := by
  unfold tailWord_1850755
  simp only [CollatzResearch.WordTrace]
  refine ⟨67502580410038193634393719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45001720273358795756262479 67502580410038193634393719)
  ·
    refine ⟨101253870615057290451590579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67502580410038193634393719 101253870615057290451590579)
    ·
      refine ⟨151880805922585935677385869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101253870615057290451590579 151880805922585935677385869)
      ·
        refine ⟨56955302220969725879019701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 151880805922585935677385869 56955302220969725879019701)
        ·
          refine ⟨5339559583215911801158097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 56955302220969725879019701 5339559583215911801158097)
          ·
            refine ⟨4004669687411933850868573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5339559583215911801158097 4004669687411933850868573)
            ·
              refine ⟨1501751132779475194075715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4004669687411933850868573 1501751132779475194075715)
              ·
                refine ⟨2252626699169212791113573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1501751132779475194075715 2252626699169212791113573)
                ·
                  refine ⟨422367506094227398333795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2252626699169212791113573 422367506094227398333795)
                  ·
                    rfl

theorem cell21_1850755_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 2, 3, 1, 4].length) (baseStart_1850755 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1850755 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1850755 prefixEnd_1850755 := by exact prefixLift 1850755
  have htrace : WordTrace (prefixWord ++ tailWord_1850755) baseStart_1850755 baseEnd_1850755 := by
    simpa [prefixWord, tailWord_1850755, baseEnd_1850755] using wordTrace_append hprefix tailTrace_1850755
  have hstable : (prefixWord ++ tailWord_1850755).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1850755).length < 2 ^ (prefixWord ++ tailWord_1850755).sum := by decide
  have hdescent : baseEnd_1850755 < baseStart_1850755 := by decide
  rcases family_descends (prefixWord ++ tailWord_1850755) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1850828 : List Nat := [2, 2, 1, 4, 2, 1, 2, 7]
def baseStart_1850828 : Nat := 118140960795 + 1850828 * 2 ^ 59
def prefixEnd_1850828 : Nat := 4983230072969 + 3 ^ 40 * 1850828 * 2
def baseEnd_1850828 : Nat := 140794721896265164538993

theorem tailTrace_1850828 : CollatzResearch.WordTrace tailWord_1850828 prefixEnd_1850828 140794721896265164538993 := by
  unfold tailWord_1850828
  simp only [CollatzResearch.WordTrace]
  refine ⟨33752621469386863550900569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45003495292515818067867425 33752621469386863550900569)
  ·
    refine ⟨25314466102040147663175427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33752621469386863550900569 25314466102040147663175427)
    ·
      refine ⟨37971699153060221494763141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25314466102040147663175427 37971699153060221494763141)
      ·
        refine ⟨7119693591198791530268089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 37971699153060221494763141 7119693591198791530268089)
        ·
          refine ⟨5339770193399093647701067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7119693591198791530268089 5339770193399093647701067)
          ·
            refine ⟨8009655290098640471551601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5339770193399093647701067 8009655290098640471551601)
            ·
              refine ⟨6007241467573980353663701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8009655290098640471551601 6007241467573980353663701)
              ·
                refine ⟨140794721896265164538993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6007241467573980353663701 140794721896265164538993)
                ·
                  rfl

theorem cell21_1850828_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 1, 2, 7].length) (baseStart_1850828 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1850828 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1850828 prefixEnd_1850828 := by exact prefixLift 1850828
  have htrace : WordTrace (prefixWord ++ tailWord_1850828) baseStart_1850828 baseEnd_1850828 := by
    simpa [prefixWord, tailWord_1850828, baseEnd_1850828] using wordTrace_append hprefix tailTrace_1850828
  have hstable : (prefixWord ++ tailWord_1850828).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1850828).length < 2 ^ (prefixWord ++ tailWord_1850828).sum := by decide
  have hdescent : baseEnd_1850828 < baseStart_1850828 := by decide
  rcases family_descends (prefixWord ++ tailWord_1850828) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1850904 : List Nat := [2, 1, 2, 3, 4, 1, 8]
def baseStart_1850904 : Nat := 118140960795 + 1850904 * 2 ^ 59
def prefixEnd_1850904 : Nat := 4983230072969 + 3 ^ 40 * 1850904 * 2
def baseEnd_1850904 : Nat := 46933501102692916705573

theorem tailTrace_1850904 : CollatzResearch.WordTrace tailWord_1850904 prefixEnd_1850904 46933501102692916705573 := by
  unfold tailWord_1850904
  simp only [CollatzResearch.WordTrace]
  refine ⟨33754007443249196040783883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45005343257665594721045177 33754007443249196040783883)
  ·
    refine ⟨50631011164873794061175825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33754007443249196040783883 50631011164873794061175825)
    ·
      refine ⟨37973258373655345545881869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50631011164873794061175825 37973258373655345545881869)
      ·
        refine ⟨14239971890120754579705701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 37973258373655345545881869 14239971890120754579705701)
        ·
          refine ⟨2669994729397641483694819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 14239971890120754579705701 2669994729397641483694819)
          ·
            refine ⟨4004992094096462225542229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2669994729397641483694819 4004992094096462225542229)
            ·
              refine ⟨46933501102692916705573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 4004992094096462225542229 46933501102692916705573)
              ·
                rfl

theorem cell21_1850904_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 4, 1, 8].length) (baseStart_1850904 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1850904 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1850904 prefixEnd_1850904 := by exact prefixLift 1850904
  have htrace : WordTrace (prefixWord ++ tailWord_1850904) baseStart_1850904 baseEnd_1850904 := by
    simpa [prefixWord, tailWord_1850904, baseEnd_1850904] using wordTrace_append hprefix tailTrace_1850904
  have hstable : (prefixWord ++ tailWord_1850904).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1850904).length < 2 ^ (prefixWord ++ tailWord_1850904).sum := by decide
  have hdescent : baseEnd_1850904 < baseStart_1850904 := by decide
  rcases family_descends (prefixWord ++ tailWord_1850904) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1850980 : List Nat := [2, 3, 1, 1, 2, 4, 2, 6]
def baseStart_1850980 : Nat := 118140960795 + 1850980 * 2 ^ 59
def prefixEnd_1850980 : Nat := 4983230072969 + 3 ^ 40 * 1850980 * 2
def baseEnd_1850980 : Nat := 140806284719892335694445

theorem tailTrace_1850980 : CollatzResearch.WordTrace tailWord_1850980 prefixEnd_1850980 140806284719892335694445 := by
  unfold tailWord_1850980
  simp only [CollatzResearch.WordTrace]
  refine ⟨33755393417111528530667197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45007191222815371374222929 33755393417111528530667197)
  ·
    refine ⟨12658272531416823199000199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 33755393417111528530667197 12658272531416823199000199)
    ·
      refine ⟨18987408797125234798500299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12658272531416823199000199 18987408797125234798500299)
      ·
        refine ⟨28481113195687852197750449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18987408797125234798500299 28481113195687852197750449)
        ·
          refine ⟨21360834896765889148312837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28481113195687852197750449 21360834896765889148312837)
          ·
            refine ⟨4005156543143604215308657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 21360834896765889148312837 4005156543143604215308657)
            ·
              refine ⟨3003867407357703161481493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4005156543143604215308657 3003867407357703161481493)
              ·
                refine ⟨140806284719892335694445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3003867407357703161481493 140806284719892335694445)
                ·
                  rfl

theorem cell21_1850980_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 4, 2, 6].length) (baseStart_1850980 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1850980 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1850980 prefixEnd_1850980 := by exact prefixLift 1850980
  have htrace : WordTrace (prefixWord ++ tailWord_1850980) baseStart_1850980 baseEnd_1850980 := by
    simpa [prefixWord, tailWord_1850980, baseEnd_1850980] using wordTrace_append hprefix tailTrace_1850980
  have hstable : (prefixWord ++ tailWord_1850980).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1850980).length < 2 ^ (prefixWord ++ tailWord_1850980).sum := by decide
  have hdescent : baseEnd_1850980 < baseStart_1850980 := by decide
  rcases family_descends (prefixWord ++ tailWord_1850980) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1851011 : List Nat := [1, 1, 1, 3, 3, 1, 1, 7, 3]
def baseStart_1851011 : Nat := 118140960795 + 1851011 * 2 ^ 59
def prefixEnd_1851011 : Nat := 4983230072969 + 3 ^ 40 * 1851011 * 2
def baseEnd_1851011 : Nat := 422425928782027842066605

theorem tailTrace_1851011 : CollatzResearch.WordTrace tailWord_1851011 prefixEnd_1851011 422425928782027842066605 := by
  unfold tailWord_1851011
  simp only [CollatzResearch.WordTrace]
  refine ⟨67511917497110749355712887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45007944998073832903808591 67511917497110749355712887)
  ·
    refine ⟨101267876245666124033569331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67511917497110749355712887 101267876245666124033569331)
    ·
      refine ⟨151901814368499186050353997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101267876245666124033569331 151901814368499186050353997)
      ·
        refine ⟨56963180388187194768882749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 151901814368499186050353997 56963180388187194768882749)
        ·
          refine ⟨21361192645570198038331031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 56963180388187194768882749 21361192645570198038331031)
          ·
            refine ⟨32041788968355297057496547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21361192645570198038331031 32041788968355297057496547)
            ·
              refine ⟨48062683452532945586244821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32041788968355297057496547 48062683452532945586244821)
              ·
                refine ⟨1126469143418740912177613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 48062683452532945586244821 1126469143418740912177613)
                ·
                  refine ⟨422425928782027842066605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1126469143418740912177613 422425928782027842066605)
                  ·
                    rfl

theorem cell21_1851011_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 1, 7, 3].length) (baseStart_1851011 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1851011 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1851011 prefixEnd_1851011 := by exact prefixLift 1851011
  have htrace : WordTrace (prefixWord ++ tailWord_1851011) baseStart_1851011 baseEnd_1851011 := by
    simpa [prefixWord, tailWord_1851011, baseEnd_1851011] using wordTrace_append hprefix tailTrace_1851011
  have hstable : (prefixWord ++ tailWord_1851011).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1851011).length < 2 ^ (prefixWord ++ tailWord_1851011).sum := by decide
  have hdescent : baseEnd_1851011 < baseStart_1851011 := by decide
  rcases family_descends (prefixWord ++ tailWord_1851011) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1851062 : List Nat := [5, 1, 3, 1, 1, 2, 2, 3, 3]
def baseStart_1851062 : Nat := 118140960795 + 1851062 * 2 ^ 59
def prefixEnd_1851062 : Nat := 4983230072969 + 3 ^ 40 * 1851062 * 2
def baseEnd_1851062 : Nat := 422437567676863086716501

theorem tailTrace_1851062 : CollatzResearch.WordTrace tailWord_1851062 prefixEnd_1851062 422437567676863086716501 := by
  unfold tailWord_1851062
  simp only [CollatzResearch.WordTrace]
  refine ⟨4219611101245374066613715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 45009185079950656710546293 4219611101245374066613715)
  ·
    refine ⟨6329416651868061099920573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4219611101245374066613715 6329416651868061099920573)
    ·
      refine ⟨2373531244450522912470215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6329416651868061099920573 2373531244450522912470215)
      ·
        refine ⟨3560296866675784368705323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2373531244450522912470215 3560296866675784368705323)
        ·
          refine ⟨5340445300013676553057985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3560296866675784368705323 5340445300013676553057985)
          ·
            refine ⟨4005333975010257414793489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5340445300013676553057985 4005333975010257414793489)
            ·
              refine ⟨3004000481257693061095117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4005333975010257414793489 3004000481257693061095117)
              ·
                refine ⟨1126500180471634897910669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3004000481257693061095117 1126500180471634897910669)
                ·
                  refine ⟨422437567676863086716501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1126500180471634897910669 422437567676863086716501)
                  ·
                    rfl

theorem cell21_1851062_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 2, 2, 3, 3].length) (baseStart_1851062 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1851062 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1851062 prefixEnd_1851062 := by exact prefixLift 1851062
  have htrace : WordTrace (prefixWord ++ tailWord_1851062) baseStart_1851062 baseEnd_1851062 := by
    simpa [prefixWord, tailWord_1851062, baseEnd_1851062] using wordTrace_append hprefix tailTrace_1851062
  have hstable : (prefixWord ++ tailWord_1851062).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1851062).length < 2 ^ (prefixWord ++ tailWord_1851062).sum := by decide
  have hdescent : baseEnd_1851062 < baseStart_1851062 := by decide
  rcases family_descends (prefixWord ++ tailWord_1851062) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1851194 : List Nat := [3, 1, 1, 1, 5, 2, 2, 2, 4]
def baseStart_1851194 : Nat := 118140960795 + 1851194 * 2 ^ 59
def prefixEnd_1851194 : Nat := 4983230072969 + 3 ^ 40 * 1851194 * 2
def baseEnd_1851194 : Nat := 422467691875260190516231

theorem tailTrace_1851194 : CollatzResearch.WordTrace tailWord_1851194 prefixEnd_1851194 422467691875260190516231 := by
  unfold tailWord_1851194
  simp only [CollatzResearch.WordTrace]
  refine ⟨16879648013861942902406159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 45012394703631847739749757 16879648013861942902406159)
  ·
    refine ⟨25319472020792914353609239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16879648013861942902406159 25319472020792914353609239)
    ·
      refine ⟨37979208031189371530413859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25319472020792914353609239 37979208031189371530413859)
      ·
        refine ⟨56968812046784057295620789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37979208031189371530413859 56968812046784057295620789)
        ·
          refine ⟨5340826129386005371464449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 56968812046784057295620789 5340826129386005371464449)
          ·
            refine ⟨4005619597039504028598337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5340826129386005371464449 4005619597039504028598337)
            ·
              refine ⟨3004214697779628021448753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4005619597039504028598337 3004214697779628021448753)
              ·
                refine ⟨2253161023334721016086565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3004214697779628021448753 2253161023334721016086565)
                ·
                  refine ⟨422467691875260190516231, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2253161023334721016086565 422467691875260190516231)
                  ·
                    rfl

theorem cell21_1851194_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 2, 2, 2, 4].length) (baseStart_1851194 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1851194 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1851194 prefixEnd_1851194 := by exact prefixLift 1851194
  have htrace : WordTrace (prefixWord ++ tailWord_1851194) baseStart_1851194 baseEnd_1851194 := by
    simpa [prefixWord, tailWord_1851194, baseEnd_1851194] using wordTrace_append hprefix tailTrace_1851194
  have hstable : (prefixWord ++ tailWord_1851194).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1851194).length < 2 ^ (prefixWord ++ tailWord_1851194).sum := by decide
  have hdescent : baseEnd_1851194 < baseStart_1851194 := by decide
  rcases family_descends (prefixWord ++ tailWord_1851194) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1851197 : List Nat := [1, 4, 1, 4, 1, 1, 4, 2, 3]
def baseStart_1851197 : Nat := 118140960795 + 1851197 * 2 ^ 59
def prefixEnd_1851197 : Nat := 4983230072969 + 3 ^ 40 * 1851197 * 2
def baseEnd_1851197 : Nat := 422468376516132851966225

theorem tailTrace_1851197 : CollatzResearch.WordTrace tailWord_1851197 prefixEnd_1851197 422468376516132851966225 := by
  unfold tailWord_1851197
  simp only [CollatzResearch.WordTrace]
  refine ⟨67518701474436903121983845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45012467649624602081322563 67518701474436903121983845)
  ·
    refine ⟨12659756526456919335371971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 67518701474436903121983845 12659756526456919335371971)
    ·
      refine ⟨18989634789685379003057957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12659756526456919335371971 18989634789685379003057957)
      ·
        refine ⟨3560556523066008563073367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 18989634789685379003057957 3560556523066008563073367)
        ·
          refine ⟨5340834784599012844610051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3560556523066008563073367 5340834784599012844610051)
          ·
            refine ⟨8011252176898519266915077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5340834784599012844610051 8011252176898519266915077)
            ·
              refine ⟨1502109783168472362546577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8011252176898519266915077 1502109783168472362546577)
              ·
                refine ⟨1126582337376354271909933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1502109783168472362546577 1126582337376354271909933)
                ·
                  refine ⟨422468376516132851966225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1126582337376354271909933 422468376516132851966225)
                  ·
                    rfl

theorem cell21_1851197_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 1, 4, 2, 3].length) (baseStart_1851197 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1851197 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1851197 prefixEnd_1851197 := by exact prefixLift 1851197
  have htrace : WordTrace (prefixWord ++ tailWord_1851197) baseStart_1851197 baseEnd_1851197 := by
    simpa [prefixWord, tailWord_1851197, baseEnd_1851197] using wordTrace_append hprefix tailTrace_1851197
  have hstable : (prefixWord ++ tailWord_1851197).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1851197).length < 2 ^ (prefixWord ++ tailWord_1851197).sum := by decide
  have hdescent : baseEnd_1851197 < baseStart_1851197 := by decide
  rcases family_descends (prefixWord ++ tailWord_1851197) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1851208 : List Nat := [2, 1, 3, 1, 1, 6, 1, 6]
def baseStart_1851208 : Nat := 118140960795 + 1851208 * 2 ^ 59
def prefixEnd_1851208 : Nat := 4983230072969 + 3 ^ 40 * 1851208 * 2
def baseEnd_1851208 : Nat := 140823628955333092427623

theorem tailTrace_1851208 : CollatzResearch.WordTrace tailWord_1851208 prefixEnd_1851208 140823628955333092427623 := by
  unfold tailWord_1851208
  simp only [CollatzResearch.WordTrace]
  refine ⟨33759551338698526000317139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45012735118264701333756185 33759551338698526000317139)
  ·
    refine ⟨50639327008047789000475709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33759551338698526000317139 50639327008047789000475709)
    ·
      refine ⟨18989747628017920875178391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 50639327008047789000475709 18989747628017920875178391)
      ·
        refine ⟨28484621442026881312767587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18989747628017920875178391 28484621442026881312767587)
        ·
          refine ⟨42726932163040321969151381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28484621442026881312767587 42726932163040321969151381)
          ·
            refine ⟨2002824945142515092303971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 42726932163040321969151381 2002824945142515092303971)
            ·
              refine ⟨3004237417713772638455957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2002824945142515092303971 3004237417713772638455957)
              ·
                refine ⟨140823628955333092427623, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3004237417713772638455957 140823628955333092427623)
                ·
                  rfl

theorem cell21_1851208_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 6, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 6, 1, 6].length) (baseStart_1851208 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1851208 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1851208 prefixEnd_1851208 := by exact prefixLift 1851208
  have htrace : WordTrace (prefixWord ++ tailWord_1851208) baseStart_1851208 baseEnd_1851208 := by
    simpa [prefixWord, tailWord_1851208, baseEnd_1851208] using wordTrace_append hprefix tailTrace_1851208
  have hstable : (prefixWord ++ tailWord_1851208).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1851208).length < 2 ^ (prefixWord ++ tailWord_1851208).sum := by decide
  have hdescent : baseEnd_1851208 < baseStart_1851208 := by decide
  rcases family_descends (prefixWord ++ tailWord_1851208) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1851253 : List Nat := [1, 3, 4, 1, 1, 1, 3, 1, 6]
def baseStart_1851253 : Nat := 118140960795 + 1851253 * 2 ^ 59
def prefixEnd_1851253 : Nat := 4983230072969 + 3 ^ 40 * 1851253 * 2
def baseEnd_1851253 : Nat := 422481156479089199032777

theorem tailTrace_1851253 : CollatzResearch.WordTrace tailWord_1851253 prefixEnd_1851253 422481156479089199032777 := by
  unfold tailWord_1851253
  simp only [CollatzResearch.WordTrace]
  refine ⟨67520743962234024686022413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45013829308156016457348275 67520743962234024686022413)
  ·
    refine ⟨25320278985837759257258405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 67520743962234024686022413 25320278985837759257258405)
    ·
      refine ⟨4747552309844579860735951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 25320278985837759257258405 4747552309844579860735951)
      ·
        refine ⟨7121328464766869791103927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4747552309844579860735951 7121328464766869791103927)
        ·
          refine ⟨10681992697150304686655891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7121328464766869791103927 10681992697150304686655891)
          ·
            refine ⟨16022989045725457029983837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10681992697150304686655891 16022989045725457029983837)
            ·
              refine ⟨6008620892147046386243939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16022989045725457029983837 6008620892147046386243939)
              ·
                refine ⟨9012931338220569579365909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6008620892147046386243939 9012931338220569579365909)
                ·
                  refine ⟨422481156479089199032777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9012931338220569579365909 422481156479089199032777)
                  ·
                    rfl

theorem cell21_1851253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 3, 1, 6].length) (baseStart_1851253 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1851253 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1851253 prefixEnd_1851253 := by exact prefixLift 1851253
  have htrace : WordTrace (prefixWord ++ tailWord_1851253) baseStart_1851253 baseEnd_1851253 := by
    simpa [prefixWord, tailWord_1851253, baseEnd_1851253] using wordTrace_append hprefix tailTrace_1851253
  have hstable : (prefixWord ++ tailWord_1851253).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1851253).length < 2 ^ (prefixWord ++ tailWord_1851253).sum := by decide
  have hdescent : baseEnd_1851253 < baseStart_1851253 := by decide
  rcases family_descends (prefixWord ++ tailWord_1851253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1851284 : List Nat := [2, 4, 2, 1, 1, 3, 1, 7]
def baseStart_1851284 : Nat := 118140960795 + 1851284 * 2 ^ 59
def prefixEnd_1851284 : Nat := 4983230072969 + 3 ^ 40 * 1851284 * 2
def baseEnd_1851284 : Nat := 140829410367146678005349

theorem tailTrace_1851284 : CollatzResearch.WordTrace tailWord_1851284 prefixEnd_1851284 140829410367146678005349 := by
  unfold tailWord_1851284
  simp only [CollatzResearch.WordTrace]
  refine ⟨33760937312560858490200453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45014583083414477986933937 33760937312560858490200453)
  ·
    refine ⟨6330175746105160966912585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 33760937312560858490200453 6330175746105160966912585)
    ·
      refine ⟨4747631809578870725184439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6330175746105160966912585 4747631809578870725184439)
      ·
        refine ⟨7121447714368306087776659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4747631809578870725184439 7121447714368306087776659)
        ·
          refine ⟨10682171571552459131664989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7121447714368306087776659 10682171571552459131664989)
          ·
            refine ⟨4005814339332172174374371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10682171571552459131664989 4005814339332172174374371)
            ·
              refine ⟨6008721508998258261561557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4005814339332172174374371 6008721508998258261561557)
              ·
                refine ⟨140829410367146678005349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6008721508998258261561557 140829410367146678005349)
                ·
                  rfl

theorem cell21_1851284_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 3, 1, 7].length) (baseStart_1851284 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1851284 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1851284 prefixEnd_1851284 := by exact prefixLift 1851284
  have htrace : WordTrace (prefixWord ++ tailWord_1851284) baseStart_1851284 baseEnd_1851284 := by
    simpa [prefixWord, tailWord_1851284, baseEnd_1851284] using wordTrace_append hprefix tailTrace_1851284
  have hstable : (prefixWord ++ tailWord_1851284).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1851284).length < 2 ^ (prefixWord ++ tailWord_1851284).sum := by decide
  have hdescent : baseEnd_1851284 < baseStart_1851284 := by decide
  rcases family_descends (prefixWord ++ tailWord_1851284) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1851377 : List Nat := [1, 2, 2, 2, 6, 1, 1, 6]
def baseStart_1851377 : Nat := 118140960795 + 1851377 * 2 ^ 59
def prefixEnd_1851377 : Nat := 4983230072969 + 3 ^ 40 * 1851377 * 2
def baseEnd_1851377 : Nat := 140836484989497512988619

theorem tailTrace_1851377 : CollatzResearch.WordTrace tailWord_1851377 prefixEnd_1851377 140836484989497512988619 := by
  unfold tailWord_1851377
  simp only [CollatzResearch.WordTrace]
  refine ⟨67525266613784793863536385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45016844409189862575690923 67525266613784793863536385)
  ·
    refine ⟨50643949960338595397652289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67525266613784793863536385 50643949960338595397652289)
    ·
      refine ⟨37982962470253946548239217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50643949960338595397652289 37982962470253946548239217)
      ·
        refine ⟨28487221852690459911179413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37982962470253946548239217 28487221852690459911179413)
        ·
          refine ⟨1335338524344865308336535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 28487221852690459911179413 1335338524344865308336535)
          ·
            refine ⟨2003007786517297962504803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1335338524344865308336535 2003007786517297962504803)
            ·
              refine ⟨3004511679775946943757205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2003007786517297962504803 3004511679775946943757205)
              ·
                refine ⟨140836484989497512988619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3004511679775946943757205 140836484989497512988619)
                ·
                  rfl

theorem cell21_1851377_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 6, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 6, 1, 1, 6].length) (baseStart_1851377 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1851377 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1851377 prefixEnd_1851377 := by exact prefixLift 1851377
  have htrace : WordTrace (prefixWord ++ tailWord_1851377) baseStart_1851377 baseEnd_1851377 := by
    simpa [prefixWord, tailWord_1851377, baseEnd_1851377] using wordTrace_append hprefix tailTrace_1851377
  have hstable : (prefixWord ++ tailWord_1851377).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1851377).length < 2 ^ (prefixWord ++ tailWord_1851377).sum := by decide
  have hdescent : baseEnd_1851377 < baseStart_1851377 := by decide
  rcases family_descends (prefixWord ++ tailWord_1851377) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1851495 : List Nat := [1, 1, 5, 1, 1, 2, 4, 6]
def baseStart_1851495 : Nat := 118140960795 + 1851495 * 2 ^ 59
def prefixEnd_1851495 : Nat := 4983230072969 + 3 ^ 40 * 1851495 * 2
def baseEnd_1851495 : Nat := 140845461392050185332983

theorem tailTrace_1851495 : CollatzResearch.WordTrace tailWord_1851495 prefixEnd_1851495 140845461392050185332983 := by
  unfold tailWord_1851495
  simp only [CollatzResearch.WordTrace]
  refine ⟨67529570427357300016331939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45019713618238200010887959 67529570427357300016331939)
  ·
    refine ⟨101294355641035950024497909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67529570427357300016331939 101294355641035950024497909)
    ·
      refine ⟨9496345841347120314796679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 101294355641035950024497909 9496345841347120314796679)
      ·
        refine ⟨14244518762020680472195019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9496345841347120314796679 14244518762020680472195019)
        ·
          refine ⟨21366778143031020708292529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14244518762020680472195019 21366778143031020708292529)
          ·
            refine ⟨16025083607273265531219397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21366778143031020708292529 16025083607273265531219397)
            ·
              refine ⟨3004703176363737287103637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16025083607273265531219397 3004703176363737287103637)
              ·
                refine ⟨140845461392050185332983, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3004703176363737287103637 140845461392050185332983)
                ·
                  rfl

theorem cell21_1851495_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 4, 6].length) (baseStart_1851495 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1851495 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1851495 prefixEnd_1851495 := by exact prefixLift 1851495
  have htrace : WordTrace (prefixWord ++ tailWord_1851495) baseStart_1851495 baseEnd_1851495 := by
    simpa [prefixWord, tailWord_1851495, baseEnd_1851495] using wordTrace_append hprefix tailTrace_1851495
  have hstable : (prefixWord ++ tailWord_1851495).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1851495).length < 2 ^ (prefixWord ++ tailWord_1851495).sum := by decide
  have hdescent : baseEnd_1851495 < baseStart_1851495 := by decide
  rcases family_descends (prefixWord ++ tailWord_1851495) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1851498 : List Nat := [3, 1, 3, 2, 3, 1, 1, 3, 4]
def baseStart_1851498 : Nat := 118140960795 + 1851498 * 2 ^ 59
def prefixEnd_1851498 : Nat := 4983230072969 + 3 ^ 40 * 1851498 * 2
def baseEnd_1851498 : Nat := 422537068817023217448943

theorem tailTrace_1851498 : CollatzResearch.WordTrace tailWord_1851498 prefixEnd_1851498 422537068817023217448943 := by
  unfold tailWord_1851498
  simp only [CollatzResearch.WordTrace]
  refine ⟨16882419961586607882172787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 45019786564230954352460765 16882419961586607882172787)
  ·
    refine ⟨25323629942379911823259181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16882419961586607882172787 25323629942379911823259181)
    ·
      refine ⟨9496361228392466933722193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25323629942379911823259181 9496361228392466933722193)
      ·
        refine ⟨7122270921294350200291645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9496361228392466933722193 7122270921294350200291645)
        ·
          refine ⟨2670851595485381325109367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7122270921294350200291645 2670851595485381325109367)
          ·
            refine ⟨4006277393228071987664051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2670851595485381325109367 4006277393228071987664051)
            ·
              refine ⟨6009416089842107981496077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4006277393228071987664051 6009416089842107981496077)
              ·
                refine ⟨2253531033690790493061029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6009416089842107981496077 2253531033690790493061029)
                ·
                  refine ⟨422537068817023217448943, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2253531033690790493061029 422537068817023217448943)
                  ·
                    rfl

theorem cell21_1851498_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 3, 1, 1, 3, 4].length) (baseStart_1851498 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1851498 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1851498 prefixEnd_1851498 := by exact prefixLift 1851498
  have htrace : WordTrace (prefixWord ++ tailWord_1851498) baseStart_1851498 baseEnd_1851498 := by
    simpa [prefixWord, tailWord_1851498, baseEnd_1851498] using wordTrace_append hprefix tailTrace_1851498
  have hstable : (prefixWord ++ tailWord_1851498).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1851498).length < 2 ^ (prefixWord ++ tailWord_1851498).sum := by decide
  have hdescent : baseEnd_1851498 < baseStart_1851498 := by decide
  rcases family_descends (prefixWord ++ tailWord_1851498) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1851602 : List Nat := [3, 2, 2, 2, 1, 2, 1, 3, 5]
def baseStart_1851602 : Nat := 118140960795 + 1851602 * 2 ^ 59
def prefixEnd_1851602 : Nat := 4983230072969 + 3 ^ 40 * 1851602 * 2
def baseEnd_1851602 : Nat := 422560803033942147715397

theorem tailTrace_1851602 : CollatzResearch.WordTrace tailWord_1851602 prefixEnd_1851602 422560803033942147715397 := by
  unfold tailWord_1851602
  simp only [CollatzResearch.WordTrace]
  refine ⟨16883368259492414322619265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 45022315358646438193651373 16883368259492414322619265)
  ·
    refine ⟨12662526194619310741964449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16883368259492414322619265 12662526194619310741964449)
    ·
      refine ⟨9496894645964483056473337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12662526194619310741964449 9496894645964483056473337)
      ·
        refine ⟨7122670984473362292355003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9496894645964483056473337 7122670984473362292355003)
        ·
          refine ⟨10684006476710043438532505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7122670984473362292355003 10684006476710043438532505)
          ·
            refine ⟨8013004857532532578899379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10684006476710043438532505 8013004857532532578899379)
            ·
              refine ⟨12019507286298798868349069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8013004857532532578899379 12019507286298798868349069)
              ·
                refine ⟨4507315232362049575630901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12019507286298798868349069 4507315232362049575630901)
                ·
                  refine ⟨422560803033942147715397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4507315232362049575630901 422560803033942147715397)
                  ·
                    rfl

theorem cell21_1851602_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 2, 1, 3, 5].length) (baseStart_1851602 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1851602 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1851602 prefixEnd_1851602 := by exact prefixLift 1851602
  have htrace : WordTrace (prefixWord ++ tailWord_1851602) baseStart_1851602 baseEnd_1851602 := by
    simpa [prefixWord, tailWord_1851602, baseEnd_1851602] using wordTrace_append hprefix tailTrace_1851602
  have hstable : (prefixWord ++ tailWord_1851602).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1851602).length < 2 ^ (prefixWord ++ tailWord_1851602).sum := by decide
  have hdescent : baseEnd_1851602 < baseStart_1851602 := by decide
  rcases family_descends (prefixWord ++ tailWord_1851602) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1851706 : List Nat := [3, 1, 1, 1, 4, 11]
def baseStart_1851706 : Nat := 118140960795 + 1851706 * 2 ^ 59
def prefixEnd_1851706 : Nat := 4983230072969 + 3 ^ 40 * 1851706 * 2
def baseEnd_1851706 : Nat := 15651279157439299184513

theorem tailTrace_1851706 : CollatzResearch.WordTrace tailWord_1851706 prefixEnd_1851706 15651279157439299184513 := by
  unfold tailWord_1851706
  simp only [CollatzResearch.WordTrace]
  refine ⟨16884316557398220763065743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 45024844153061922034841981 16884316557398220763065743)
  ·
    refine ⟨25326474836097331144598615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16884316557398220763065743 25326474836097331144598615)
    ·
      refine ⟨37989712254145996716897923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25326474836097331144598615 37989712254145996716897923)
      ·
        refine ⟨56984568381218995075346885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37989712254145996716897923 56984568381218995075346885)
        ·
          refine ⟨10684606571478561576627541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 56984568381218995075346885 10684606571478561576627541)
          ·
            refine ⟨15651279157439299184513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 10684606571478561576627541 15651279157439299184513)
            ·
              rfl

theorem cell21_1851706_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 11].length) (baseStart_1851706 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1851706 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1851706 prefixEnd_1851706 := by exact prefixLift 1851706
  have htrace : WordTrace (prefixWord ++ tailWord_1851706) baseStart_1851706 baseEnd_1851706 := by
    simpa [prefixWord, tailWord_1851706, baseEnd_1851706] using wordTrace_append hprefix tailTrace_1851706
  have hstable : (prefixWord ++ tailWord_1851706).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1851706).length < 2 ^ (prefixWord ++ tailWord_1851706).sum := by decide
  have hdescent : baseEnd_1851706 < baseStart_1851706 := by decide
  rcases family_descends (prefixWord ++ tailWord_1851706) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1851799 : List Nat := [1, 1, 3, 3, 1, 1, 6, 5]
def baseStart_1851799 : Nat := 118140960795 + 1851799 * 2 ^ 59
def prefixEnd_1851799 : Nat := 4983230072969 + 3 ^ 40 * 1851799 * 2
def baseEnd_1851799 : Nat := 140868587039304527643887

theorem tailTrace_1851799 : CollatzResearch.WordTrace tailWord_1851799 prefixEnd_1851799 140868587039304527643887 := by
  unfold tailWord_1851799
  simp only [CollatzResearch.WordTrace]
  refine ⟨67540658218255959935398451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45027105478837306623598967 67540658218255959935398451)
  ·
    refine ⟨101310987327383939903097677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67540658218255959935398451 101310987327383939903097677)
    ·
      refine ⟨37991620247768977463661629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 101310987327383939903097677 37991620247768977463661629)
      ·
        refine ⟨14246857592913366548873111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 37991620247768977463661629 14246857592913366548873111)
        ·
          refine ⟨21370286389370049823309667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14246857592913366548873111 21370286389370049823309667)
          ·
            refine ⟨32055429584055074734964501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21370286389370049823309667 32055429584055074734964501)
            ·
              refine ⟨1502598261752581628201461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 32055429584055074734964501 1502598261752581628201461)
              ·
                refine ⟨140868587039304527643887, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1502598261752581628201461 140868587039304527643887)
                ·
                  rfl

theorem cell21_1851799_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 6, 5].length) (baseStart_1851799 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1851799 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1851799 prefixEnd_1851799 := by exact prefixLift 1851799
  have htrace : WordTrace (prefixWord ++ tailWord_1851799) baseStart_1851799 baseEnd_1851799 := by
    simpa [prefixWord, tailWord_1851799, baseEnd_1851799] using wordTrace_append hprefix tailTrace_1851799
  have hstable : (prefixWord ++ tailWord_1851799).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1851799).length < 2 ^ (prefixWord ++ tailWord_1851799).sum := by decide
  have hdescent : baseEnd_1851799 < baseStart_1851799 := by decide
  rcases family_descends (prefixWord ++ tailWord_1851799) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1851805 : List Nat := [1, 4, 2, 1, 5, 1, 1, 3, 3]
def baseStart_1851805 : Nat := 118140960795 + 1851805 * 2 ^ 59
def prefixEnd_1851805 : Nat := 4983230072969 + 3 ^ 40 * 1851805 * 2
def baseEnd_1851805 : Nat := 422607130399658905831649

theorem tailTrace_1851805 : CollatzResearch.WordTrace tailWord_1851805 prefixEnd_1851805 422607130399658905831649 := by
  unfold tailWord_1851805
  simp only [CollatzResearch.WordTrace]
  refine ⟨67540877056234222960116869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45027251370822815306744579 67540877056234222960116869)
  ·
    refine ⟨12663914448043916805021913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 67540877056234222960116869 12663914448043916805021913)
    ·
      refine ⟨9497935836032937603766435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12663914448043916805021913 9497935836032937603766435)
      ·
        refine ⟨14246903754049406405649653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9497935836032937603766435 14246903754049406405649653)
        ·
          refine ⟨1335647226942131850529655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 14246903754049406405649653 1335647226942131850529655)
          ·
            refine ⟨2003470840413197775794483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1335647226942131850529655 2003470840413197775794483)
            ·
              refine ⟨3005206260619796663691725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2003470840413197775794483 3005206260619796663691725)
              ·
                refine ⟨1126952347732423748884397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3005206260619796663691725 1126952347732423748884397)
                ·
                  refine ⟨422607130399658905831649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1126952347732423748884397 422607130399658905831649)
                  ·
                    rfl

theorem cell21_1851805_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 5, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 5, 1, 1, 3, 3].length) (baseStart_1851805 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1851805 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1851805 prefixEnd_1851805 := by exact prefixLift 1851805
  have htrace : WordTrace (prefixWord ++ tailWord_1851805) baseStart_1851805 baseEnd_1851805 := by
    simpa [prefixWord, tailWord_1851805, baseEnd_1851805] using wordTrace_append hprefix tailTrace_1851805
  have hstable : (prefixWord ++ tailWord_1851805).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1851805).length < 2 ^ (prefixWord ++ tailWord_1851805).sum := by decide
  have hdescent : baseEnd_1851805 < baseStart_1851805 := by decide
  rcases family_descends (prefixWord ++ tailWord_1851805) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1851816 : List Nat := [2, 1, 6, 1, 1, 3, 7]
def baseStart_1851816 : Nat := 118140960795 + 1851816 * 2 ^ 59
def prefixEnd_1851816 : Nat := 4983230072969 + 3 ^ 40 * 1851816 * 2
def baseEnd_1851816 : Nat := 46956626749947259016477

theorem tailTrace_1851816 : CollatzResearch.WordTrace tailWord_1851816 prefixEnd_1851816 46956626749947259016477 := by
  unfold tailWord_1851816
  simp only [CollatzResearch.WordTrace]
  refine ⟨33770639129597185919383651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45027518839462914559178201 33770639129597185919383651)
  ·
    refine ⟨50655958694395778879075477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33770639129597185919383651 50655958694395778879075477)
    ·
      refine ⟨2374498063799802134956663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 50655958694395778879075477 2374498063799802134956663)
      ·
        refine ⟨3561747095699703202434995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2374498063799802134956663 3561747095699703202434995)
        ·
          refine ⟨5342620643549554803652493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3561747095699703202434995 5342620643549554803652493)
          ·
            refine ⟨2003482741331083051369685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5342620643549554803652493 2003482741331083051369685)
            ·
              refine ⟨46956626749947259016477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 2003482741331083051369685 46956626749947259016477)
              ·
                rfl

theorem cell21_1851816_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 3, 7].length) (baseStart_1851816 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1851816 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1851816 prefixEnd_1851816 := by exact prefixLift 1851816
  have htrace : WordTrace (prefixWord ++ tailWord_1851816) baseStart_1851816 baseEnd_1851816 := by
    simpa [prefixWord, tailWord_1851816, baseEnd_1851816] using wordTrace_append hprefix tailTrace_1851816
  have hstable : (prefixWord ++ tailWord_1851816).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1851816).length < 2 ^ (prefixWord ++ tailWord_1851816).sum := by decide
  have hdescent : baseEnd_1851816 < baseStart_1851816 := by decide
  rcases family_descends (prefixWord ++ tailWord_1851816) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1851875 : List Nat := [1, 1, 1, 6, 4, 8]
def baseStart_1851875 : Nat := 118140960795 + 1851875 * 2 ^ 59
def prefixEnd_1851875 : Nat := 4983230072969 + 3 ^ 40 * 1851875 * 2
def baseEnd_1851875 : Nat := 15652707605679790357957

theorem tailTrace_1851875 : CollatzResearch.WordTrace tailWord_1851875 prefixEnd_1851875 15652707605679790357957 := by
  unfold tailWord_1851875
  simp only [CollatzResearch.WordTrace]
  refine ⟨67543430165980624915165079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45028953443987083276776719 67543430165980624915165079)
  ·
    refine ⟨101315145248970937372747619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67543430165980624915165079 101315145248970937372747619)
    ·
      refine ⟨151972717873456406059121429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101315145248970937372747619 151972717873456406059121429)
      ·
        refine ⟨7123721150318269034021317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 151972717873456406059121429 7123721150318269034021317)
        ·
          refine ⟨1335697715684675443878997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7123721150318269034021317 1335697715684675443878997)
          ·
            refine ⟨15652707605679790357957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 1335697715684675443878997 15652707605679790357957)
            ·
              rfl

theorem cell21_1851875_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 4, 8].length) (baseStart_1851875 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1851875 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1851875 prefixEnd_1851875 := by exact prefixLift 1851875
  have htrace : WordTrace (prefixWord ++ tailWord_1851875) baseStart_1851875 baseEnd_1851875 := by
    simpa [prefixWord, tailWord_1851875, baseEnd_1851875] using wordTrace_append hprefix tailTrace_1851875
  have hstable : (prefixWord ++ tailWord_1851875).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1851875).length < 2 ^ (prefixWord ++ tailWord_1851875).sum := by decide
  have hdescent : baseEnd_1851875 < baseStart_1851875 := by decide
  rcases family_descends (prefixWord ++ tailWord_1851875) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1851889 : List Nat := [1, 2, 2, 2, 3, 1, 2, 3, 5]
def baseStart_1851889 : Nat := 118140960795 + 1851889 * 2 ^ 59
def prefixEnd_1851889 : Nat := 4983230072969 + 3 ^ 40 * 1851889 * 2
def baseEnd_1851889 : Nat := 422626300344093426431477

theorem tailTrace_1851889 : CollatzResearch.WordTrace tailWord_1851889 prefixEnd_1851889 422626300344093426431477 := by
  unfold tailWord_1851889
  simp only [CollatzResearch.WordTrace]
  refine ⟨67543940787929905306174721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45029293858619936870783147 67543940787929905306174721)
  ·
    refine ⟨50657955590947428979631041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67543940787929905306174721 50657955590947428979631041)
    ·
      refine ⟨37993466693210571734723281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50657955590947428979631041 37993466693210571734723281)
      ·
        refine ⟨28495100019907928801042461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37993466693210571734723281 28495100019907928801042461)
        ·
          refine ⟨10685662507465473300390923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28495100019907928801042461 10685662507465473300390923)
          ·
            refine ⟨16028493761198209950586385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10685662507465473300390923 16028493761198209950586385)
            ·
              refine ⟨12021370320898657462939789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16028493761198209950586385 12021370320898657462939789)
              ·
                refine ⟨4508013870336996548602421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12021370320898657462939789 4508013870336996548602421)
                ·
                  refine ⟨422626300344093426431477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4508013870336996548602421 422626300344093426431477)
                  ·
                    rfl

theorem cell21_1851889_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 2, 3, 5].length) (baseStart_1851889 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1851889 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1851889 prefixEnd_1851889 := by exact prefixLift 1851889
  have htrace : WordTrace (prefixWord ++ tailWord_1851889) baseStart_1851889 baseEnd_1851889 := by
    simpa [prefixWord, tailWord_1851889, baseEnd_1851889] using wordTrace_append hprefix tailTrace_1851889
  have hstable : (prefixWord ++ tailWord_1851889).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1851889).length < 2 ^ (prefixWord ++ tailWord_1851889).sum := by decide
  have hdescent : baseEnd_1851889 < baseStart_1851889 := by decide
  rcases family_descends (prefixWord ++ tailWord_1851889) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1851979 : List Nat := [1, 1, 1, 1, 3, 1, 5, 2, 6]
def baseStart_1851979 : Nat := 118140960795 + 1851979 * 2 ^ 59
def prefixEnd_1851979 : Nat := 4983230072969 + 3 ^ 40 * 1851979 * 2
def baseEnd_1851979 : Nat := 422646839570273269931293

theorem tailTrace_1851979 : CollatzResearch.WordTrace tailWord_1851979 prefixEnd_1851979 422646839570273269931293 := by
  unfold tailWord_1851979
  simp only [CollatzResearch.WordTrace]
  refine ⟨67547223357603850676950991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45031482238402567117967327 67547223357603850676950991)
  ·
    refine ⟨101320835036405776015426487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67547223357603850676950991 101320835036405776015426487)
    ·
      refine ⟨151981252554608664023139731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101320835036405776015426487 151981252554608664023139731)
      ·
        refine ⟨227971878831912996034709597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 151981252554608664023139731 227971878831912996034709597)
        ·
          refine ⟨85489454561967373513016099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 227971878831912996034709597 85489454561967373513016099)
          ·
            refine ⟨128234181842951060269524149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 85489454561967373513016099 128234181842951060269524149)
            ·
              refine ⟨12021954547776661900267889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 128234181842951060269524149 12021954547776661900267889)
              ·
                refine ⟨9016465910832496425200917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12021954547776661900267889 9016465910832496425200917)
                ·
                  refine ⟨422646839570273269931293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9016465910832496425200917 422646839570273269931293)
                  ·
                    rfl

theorem cell21_1851979_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 5, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 5, 2, 6].length) (baseStart_1851979 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1851979 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1851979 prefixEnd_1851979 := by exact prefixLift 1851979
  have htrace : WordTrace (prefixWord ++ tailWord_1851979) baseStart_1851979 baseEnd_1851979 := by
    simpa [prefixWord, tailWord_1851979, baseEnd_1851979] using wordTrace_append hprefix tailTrace_1851979
  have hstable : (prefixWord ++ tailWord_1851979).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1851979).length < 2 ^ (prefixWord ++ tailWord_1851979).sum := by decide
  have hdescent : baseEnd_1851979 < baseStart_1851979 := by decide
  rcases family_descends (prefixWord ++ tailWord_1851979) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1852013 : List Nat := [1, 5, 1, 1, 3, 2, 1, 3, 4]
def baseStart_1852013 : Nat := 118140960795 + 1852013 * 2 ^ 59
def prefixEnd_1852013 : Nat := 4983230072969 + 3 ^ 40 * 1852013 * 2
def baseEnd_1852013 : Nat := 422654598833496766364557

theorem tailTrace_1852013 : CollatzResearch.WordTrace tailWord_1852013 prefixEnd_1852013 422654598833496766364557 := by
  unfold tailWord_1852013
  simp only [CollatzResearch.WordTrace]
  refine ⟨67548463439480674483688693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45032308959653782989125795 67548463439480674483688693)
  ·
    refine ⟨6332668447451313232845815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 67548463439480674483688693 6332668447451313232845815)
    ·
      refine ⟨9499002671176969849268723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6332668447451313232845815 9499002671176969849268723)
      ·
        refine ⟨14248504006765454773903085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9499002671176969849268723 14248504006765454773903085)
        ·
          refine ⟨5343189002537045540213657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14248504006765454773903085 5343189002537045540213657)
          ·
            refine ⟨4007391751902784155160243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5343189002537045540213657 4007391751902784155160243)
            ·
              refine ⟨6011087627854176232740365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4007391751902784155160243 6011087627854176232740365)
              ·
                refine ⟨2254157860445316087277637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6011087627854176232740365 2254157860445316087277637)
                ·
                  refine ⟨422654598833496766364557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2254157860445316087277637 422654598833496766364557)
                  ·
                    rfl

theorem cell21_1852013_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 2, 1, 3, 4].length) (baseStart_1852013 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1852013 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1852013 prefixEnd_1852013 := by exact prefixLift 1852013
  have htrace : WordTrace (prefixWord ++ tailWord_1852013) baseStart_1852013 baseEnd_1852013 := by
    simpa [prefixWord, tailWord_1852013, baseEnd_1852013] using wordTrace_append hprefix tailTrace_1852013
  have hstable : (prefixWord ++ tailWord_1852013).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1852013).length < 2 ^ (prefixWord ++ tailWord_1852013).sum := by decide
  have hdescent : baseEnd_1852013 < baseStart_1852013 := by decide
  rcases family_descends (prefixWord ++ tailWord_1852013) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1852210 : List Nat := [3, 2, 1, 1, 3, 1, 2, 5, 3]
def baseStart_1852210 : Nat := 118140960795 + 1852210 * 2 ^ 59
def prefixEnd_1852210 : Nat := 4983230072969 + 3 ^ 40 * 1852210 * 2
def baseEnd_1852210 : Nat := 422699556917468201580821

theorem tailTrace_1852210 : CollatzResearch.WordTrace tailWord_1852210 prefixEnd_1852210 422699556917468201580821 := by
  unfold tailWord_1852210
  simp only [CollatzResearch.WordTrace]
  refine ⟨16888912154941744282152521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 45037099079844651419073389 16888912154941744282152521)
  ·
    refine ⟨12666684116206308211614391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16888912154941744282152521 12666684116206308211614391)
    ·
      refine ⟨19000026174309462317421587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12666684116206308211614391 19000026174309462317421587)
      ·
        refine ⟨28500039261464193476132381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19000026174309462317421587 28500039261464193476132381)
        ·
          refine ⟨10687514723049072553549643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28500039261464193476132381 10687514723049072553549643)
          ·
            refine ⟨16031272084573608830324465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10687514723049072553549643 16031272084573608830324465)
            ·
              refine ⟨12023454063430206622743349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16031272084573608830324465 12023454063430206622743349)
              ·
                refine ⟨1127198818446581870882189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 12023454063430206622743349 1127198818446581870882189)
                ·
                  refine ⟨422699556917468201580821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1127198818446581870882189 422699556917468201580821)
                  ·
                    rfl

theorem cell21_1852210_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 2, 5, 3].length) (baseStart_1852210 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1852210 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1852210 prefixEnd_1852210 := by exact prefixLift 1852210
  have htrace : WordTrace (prefixWord ++ tailWord_1852210) baseStart_1852210 baseEnd_1852210 := by
    simpa [prefixWord, tailWord_1852210, baseEnd_1852210] using wordTrace_append hprefix tailTrace_1852210
  have hstable : (prefixWord ++ tailWord_1852210).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1852210).length < 2 ^ (prefixWord ++ tailWord_1852210).sum := by decide
  have hdescent : baseEnd_1852210 < baseStart_1852210 := by decide
  rcases family_descends (prefixWord ++ tailWord_1852210) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1852230 : List Nat := [6, 1, 1, 2, 3, 1, 1, 6]
def baseStart_1852230 : Nat := 118140960795 + 1852230 * 2 ^ 59
def prefixEnd_1852230 : Nat := 4983230072969 + 3 ^ 40 * 1852230 * 2
def baseEnd_1852230 : Nat := 140901373729984203749149

theorem tailTrace_1852230 : CollatzResearch.WordTrace tailWord_1852230 prefixEnd_1852230 140901373729984203749149 := by
  unfold tailWord_1852230
  simp only [CollatzResearch.WordTrace]
  refine ⟨2111136814990453767010567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 45037585386463013696225429 2111136814990453767010567)
  ·
    refine ⟨3166705222485680650515851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2111136814990453767010567 3166705222485680650515851)
    ·
      refine ⟨4750057833728520975773777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3166705222485680650515851 4750057833728520975773777)
      ·
        refine ⟨3562543375296390731830333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4750057833728520975773777 3562543375296390731830333)
        ·
          refine ⟨1335953765736146524436375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3562543375296390731830333 1335953765736146524436375)
          ·
            refine ⟨2003930648604219786654563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1335953765736146524436375 2003930648604219786654563)
            ·
              refine ⟨3005895972906329679981845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2003930648604219786654563 3005895972906329679981845)
              ·
                refine ⟨140901373729984203749149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3005895972906329679981845 140901373729984203749149)
                ·
                  rfl

theorem cell21_1852230_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 3, 1, 1, 6].length) (baseStart_1852230 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1852230 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1852230 prefixEnd_1852230 := by exact prefixLift 1852230
  have htrace : WordTrace (prefixWord ++ tailWord_1852230) baseStart_1852230 baseEnd_1852230 := by
    simpa [prefixWord, tailWord_1852230, baseEnd_1852230] using wordTrace_append hprefix tailTrace_1852230
  have hstable : (prefixWord ++ tailWord_1852230).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1852230).length < 2 ^ (prefixWord ++ tailWord_1852230).sum := by decide
  have hdescent : baseEnd_1852230 < baseStart_1852230 := by decide
  rcases family_descends (prefixWord ++ tailWord_1852230) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1852345 : List Nat := [1, 2, 1, 4, 2, 2, 3, 1, 5]
def baseStart_1852345 : Nat := 118140960795 + 1852345 * 2 ^ 59
def prefixEnd_1852345 : Nat := 4983230072969 + 3 ^ 40 * 1852345 * 2
def baseEnd_1852345 : Nat := 422730365756737966830545

theorem tailTrace_1852345 : CollatzResearch.WordTrace tailWord_1852345 prefixEnd_1852345 422730365756737966830545 := by
  unfold tailWord_1852345
  simp only [CollatzResearch.WordTrace]
  refine ⟨67560572474277895184774489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45040381649518596789849659 67560572474277895184774489)
  ·
    refine ⟨50670429355708421388580867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67560572474277895184774489 50670429355708421388580867)
    ·
      refine ⟨76005644033562632082871301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50670429355708421388580867 76005644033562632082871301)
      ·
        refine ⟨14251058256292993515538369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 76005644033562632082871301 14251058256292993515538369)
        ·
          refine ⟨10688293692219745136653777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14251058256292993515538369 10688293692219745136653777)
          ·
            refine ⟨8016220269164808852490333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10688293692219745136653777 8016220269164808852490333)
            ·
              refine ⟨3006082600936803319683875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8016220269164808852490333 3006082600936803319683875)
              ·
                refine ⟨4509123901405204979525813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3006082600936803319683875 4509123901405204979525813)
                ·
                  refine ⟨422730365756737966830545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4509123901405204979525813 422730365756737966830545)
                  ·
                    rfl

theorem cell21_1852345_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 2, 3, 1, 5].length) (baseStart_1852345 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1852345 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1852345 prefixEnd_1852345 := by exact prefixLift 1852345
  have htrace : WordTrace (prefixWord ++ tailWord_1852345) baseStart_1852345 baseEnd_1852345 := by
    simpa [prefixWord, tailWord_1852345, baseEnd_1852345] using wordTrace_append hprefix tailTrace_1852345
  have hstable : (prefixWord ++ tailWord_1852345).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1852345).length < 2 ^ (prefixWord ++ tailWord_1852345).sum := by decide
  have hdescent : baseEnd_1852345 < baseStart_1852345 := by decide
  rcases family_descends (prefixWord ++ tailWord_1852345) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1852452 : List Nat := [2, 3, 1, 4, 1, 2, 1, 1, 6]
def baseStart_1852452 : Nat := 118140960795 + 1852452 * 2 ^ 59
def prefixEnd_1852452 : Nat := 4983230072969 + 3 ^ 40 * 1852452 * 2
def baseEnd_1852452 : Nat := 422754784614529558546993

theorem tailTrace_1852452 : CollatzResearch.WordTrace tailWord_1852452 prefixEnd_1852452 422754784614529558546993 := by
  unfold tailWord_1852452
  simp only [CollatzResearch.WordTrace]
  refine ⟨33782237542445126229459805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45042983389926834972613073 33782237542445126229459805)
  ·
    refine ⟨12668339078416922336047427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 33782237542445126229459805 12668339078416922336047427)
    ·
      refine ⟨19002508617625383504071141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12668339078416922336047427 19002508617625383504071141)
      ·
        refine ⟨3562970365804759407013339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 19002508617625383504071141 3562970365804759407013339)
        ·
          refine ⟨5344455548707139110520009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3562970365804759407013339 5344455548707139110520009)
          ·
            refine ⟨4008341661530354332890007, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5344455548707139110520009 4008341661530354332890007)
            ·
              refine ⟨6012512492295531499335011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4008341661530354332890007 6012512492295531499335011)
              ·
                refine ⟨9018768738443297249002517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6012512492295531499335011 9018768738443297249002517)
                ·
                  refine ⟨422754784614529558546993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9018768738443297249002517 422754784614529558546993)
                  ·
                    rfl

theorem cell21_1852452_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 2, 1, 1, 6].length) (baseStart_1852452 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1852452 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1852452 prefixEnd_1852452 := by exact prefixLift 1852452
  have htrace : WordTrace (prefixWord ++ tailWord_1852452) baseStart_1852452 baseEnd_1852452 := by
    simpa [prefixWord, tailWord_1852452, baseEnd_1852452] using wordTrace_append hprefix tailTrace_1852452
  have hstable : (prefixWord ++ tailWord_1852452).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1852452).length < 2 ^ (prefixWord ++ tailWord_1852452).sum := by decide
  have hdescent : baseEnd_1852452 < baseStart_1852452 := by decide
  rcases family_descends (prefixWord ++ tailWord_1852452) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1852455 : List Nat := [1, 1, 7, 1, 1, 1, 2, 4, 3]
def baseStart_1852455 : Nat := 118140960795 + 1852455 * 2 ^ 59
def prefixEnd_1852455 : Nat := 4983230072969 + 3 ^ 40 * 1852455 * 2
def baseEnd_1852455 : Nat := 422755469255402219996987

theorem tailTrace_1852455 : CollatzResearch.WordTrace tailWord_1852455 prefixEnd_1852455 422755469255402219996987 := by
  unfold tailWord_1852455
  simp only [CollatzResearch.WordTrace]
  refine ⟨67564584503879383971278819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45043056335919589314185879 67564584503879383971278819)
  ·
    refine ⟨101346876755819075956918229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67564584503879383971278819 101346876755819075956918229)
    ·
      refine ⟨2375317423964509592740271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 101346876755819075956918229 2375317423964509592740271)
      ·
        refine ⟨3562976135946764389110407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2375317423964509592740271 3562976135946764389110407)
        ·
          refine ⟨5344464203920146583665611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3562976135946764389110407 5344464203920146583665611)
          ·
            refine ⟨8016696305880219875498417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5344464203920146583665611 8016696305880219875498417)
            ·
              refine ⟨6012522229410164906623813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8016696305880219875498417 6012522229410164906623813)
              ·
                refine ⟨1127347918014405919991965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6012522229410164906623813 1127347918014405919991965)
                ·
                  refine ⟨422755469255402219996987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1127347918014405919991965 422755469255402219996987)
                  ·
                    rfl

theorem cell21_1852455_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 1, 2, 4, 3].length) (baseStart_1852455 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1852455 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1852455 prefixEnd_1852455 := by exact prefixLift 1852455
  have htrace : WordTrace (prefixWord ++ tailWord_1852455) baseStart_1852455 baseEnd_1852455 := by
    simpa [prefixWord, tailWord_1852455, baseEnd_1852455] using wordTrace_append hprefix tailTrace_1852455
  have hstable : (prefixWord ++ tailWord_1852455).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1852455).length < 2 ^ (prefixWord ++ tailWord_1852455).sum := by decide
  have hdescent : baseEnd_1852455 < baseStart_1852455 := by decide
  rcases family_descends (prefixWord ++ tailWord_1852455) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1852480 : List Nat := [2, 1, 1, 2, 2, 3, 1, 4, 5]
def baseStart_1852480 : Nat := 118140960795 + 1852480 * 2 ^ 59
def prefixEnd_1852480 : Nat := 4983230072969 + 3 ^ 40 * 1852480 * 2
def baseEnd_1852480 : Nat := 422761174596007732080269

theorem tailTrace_1852480 : CollatzResearch.WordTrace tailWord_1852480 prefixEnd_1852480 422761174596007732080269 := by
  unfold tailWord_1852480
  simp only [CollatzResearch.WordTrace]
  refine ⟨33782748164394406620469447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45043664219192542160625929 33782748164394406620469447)
  ·
    refine ⟨50674122246591609930704171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33782748164394406620469447 50674122246591609930704171)
    ·
      refine ⟨76011183369887414896056257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50674122246591609930704171 76011183369887414896056257)
      ·
        refine ⟨57008387527415561172042193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 76011183369887414896056257 57008387527415561172042193)
        ·
          refine ⟨42756290645561670879031645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57008387527415561172042193 42756290645561670879031645)
          ·
            refine ⟨16033608992085626579636867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 42756290645561670879031645 16033608992085626579636867)
            ·
              refine ⟨24050413488128439869455301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16033608992085626579636867 24050413488128439869455301)
              ·
                refine ⟨4509452529024082475522869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 24050413488128439869455301 4509452529024082475522869)
                ·
                  refine ⟨422761174596007732080269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4509452529024082475522869 422761174596007732080269)
                  ·
                    rfl

theorem cell21_1852480_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 1, 4, 5].length) (baseStart_1852480 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1852480 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1852480 prefixEnd_1852480 := by exact prefixLift 1852480
  have htrace : WordTrace (prefixWord ++ tailWord_1852480) baseStart_1852480 baseEnd_1852480 := by
    simpa [prefixWord, tailWord_1852480, baseEnd_1852480] using wordTrace_append hprefix tailTrace_1852480
  have hstable : (prefixWord ++ tailWord_1852480).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1852480).length < 2 ^ (prefixWord ++ tailWord_1852480).sum := by decide
  have hdescent : baseEnd_1852480 < baseStart_1852480 := by decide
  rcases family_descends (prefixWord ++ tailWord_1852480) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1852511 : List Nat := [1, 1, 2, 3, 1, 1, 4, 4, 4]
def baseStart_1852511 : Nat := 118140960795 + 1852511 * 2 ^ 59
def prefixEnd_1852511 : Nat := 4983230072969 + 3 ^ 40 * 1852511 * 2
def baseEnd_1852511 : Nat := 422768249218358567063539

theorem tailTrace_1852511 : CollatzResearch.WordTrace tailWord_1852511 prefixEnd_1852511 422768249218358567063539 := by
  unfold tailWord_1852511
  simp only [CollatzResearch.WordTrace]
  refine ⟨67566626991676505535317387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45044417994451003690211591 67566626991676505535317387)
  ·
    refine ⟨101349940487514758302976081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67566626991676505535317387 101349940487514758302976081)
    ·
      refine ⟨76012455365636068727232061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 101349940487514758302976081 76012455365636068727232061)
      ·
        refine ⟨28504670762113525772712023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 76012455365636068727232061 28504670762113525772712023)
        ·
          refine ⟨42757006143170288659068035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28504670762113525772712023 42757006143170288659068035)
          ·
            refine ⟨64135509214755432988602053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42757006143170288659068035 64135509214755432988602053)
            ·
              refine ⟨12025407977766643685362885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 64135509214755432988602053 12025407977766643685362885)
              ·
                refine ⟨2254763995831245691005541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12025407977766643685362885 2254763995831245691005541)
                ·
                  refine ⟨422768249218358567063539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2254763995831245691005541 422768249218358567063539)
                  ·
                    rfl

theorem cell21_1852511_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 4, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 4, 4, 4].length) (baseStart_1852511 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1852511 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1852511 prefixEnd_1852511 := by exact prefixLift 1852511
  have htrace : WordTrace (prefixWord ++ tailWord_1852511) baseStart_1852511 baseEnd_1852511 := by
    simpa [prefixWord, tailWord_1852511, baseEnd_1852511] using wordTrace_append hprefix tailTrace_1852511
  have hstable : (prefixWord ++ tailWord_1852511).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1852511).length < 2 ^ (prefixWord ++ tailWord_1852511).sum := by decide
  have hdescent : baseEnd_1852511 < baseStart_1852511 := by decide
  rcases family_descends (prefixWord ++ tailWord_1852511) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1852514 : List Nat := [3, 3, 2, 2, 1, 1, 3, 1, 5]
def baseStart_1852514 : Nat := 118140960795 + 1852514 * 2 ^ 59
def prefixEnd_1852514 : Nat := 4983230072969 + 3 ^ 40 * 1852514 * 2
def baseEnd_1852514 : Nat := 422768933859231228513533

theorem tailTrace_1852514 : CollatzResearch.WordTrace tailWord_1852514 prefixEnd_1852514 422768933859231228513533 := by
  unfold tailWord_1852514
  simp only [CollatzResearch.WordTrace]
  refine ⟨16891684102666409261919149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 45044490940443758031784397 16891684102666409261919149)
  ·
    refine ⟨6334381538499903473219681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16891684102666409261919149 6334381538499903473219681)
    ·
      refine ⟨4750786153874927604914761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6334381538499903473219681 4750786153874927604914761)
      ·
        refine ⟨3563089615406195703686071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4750786153874927604914761 3563089615406195703686071)
        ·
          refine ⟨5344634423109293555529107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3563089615406195703686071 5344634423109293555529107)
          ·
            refine ⟨8016951634663940333293661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5344634423109293555529107 8016951634663940333293661)
            ·
              refine ⟨3006356862998977624985123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8016951634663940333293661 3006356862998977624985123)
              ·
                refine ⟨4509535294498466437477685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3006356862998977624985123 4509535294498466437477685)
                ·
                  refine ⟨422768933859231228513533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4509535294498466437477685 422768933859231228513533)
                  ·
                    rfl

theorem cell21_1852514_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 1, 3, 1, 5].length) (baseStart_1852514 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1852514 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1852514 prefixEnd_1852514 := by exact prefixLift 1852514
  have htrace : WordTrace (prefixWord ++ tailWord_1852514) baseStart_1852514 baseEnd_1852514 := by
    simpa [prefixWord, tailWord_1852514, baseEnd_1852514] using wordTrace_append hprefix tailTrace_1852514
  have hstable : (prefixWord ++ tailWord_1852514).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1852514).length < 2 ^ (prefixWord ++ tailWord_1852514).sum := by decide
  have hdescent : baseEnd_1852514 < baseStart_1852514 := by decide
  rcases family_descends (prefixWord ++ tailWord_1852514) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1852708 : List Nat := [2, 3, 1, 3, 1, 1, 2, 1, 7]
def baseStart_1852708 : Nat := 118140960795 + 1852708 * 2 ^ 59
def prefixEnd_1852708 : Nat := 4983230072969 + 3 ^ 40 * 1852708 * 2
def baseEnd_1852708 : Nat := 422813207302330002279803

theorem tailTrace_1852708 : CollatzResearch.WordTrace tailWord_1852708 prefixEnd_1852708 422813207302330002279803 := by
  unfold tailWord_1852708
  simp only [CollatzResearch.WordTrace]
  refine ⟨33786906085981404090119389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45049208114641872120159185 33786906085981404090119389)
  ·
    refine ⟨12670089782243026533794771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 33786906085981404090119389 12670089782243026533794771)
    ·
      refine ⟨19005134673364539800692157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12670089782243026533794771 19005134673364539800692157)
      ·
        refine ⟨7126925502511702425259559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19005134673364539800692157 7126925502511702425259559)
        ·
          refine ⟨10690388253767553637889339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7126925502511702425259559 10690388253767553637889339)
          ·
            refine ⟨16035582380651330456834009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10690388253767553637889339 16035582380651330456834009)
            ·
              refine ⟨12026686785488497842625507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16035582380651330456834009 12026686785488497842625507)
              ·
                refine ⟨18040030178232746763938261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12026686785488497842625507 18040030178232746763938261)
                ·
                  refine ⟨422813207302330002279803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 18040030178232746763938261 422813207302330002279803)
                  ·
                    rfl

theorem cell21_1852708_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 2, 1, 7].length) (baseStart_1852708 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1852708 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1852708 prefixEnd_1852708 := by exact prefixLift 1852708
  have htrace : WordTrace (prefixWord ++ tailWord_1852708) baseStart_1852708 baseEnd_1852708 := by
    simpa [prefixWord, tailWord_1852708, baseEnd_1852708] using wordTrace_append hprefix tailTrace_1852708
  have hstable : (prefixWord ++ tailWord_1852708).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1852708).length < 2 ^ (prefixWord ++ tailWord_1852708).sum := by decide
  have hdescent : baseEnd_1852708 < baseStart_1852708 := by decide
  rcases family_descends (prefixWord ++ tailWord_1852708) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1852984 : List Nat := [2, 1, 2, 1, 4, 3, 3, 1, 4]
def baseStart_1852984 : Nat := 118140960795 + 1852984 * 2 ^ 59
def prefixEnd_1852984 : Nat := 4983230072969 + 3 ^ 40 * 1852984 * 2
def baseEnd_1852984 : Nat := 422876194262614855679239

theorem tailTrace_1852984 : CollatzResearch.WordTrace tailWord_1852984 prefixEnd_1852984 422876194262614855679239 := by
  unfold tailWord_1852984
  simp only [CollatzResearch.WordTrace]
  refine ⟨33791939359481453658643003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45055919145975271544857337 33791939359481453658643003)
  ·
    refine ⟨50687909039222180487964505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33791939359481453658643003 50687909039222180487964505)
    ·
      refine ⟨38015931779416635365973379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50687909039222180487964505 38015931779416635365973379)
      ·
        refine ⟨57023897669124953048960069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38015931779416635365973379 57023897669124953048960069)
        ·
          refine ⟨10691980812960928696680013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 57023897669124953048960069 10691980812960928696680013)
          ·
            refine ⟨4009492804860348261255005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10691980812960928696680013 4009492804860348261255005)
            ·
              refine ⟨1503559801822630597970627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4009492804860348261255005 1503559801822630597970627)
              ·
                refine ⟨2255339702733945896955941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1503559801822630597970627 2255339702733945896955941)
                ·
                  refine ⟨422876194262614855679239, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2255339702733945896955941 422876194262614855679239)
                  ·
                    rfl

theorem cell21_1852984_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 3, 3, 1, 4].length) (baseStart_1852984 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1852984 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1852984 prefixEnd_1852984 := by exact prefixLift 1852984
  have htrace : WordTrace (prefixWord ++ tailWord_1852984) baseStart_1852984 baseEnd_1852984 := by
    simpa [prefixWord, tailWord_1852984, baseEnd_1852984] using wordTrace_append hprefix tailTrace_1852984
  have hstable : (prefixWord ++ tailWord_1852984).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1852984).length < 2 ^ (prefixWord ++ tailWord_1852984).sum := by decide
  have hdescent : baseEnd_1852984 < baseStart_1852984 := by decide
  rcases family_descends (prefixWord ++ tailWord_1852984) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1853029 : List Nat := [1, 3, 1, 3, 3, 3, 1, 1, 5]
def baseStart_1853029 : Nat := 118140960795 + 1853029 * 2 ^ 59
def prefixEnd_1853029 : Nat := 4983230072969 + 3 ^ 40 * 1853029 * 2
def baseEnd_1853029 : Nat := 422886463875704777429147

theorem tailTrace_1853029 : CollatzResearch.WordTrace tailWord_1853029 prefixEnd_1853029 422886463875704777429147 := by
  unfold tailWord_1853029
  simp only [CollatzResearch.WordTrace]
  refine ⟨67585520003799880002674141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45057013335866586668449427 67585520003799880002674141)
  ·
    refine ⟨25344570001424955001002803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 67585520003799880002674141 25344570001424955001002803)
    ·
      refine ⟨38016855002137432501504205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25344570001424955001002803 38016855002137432501504205)
      ·
        refine ⟨14256320625801537188064077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 38016855002137432501504205 14256320625801537188064077)
        ·
          refine ⟨5346120234675576445524029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14256320625801537188064077 5346120234675576445524029)
          ·
            refine ⟨2004795088003341167071511, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5346120234675576445524029 2004795088003341167071511)
            ·
              refine ⟨3007192632005011750607267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2004795088003341167071511 3007192632005011750607267)
              ·
                refine ⟨4510788948007517625910901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3007192632005011750607267 4510788948007517625910901)
                ·
                  refine ⟨422886463875704777429147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4510788948007517625910901 422886463875704777429147)
                  ·
                    rfl

theorem cell21_1853029_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 3, 1, 1, 5].length) (baseStart_1853029 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1853029 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1853029 prefixEnd_1853029 := by exact prefixLift 1853029
  have htrace : WordTrace (prefixWord ++ tailWord_1853029) baseStart_1853029 baseEnd_1853029 := by
    simpa [prefixWord, tailWord_1853029, baseEnd_1853029] using wordTrace_append hprefix tailTrace_1853029
  have hstable : (prefixWord ++ tailWord_1853029).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1853029).length < 2 ^ (prefixWord ++ tailWord_1853029).sum := by decide
  have hdescent : baseEnd_1853029 < baseStart_1853029 := by decide
  rcases family_descends (prefixWord ++ tailWord_1853029) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1853057 : List Nat := [1, 2, 4, 2, 1, 2, 2, 7]
def baseStart_1853057 : Nat := 118140960795 + 1853057 * 2 ^ 59
def prefixEnd_1853057 : Nat := 4983230072969 + 3 ^ 40 * 1853057 * 2
def baseEnd_1853057 : Nat := 140964284619060983654141

theorem tailTrace_1853057 : CollatzResearch.WordTrace tailWord_1853057 prefixEnd_1853057 140964284619060983654141 := by
  unfold tailWord_1853057
  simp only [CollatzResearch.WordTrace]
  refine ⟨67586541247698440784693425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45057694165132293856462283 67586541247698440784693425)
  ·
    refine ⟨50689905935773830588520069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67586541247698440784693425 50689905935773830588520069)
    ·
      refine ⟨9504357362957593235347513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 50689905935773830588520069 9504357362957593235347513)
      ·
        refine ⟨7128268022218194926510635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9504357362957593235347513 7128268022218194926510635)
        ·
          refine ⟨10692402033327292389765953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7128268022218194926510635 10692402033327292389765953)
          ·
            refine ⟨8019301524995469292324465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10692402033327292389765953 8019301524995469292324465)
            ·
              refine ⟨6014476143746601969243349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8019301524995469292324465 6014476143746601969243349)
              ·
                refine ⟨140964284619060983654141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6014476143746601969243349 140964284619060983654141)
                ·
                  rfl

theorem cell21_1853057_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 2, 2, 7].length) (baseStart_1853057 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1853057 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1853057 prefixEnd_1853057 := by exact prefixLift 1853057
  have htrace : WordTrace (prefixWord ++ tailWord_1853057) baseStart_1853057 baseEnd_1853057 := by
    simpa [prefixWord, tailWord_1853057, baseEnd_1853057] using wordTrace_append hprefix tailTrace_1853057
  have hstable : (prefixWord ++ tailWord_1853057).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1853057).length < 2 ^ (prefixWord ++ tailWord_1853057).sum := by decide
  have hdescent : baseEnd_1853057 < baseStart_1853057 := by decide
  rcases family_descends (prefixWord ++ tailWord_1853057) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1853074 : List Nat := [3, 2, 3, 1, 4, 8]
def baseStart_1853074 : Nat := 118140960795 + 1853074 * 2 ^ 59
def prefixEnd_1853074 : Nat := 4983230072969 + 3 ^ 40 * 1853074 * 2
def baseEnd_1853074 : Nat := 15662841981066470339965

theorem tailTrace_1853074 : CollatzResearch.WordTrace tailWord_1853074 prefixEnd_1853074 15662841981066470339965 := by
  unfold tailWord_1853074
  simp only [CollatzResearch.WordTrace]
  refine ⟨16896790322159213172015569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 45058107525757901792041517 16896790322159213172015569)
  ·
    refine ⟨12672592741619409879011677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16896790322159213172015569 12672592741619409879011677)
    ·
      refine ⟨4752222278107278704629379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12672592741619409879011677 4752222278107278704629379)
      ·
        refine ⟨7128333417160918056944069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4752222278107278704629379 7128333417160918056944069)
        ·
          refine ⟨1336562515717672135677013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7128333417160918056944069 1336562515717672135677013)
          ·
            refine ⟨15662841981066470339965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 1336562515717672135677013 15662841981066470339965)
            ·
              rfl

theorem cell21_1853074_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 4, 8].length) (baseStart_1853074 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1853074 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1853074 prefixEnd_1853074 := by exact prefixLift 1853074
  have htrace : WordTrace (prefixWord ++ tailWord_1853074) baseStart_1853074 baseEnd_1853074 := by
    simpa [prefixWord, tailWord_1853074, baseEnd_1853074] using wordTrace_append hprefix tailTrace_1853074
  have hstable : (prefixWord ++ tailWord_1853074).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1853074).length < 2 ^ (prefixWord ++ tailWord_1853074).sum := by decide
  have hdescent : baseEnd_1853074 < baseStart_1853074 := by decide
  rcases family_descends (prefixWord ++ tailWord_1853074) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1853190 : List Nat := [6, 2, 2, 1, 2, 1, 1, 1, 5]
def baseStart_1853190 : Nat := 118140960795 + 1853190 * 2 ^ 59
def prefixEnd_1853190 : Nat := 4983230072969 + 3 ^ 40 * 1853190 * 2
def baseEnd_1853190 : Nat := 422923206269204275245485

theorem tailTrace_1853190 : CollatzResearch.WordTrace tailWord_1853190 prefixEnd_1853190 422923206269204275245485 := by
  unfold tailWord_1853190
  simp only [CollatzResearch.WordTrace]
  refine ⟨2112231004881768890602657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 45060928104144402999523349 2112231004881768890602657)
  ·
    refine ⟨1584173253661326667951993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2112231004881768890602657 1584173253661326667951993)
    ·
      refine ⟨1188129940245995000963995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1584173253661326667951993 1188129940245995000963995)
      ·
        refine ⟨1782194910368992501445993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1188129940245995000963995 1782194910368992501445993)
        ·
          refine ⟨1336646182776744376084495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1782194910368992501445993 1336646182776744376084495)
          ·
            refine ⟨2004969274165116564126743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1336646182776744376084495 2004969274165116564126743)
            ·
              refine ⟨3007453911247674846190115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2004969274165116564126743 3007453911247674846190115)
              ·
                refine ⟨4511180866871512269285173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3007453911247674846190115 4511180866871512269285173)
                ·
                  refine ⟨422923206269204275245485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4511180866871512269285173 422923206269204275245485)
                  ·
                    rfl

theorem cell21_1853190_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 2, 1, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 2, 1, 2, 1, 1, 1, 5].length) (baseStart_1853190 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1853190 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1853190 prefixEnd_1853190 := by exact prefixLift 1853190
  have htrace : WordTrace (prefixWord ++ tailWord_1853190) baseStart_1853190 baseEnd_1853190 := by
    simpa [prefixWord, tailWord_1853190, baseEnd_1853190] using wordTrace_append hprefix tailTrace_1853190
  have hstable : (prefixWord ++ tailWord_1853190).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1853190).length < 2 ^ (prefixWord ++ tailWord_1853190).sum := by decide
  have hdescent : baseEnd_1853190 < baseStart_1853190 := by decide
  rcases family_descends (prefixWord ++ tailWord_1853190) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1853204 : List Nat := [2, 4, 4, 1, 2, 1, 2, 1, 4]
def baseStart_1853204 : Nat := 118140960795 + 1853204 * 2 ^ 59
def prefixEnd_1853204 : Nat := 4983230072969 + 3 ^ 40 * 1853204 * 2
def baseEnd_1853204 : Nat := 422926401259943362012123

theorem tailTrace_1853204 : CollatzResearch.WordTrace tailWord_1853204 prefixEnd_1853204 422926401259943362012123 := by
  unfold tailWord_1853204
  simp only [CollatzResearch.WordTrace]
  refine ⟨33795951389082942445147333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45061268518777256593529777 33795951389082942445147333)
  ·
    refine ⟨6336740885453051708465125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 33795951389082942445147333 6336740885453051708465125)
    ·
      refine ⟨1188138916022447195337211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 6336740885453051708465125 1188138916022447195337211)
      ·
        refine ⟨1782208374033670793005817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1188138916022447195337211 1782208374033670793005817)
        ·
          refine ⟨1336656280525253094754363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1782208374033670793005817 1336656280525253094754363)
          ·
            refine ⟨2004984420787879642131545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1336656280525253094754363 2004984420787879642131545)
            ·
              refine ⟨1503738315590909731598659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2004984420787879642131545 1503738315590909731598659)
              ·
                refine ⟨2255607473386364597397989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1503738315590909731598659 2255607473386364597397989)
                ·
                  refine ⟨422926401259943362012123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2255607473386364597397989 422926401259943362012123)
                  ·
                    rfl

theorem cell21_1853204_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 4, 1, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 4, 1, 2, 1, 2, 1, 4].length) (baseStart_1853204 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1853204 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1853204 prefixEnd_1853204 := by exact prefixLift 1853204
  have htrace : WordTrace (prefixWord ++ tailWord_1853204) baseStart_1853204 baseEnd_1853204 := by
    simpa [prefixWord, tailWord_1853204, baseEnd_1853204] using wordTrace_append hprefix tailTrace_1853204
  have hstable : (prefixWord ++ tailWord_1853204).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1853204).length < 2 ^ (prefixWord ++ tailWord_1853204).sum := by decide
  have hdescent : baseEnd_1853204 < baseStart_1853204 := by decide
  rcases family_descends (prefixWord ++ tailWord_1853204) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1853302 : List Nat := [5, 1, 1, 3, 2, 1, 8]
def baseStart_1853302 : Nat := 118140960795 + 1853302 * 2 ^ 59
def prefixEnd_1853302 : Nat := 4983230072969 + 3 ^ 40 * 1853302 * 2
def baseEnd_1853302 : Nat := 46994307355012996597621

theorem tailTrace_1853302 : CollatzResearch.WordTrace tailWord_1853302 prefixEnd_1853302 46994307355012996597621 := by
  unfold tailWord_1853302
  simp only [CollatzResearch.WordTrace]
  refine ⟨4224717320738177976710135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 45063651421207231751574773 4224717320738177976710135)
  ·
    refine ⟨6337075981107266965065203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4224717320738177976710135 6337075981107266965065203)
    ·
      refine ⟨9505613971660900447597805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6337075981107266965065203 9505613971660900447597805)
      ·
        refine ⟨3564605239372837667849177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9505613971660900447597805 3564605239372837667849177)
        ·
          refine ⟨2673453929529628250886883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3564605239372837667849177 2673453929529628250886883)
          ·
            refine ⟨4010180894294442376330325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2673453929529628250886883 4010180894294442376330325)
            ·
              refine ⟨46994307355012996597621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 4010180894294442376330325 46994307355012996597621)
              ·
                rfl

theorem cell21_1853302_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 2, 1, 8].length) (baseStart_1853302 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1853302 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1853302 prefixEnd_1853302 := by exact prefixLift 1853302
  have htrace : WordTrace (prefixWord ++ tailWord_1853302) baseStart_1853302 baseEnd_1853302 := by
    simpa [prefixWord, tailWord_1853302, baseEnd_1853302] using wordTrace_append hprefix tailTrace_1853302
  have hstable : (prefixWord ++ tailWord_1853302).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1853302).length < 2 ^ (prefixWord ++ tailWord_1853302).sum := by decide
  have hdescent : baseEnd_1853302 < baseStart_1853302 := by decide
  rcases family_descends (prefixWord ++ tailWord_1853302) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1853336 : List Nat := [2, 1, 2, 6, 2, 1, 2, 5]
def baseStart_1853336 : Nat := 118140960795 + 1853336 * 2 ^ 59
def prefixEnd_1853336 : Nat := 4983230072969 + 3 ^ 40 * 1853336 * 2
def baseEnd_1853336 : Nat := 140985508486113488603951

theorem tailTrace_1853336 : CollatzResearch.WordTrace tailWord_1853336 prefixEnd_1853336 140985508486113488603951 := by
  unfold tailWord_1853336
  simp only [CollatzResearch.WordTrace]
  refine ⟨33798358606843835717049931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45064478142458447622733241 33798358606843835717049931)
  ·
    refine ⟨50697537910265753575574897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33798358606843835717049931 50697537910265753575574897)
    ·
      refine ⟨38023153432699315181681173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50697537910265753575574897 38023153432699315181681173)
      ·
        refine ⟨1782335317157780399141305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 38023153432699315181681173 1782335317157780399141305)
        ·
          refine ⟨1336751487868335299355979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1782335317157780399141305 1336751487868335299355979)
          ·
            refine ⟨2005127231802502949033969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1336751487868335299355979 2005127231802502949033969)
            ·
              refine ⟨1503845423851877211775477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2005127231802502949033969 1503845423851877211775477)
              ·
                refine ⟨140985508486113488603951, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1503845423851877211775477 140985508486113488603951)
                ·
                  rfl

theorem cell21_1853336_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 6, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 6, 2, 1, 2, 5].length) (baseStart_1853336 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1853336 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1853336 prefixEnd_1853336 := by exact prefixLift 1853336
  have htrace : WordTrace (prefixWord ++ tailWord_1853336) baseStart_1853336 baseEnd_1853336 := by
    simpa [prefixWord, tailWord_1853336, baseEnd_1853336] using wordTrace_append hprefix tailTrace_1853336
  have hstable : (prefixWord ++ tailWord_1853336).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1853336).length < 2 ^ (prefixWord ++ tailWord_1853336).sum := by decide
  have hdescent : baseEnd_1853336 < baseStart_1853336 := by decide
  rcases family_descends (prefixWord ++ tailWord_1853336) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1853361 : List Nat := [1, 2, 2, 4, 2, 3, 7]
def baseStart_1853361 : Nat := 118140960795 + 1853361 * 2 ^ 59
def prefixEnd_1853361 : Nat := 4983230072969 + 3 ^ 40 * 1853361 * 2
def baseEnd_1853361 : Nat := 46995803422105108655015

theorem tailTrace_1853361 : CollatzResearch.WordTrace tailWord_1853361 prefixEnd_1853361 46995803422105108655015 := by
  unfold tailWord_1853361
  simp only [CollatzResearch.WordTrace]
  refine ⟨67597629038597100703759937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45065086025731400469173291 67597629038597100703759937)
  ·
    refine ⟨50698221778947825527819953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67597629038597100703759937 50698221778947825527819953)
    ·
      refine ⟨38023666334210869145864965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50698221778947825527819953 38023666334210869145864965)
      ·
        refine ⟨7129437437664537964849681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 38023666334210869145864965 7129437437664537964849681)
        ·
          refine ⟨5347078078248403473637261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7129437437664537964849681 5347078078248403473637261)
          ·
            refine ⟨2005154279343151302613973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5347078078248403473637261 2005154279343151302613973)
            ·
              refine ⟨46995803422105108655015, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 2005154279343151302613973 46995803422105108655015)
              ·
                rfl

theorem cell21_1853361_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 3, 7].length) (baseStart_1853361 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1853361 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1853361 prefixEnd_1853361 := by exact prefixLift 1853361
  have htrace : WordTrace (prefixWord ++ tailWord_1853361) baseStart_1853361 baseEnd_1853361 := by
    simpa [prefixWord, tailWord_1853361, baseEnd_1853361] using wordTrace_append hprefix tailTrace_1853361
  have hstable : (prefixWord ++ tailWord_1853361).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1853361).length < 2 ^ (prefixWord ++ tailWord_1853361).sum := by decide
  have hdescent : baseEnd_1853361 < baseStart_1853361 := by decide
  rcases family_descends (prefixWord ++ tailWord_1853361) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1853451 : List Nat := [1, 1, 1, 1, 6, 1, 3, 2, 5]
def baseStart_1853451 : Nat := 118140960795 + 1853451 * 2 ^ 59
def prefixEnd_1853451 : Nat := 4983230072969 + 3 ^ 40 * 1853451 * 2
def baseEnd_1853451 : Nat := 422982770025125821394951

theorem tailTrace_1853451 : CollatzResearch.WordTrace tailWord_1853451 prefixEnd_1853451 422982770025125821394951 := by
  unfold tailWord_1853451
  simp only [CollatzResearch.WordTrace]
  refine ⟨67600911608271046074536207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45067274405514030716357471 67600911608271046074536207)
  ·
    refine ⟨101401367412406569111804311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67600911608271046074536207 101401367412406569111804311)
    ·
      refine ⟨152102051118609853667706467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101401367412406569111804311 152102051118609853667706467)
      ·
        refine ⟨228153076677914780501559701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 152102051118609853667706467 228153076677914780501559701)
        ·
          refine ⟨10694675469277255336010611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 228153076677914780501559701 10694675469277255336010611)
          ·
            refine ⟨16042013203915883004015917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10694675469277255336010611 16042013203915883004015917)
            ·
              refine ⟨6015754951468456126505969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16042013203915883004015917 6015754951468456126505969)
              ·
                refine ⟨4511816213601342094879477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6015754951468456126505969 4511816213601342094879477)
                ·
                  refine ⟨422982770025125821394951, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4511816213601342094879477 422982770025125821394951)
                  ·
                    rfl

theorem cell21_1853451_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 3, 2, 5].length) (baseStart_1853451 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1853451 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1853451 prefixEnd_1853451 := by exact prefixLift 1853451
  have htrace : WordTrace (prefixWord ++ tailWord_1853451) baseStart_1853451 baseEnd_1853451 := by
    simpa [prefixWord, tailWord_1853451, baseEnd_1853451] using wordTrace_append hprefix tailTrace_1853451
  have hstable : (prefixWord ++ tailWord_1853451).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1853451).length < 2 ^ (prefixWord ++ tailWord_1853451).sum := by decide
  have hdescent : baseEnd_1853451 < baseStart_1853451 := by decide
  rcases family_descends (prefixWord ++ tailWord_1853451) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1853465 : List Nat := [1, 2, 1, 2, 1, 1, 3, 4, 6]
def baseStart_1853465 : Nat := 118140960795 + 1853465 * 2 ^ 59
def prefixEnd_1853465 : Nat := 4983230072969 + 3 ^ 40 * 1853465 * 2
def baseEnd_1853465 : Nat := 422985965015864908161589

theorem tailTrace_1853465 : CollatzResearch.WordTrace tailWord_1853465 prefixEnd_1853465 422985965015864908161589 := by
  unfold tailWord_1853465
  simp only [CollatzResearch.WordTrace]
  refine ⟨67601422230220326465545849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45067614820146884310363899 67601422230220326465545849)
  ·
    refine ⟨50701066672665244849159387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67601422230220326465545849 50701066672665244849159387)
    ·
      refine ⟨76051600008997867273739081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50701066672665244849159387 76051600008997867273739081)
      ·
        refine ⟨57038700006748400455304311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 76051600008997867273739081 57038700006748400455304311)
        ·
          refine ⟨85558050010122600682956467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57038700006748400455304311 85558050010122600682956467)
          ·
            refine ⟨128337075015183901024434701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 85558050010122600682956467 128337075015183901024434701)
            ·
              refine ⟨48126403130693962884163013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 128337075015183901024434701 48126403130693962884163013)
              ·
                refine ⟨9023700587005118040780565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 48126403130693962884163013 9023700587005118040780565)
                ·
                  refine ⟨422985965015864908161589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9023700587005118040780565 422985965015864908161589)
                  ·
                    rfl

theorem cell21_1853465_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 3, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 3, 4, 6].length) (baseStart_1853465 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1853465 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1853465 prefixEnd_1853465 := by exact prefixLift 1853465
  have htrace : WordTrace (prefixWord ++ tailWord_1853465) baseStart_1853465 baseEnd_1853465 := by
    simpa [prefixWord, tailWord_1853465, baseEnd_1853465] using wordTrace_append hprefix tailTrace_1853465
  have hstable : (prefixWord ++ tailWord_1853465).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1853465).length < 2 ^ (prefixWord ++ tailWord_1853465).sum := by decide
  have hdescent : baseEnd_1853465 < baseStart_1853465 := by decide
  rcases family_descends (prefixWord ++ tailWord_1853465) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1853572 : List Nat := [2, 3, 2, 1, 2, 1, 1, 9]
def baseStart_1853572 : Nat := 118140960795 + 1853572 * 2 ^ 59
def prefixEnd_1853572 : Nat := 4983230072969 + 3 ^ 40 * 1853572 * 2
def baseEnd_1853572 : Nat := 141003461291218833292679

theorem tailTrace_1853572 : CollatzResearch.WordTrace tailWord_1853572 prefixEnd_1853572 141003461291218833292679 := by
  unfold tailWord_1853572
  simp only [CollatzResearch.WordTrace]
  refine ⟨33802662420416341869845485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45070216560555122493127313 33802662420416341869845485)
  ·
    refine ⟨12675998407656128201192057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 33802662420416341869845485 12675998407656128201192057)
    ·
      refine ⟨9506998805742096150894043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12675998407656128201192057 9506998805742096150894043)
      ·
        refine ⟨14260498208613144226341065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9506998805742096150894043 14260498208613144226341065)
        ·
          refine ⟨10695373656459858169755799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14260498208613144226341065 10695373656459858169755799)
          ·
            refine ⟨16043060484689787254633699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10695373656459858169755799 16043060484689787254633699)
            ·
              refine ⟨24064590727034680881950549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16043060484689787254633699 24064590727034680881950549)
              ·
                refine ⟨141003461291218833292679, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 24064590727034680881950549 141003461291218833292679)
                ·
                  rfl

theorem cell21_1853572_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 1, 9].length) (baseStart_1853572 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1853572 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1853572 prefixEnd_1853572 := by exact prefixLift 1853572
  have htrace : WordTrace (prefixWord ++ tailWord_1853572) baseStart_1853572 baseEnd_1853572 := by
    simpa [prefixWord, tailWord_1853572, baseEnd_1853572] using wordTrace_append hprefix tailTrace_1853572
  have hstable : (prefixWord ++ tailWord_1853572).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1853572).length < 2 ^ (prefixWord ++ tailWord_1853572).sum := by decide
  have hdescent : baseEnd_1853572 < baseStart_1853572 := by decide
  rcases family_descends (prefixWord ++ tailWord_1853572) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1853654 : List Nat := [5, 2, 1, 2, 1, 1, 2, 4, 3]
def baseStart_1853654 : Nat := 118140960795 + 1853654 * 2 ^ 59
def prefixEnd_1853654 : Nat := 4983230072969 + 3 ^ 40 * 1853654 * 2
def baseEnd_1853654 : Nat := 423029097390842579511203

theorem tailTrace_1853654 : CollatzResearch.WordTrace tailWord_1853654 prefixEnd_1853654 423029097390842579511203 := by
  unfold tailWord_1853654
  simp only [CollatzResearch.WordTrace]
  refine ⟨4225519726658475734011001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 45072210417690407829450677 4225519726658475734011001)
  ·
    refine ⟨3169139794993856800508251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4225519726658475734011001 3169139794993856800508251)
    ·
      refine ⟨4753709692490785200762377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3169139794993856800508251 4753709692490785200762377)
      ·
        refine ⟨3565282269368088900571783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4753709692490785200762377 3565282269368088900571783)
        ·
          refine ⟨5347923404052133350857675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3565282269368088900571783 5347923404052133350857675)
          ·
            refine ⟨8021885106078200026286513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5347923404052133350857675 8021885106078200026286513)
            ·
              refine ⟨6016413829558650019714885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8021885106078200026286513 6016413829558650019714885)
              ·
                refine ⟨1128077593042246878696541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6016413829558650019714885 1128077593042246878696541)
                ·
                  refine ⟨423029097390842579511203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1128077593042246878696541 423029097390842579511203)
                  ·
                    rfl

theorem cell21_1853654_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 1, 2, 4, 3].length) (baseStart_1853654 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1853654 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1853654 prefixEnd_1853654 := by exact prefixLift 1853654
  have htrace : WordTrace (prefixWord ++ tailWord_1853654) baseStart_1853654 baseEnd_1853654 := by
    simpa [prefixWord, tailWord_1853654, baseEnd_1853654] using wordTrace_append hprefix tailTrace_1853654
  have hstable : (prefixWord ++ tailWord_1853654).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1853654).length < 2 ^ (prefixWord ++ tailWord_1853654).sum := by decide
  have hdescent : baseEnd_1853654 < baseStart_1853654 := by decide
  rcases family_descends (prefixWord ++ tailWord_1853654) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1853679 : List Nat := [1, 1, 2, 1, 6, 1, 2, 2, 5]
def baseStart_1853679 : Nat := 118140960795 + 1853679 * 2 ^ 59
def prefixEnd_1853679 : Nat := 4983230072969 + 3 ^ 40 * 1853679 * 2
def baseEnd_1853679 : Nat := 423034802731448091594485

theorem tailTrace_1853679 : CollatzResearch.WordTrace tailWord_1853679 prefixEnd_1853679 423034802731448091594485 := by
  unfold tailWord_1853679
  simp only [CollatzResearch.WordTrace]
  refine ⟨67609227451445041013836091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45072818300963360675890727 67609227451445041013836091)
  ·
    refine ⟨101413841177167561520754137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67609227451445041013836091 101413841177167561520754137)
    ·
      refine ⟨76060380882875671140565603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 101413841177167561520754137 76060380882875671140565603)
      ·
        refine ⟨114090571324313506710848405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76060380882875671140565603 114090571324313506710848405)
        ·
          refine ⟨5347995530827195627071019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 114090571324313506710848405 5347995530827195627071019)
          ·
            refine ⟨8021993296240793440606529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5347995530827195627071019 8021993296240793440606529)
            ·
              refine ⟨6016494972180595080454897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8021993296240793440606529 6016494972180595080454897)
              ·
                refine ⟨4512371229135446310341173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6016494972180595080454897 4512371229135446310341173)
                ·
                  refine ⟨423034802731448091594485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4512371229135446310341173 423034802731448091594485)
                  ·
                    rfl

theorem cell21_1853679_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 1, 2, 2, 5].length) (baseStart_1853679 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1853679 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1853679 prefixEnd_1853679 := by exact prefixLift 1853679
  have htrace : WordTrace (prefixWord ++ tailWord_1853679) baseStart_1853679 baseEnd_1853679 := by
    simpa [prefixWord, tailWord_1853679, baseEnd_1853679] using wordTrace_append hprefix tailTrace_1853679
  have hstable : (prefixWord ++ tailWord_1853679).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1853679).length < 2 ^ (prefixWord ++ tailWord_1853679).sum := by decide
  have hdescent : baseEnd_1853679 < baseStart_1853679 := by decide
  rcases family_descends (prefixWord ++ tailWord_1853679) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1853682 : List Nat := [3, 2, 1, 3, 2, 3, 2, 5]
def baseStart_1853682 : Nat := 118140960795 + 1853682 * 2 ^ 59
def prefixEnd_1853682 : Nat := 4983230072969 + 3 ^ 40 * 1853682 * 2
def baseEnd_1853682 : Nat := 141011829124106917681493

theorem tailTrace_1853682 : CollatzResearch.WordTrace tailWord_1853682 prefixEnd_1853682 141011829124106917681493 := by
  unfold tailWord_1853682
  simp only [CollatzResearch.WordTrace]
  refine ⟨16902334217608543131548825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 45072891246956115017463533 16902334217608543131548825)
  ·
    refine ⟨12676750663206407348661619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16902334217608543131548825 12676750663206407348661619)
    ·
      refine ⟨19015125994809611022992429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12676750663206407348661619 19015125994809611022992429)
      ·
        refine ⟨7130672248053604133622161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19015125994809611022992429 7130672248053604133622161)
        ·
          refine ⟨5348004186040203100216621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7130672248053604133622161 5348004186040203100216621)
          ·
            refine ⟨2005501569765076162581233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5348004186040203100216621 2005501569765076162581233)
            ·
              refine ⟨1504126177323807121935925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2005501569765076162581233 1504126177323807121935925)
              ·
                refine ⟨141011829124106917681493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1504126177323807121935925 141011829124106917681493)
                ·
                  rfl

theorem cell21_1853682_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 3, 2, 5].length) (baseStart_1853682 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1853682 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1853682 prefixEnd_1853682 := by exact prefixLift 1853682
  have htrace : WordTrace (prefixWord ++ tailWord_1853682) baseStart_1853682 baseEnd_1853682 := by
    simpa [prefixWord, tailWord_1853682, baseEnd_1853682] using wordTrace_append hprefix tailTrace_1853682
  have hstable : (prefixWord ++ tailWord_1853682).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1853682).length < 2 ^ (prefixWord ++ tailWord_1853682).sum := by decide
  have hdescent : baseEnd_1853682 < baseStart_1853682 := by decide
  rcases family_descends (prefixWord ++ tailWord_1853682) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1853696 : List Nat := [2, 1, 1, 2, 1, 1, 7, 3, 3]
def baseStart_1853696 : Nat := 118140960795 + 1853696 * 2 ^ 59
def prefixEnd_1853696 : Nat := 4983230072969 + 3 ^ 40 * 1853696 * 2
def baseEnd_1853696 : Nat := 423038682363059839811117

theorem tailTrace_1853696 : CollatzResearch.WordTrace tailWord_1853696 prefixEnd_1853696 423038682363059839811117 := by
  unfold tailWord_1853696
  simp only [CollatzResearch.WordTrace]
  refine ⟨33804923746191726458602471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45073231661588968611469961 33804923746191726458602471)
  ·
    refine ⟨50707385619287589687903707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33804923746191726458602471 50707385619287589687903707)
    ·
      refine ⟨76061078428931384531855561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50707385619287589687903707 76061078428931384531855561)
      ·
        refine ⟨57045808821698538398891671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 76061078428931384531855561 57045808821698538398891671)
        ·
          refine ⟨85568713232547807598337507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57045808821698538398891671 85568713232547807598337507)
          ·
            refine ⟨128353069848821711397506261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 85568713232547807598337507 128353069848821711397506261)
            ·
              refine ⟨3008275074581758860879053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 128353069848821711397506261 3008275074581758860879053)
              ·
                refine ⟨1128103152968159572829645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3008275074581758860879053 1128103152968159572829645)
                ·
                  refine ⟨423038682363059839811117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1128103152968159572829645 423038682363059839811117)
                  ·
                    rfl

theorem cell21_1853696_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 7, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 7, 3, 3].length) (baseStart_1853696 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1853696 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1853696 prefixEnd_1853696 := by exact prefixLift 1853696
  have htrace : WordTrace (prefixWord ++ tailWord_1853696) baseStart_1853696 baseEnd_1853696 := by
    simpa [prefixWord, tailWord_1853696, baseEnd_1853696] using wordTrace_append hprefix tailTrace_1853696
  have hstable : (prefixWord ++ tailWord_1853696).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1853696).length < 2 ^ (prefixWord ++ tailWord_1853696).sum := by decide
  have hdescent : baseEnd_1853696 < baseStart_1853696 := by decide
  rcases family_descends (prefixWord ++ tailWord_1853696) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1853710 : List Nat := [4, 1, 1, 2, 1, 2, 2, 4, 4]
def baseStart_1853710 : Nat := 118140960795 + 1853710 * 2 ^ 59
def prefixEnd_1853710 : Nat := 4983230072969 + 3 ^ 40 * 1853710 * 2
def baseEnd_1853710 : Nat := 423041877353798926577755

theorem tailTrace_1853710 : CollatzResearch.WordTrace tailWord_1853710 prefixEnd_1853710 423041877353798926577755 := by
  unfold tailWord_1853710
  simp only [CollatzResearch.WordTrace]
  refine ⟨8451294764291591663526823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 45073572076221822205476389 8451294764291591663526823)
  ·
    refine ⟨12676942146437387495290235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8451294764291591663526823 12676942146437387495290235)
    ·
      refine ⟨19015413219656081242935353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12676942146437387495290235 19015413219656081242935353)
      ·
        refine ⟨14261559914742060932201515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19015413219656081242935353 14261559914742060932201515)
        ·
          refine ⟨21392339872113091398302273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14261559914742060932201515 21392339872113091398302273)
          ·
            refine ⟨16044254904084818548726705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21392339872113091398302273 16044254904084818548726705)
            ·
              refine ⟨12033191178063613911545029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16044254904084818548726705 12033191178063613911545029)
              ·
                refine ⟨2256223345886927608414693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12033191178063613911545029 2256223345886927608414693)
                ·
                  refine ⟨423041877353798926577755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2256223345886927608414693 423041877353798926577755)
                  ·
                    rfl

theorem cell21_1853710_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 2, 4, 4].length) (baseStart_1853710 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1853710 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1853710 prefixEnd_1853710 := by exact prefixLift 1853710
  have htrace : WordTrace (prefixWord ++ tailWord_1853710) baseStart_1853710 baseEnd_1853710 := by
    simpa [prefixWord, tailWord_1853710, baseEnd_1853710] using wordTrace_append hprefix tailTrace_1853710
  have hstable : (prefixWord ++ tailWord_1853710).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1853710).length < 2 ^ (prefixWord ++ tailWord_1853710).sum := by decide
  have hdescent : baseEnd_1853710 < baseStart_1853710 := by decide
  rcases family_descends (prefixWord ++ tailWord_1853710) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1853713 : List Nat := [1, 2, 2, 1, 1, 6, 3, 2, 3]
def baseStart_1853713 : Nat := 118140960795 + 1853713 * 2 ^ 59
def prefixEnd_1853713 : Nat := 4983230072969 + 3 ^ 40 * 1853713 * 2
def baseEnd_1853713 : Nat := 423042561994671588027749

theorem tailTrace_1853713 : CollatzResearch.WordTrace tailWord_1853713 prefixEnd_1853713 423042561994671588027749 := by
  unfold tailWord_1853713
  simp only [CollatzResearch.WordTrace]
  refine ⟨67610467533321864820573793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45073645022214576547049195 67610467533321864820573793)
  ·
    refine ⟨50707850649991398615430345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67610467533321864820573793 50707850649991398615430345)
    ·
      refine ⟨38030887987493548961572759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50707850649991398615430345 38030887987493548961572759)
      ·
        refine ⟨57046331981240323442359139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38030887987493548961572759 57046331981240323442359139)
        ·
          refine ⟨85569497971860485163538709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57046331981240323442359139 85569497971860485163538709)
          ·
            refine ⟨4011070217430960242040877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 85569497971860485163538709 4011070217430960242040877)
            ·
              refine ⟨1504151331536610090765329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4011070217430960242040877 1504151331536610090765329)
              ·
                refine ⟨1128113498652457568073997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1504151331536610090765329 1128113498652457568073997)
                ·
                  refine ⟨423042561994671588027749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1128113498652457568073997 423042561994671588027749)
                  ·
                    rfl

theorem cell21_1853713_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 6, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 6, 3, 2, 3].length) (baseStart_1853713 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1853713 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1853713 prefixEnd_1853713 := by exact prefixLift 1853713
  have htrace : WordTrace (prefixWord ++ tailWord_1853713) baseStart_1853713 baseEnd_1853713 := by
    simpa [prefixWord, tailWord_1853713, baseEnd_1853713] using wordTrace_append hprefix tailTrace_1853713
  have hstable : (prefixWord ++ tailWord_1853713).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1853713).length < 2 ^ (prefixWord ++ tailWord_1853713).sum := by decide
  have hdescent : baseEnd_1853713 < baseStart_1853713 := by decide
  rcases family_descends (prefixWord ++ tailWord_1853713) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1853727 : List Nat := [1, 1, 2, 4, 3, 1, 4, 1, 4]
def baseStart_1853727 : Nat := 118140960795 + 1853727 * 2 ^ 59
def prefixEnd_1853727 : Nat := 4983230072969 + 3 ^ 40 * 1853727 * 2
def baseEnd_1853727 : Nat := 423045756985410674794387

theorem tailTrace_1853727 : CollatzResearch.WordTrace tailWord_1853727 prefixEnd_1853727 423045756985410674794387 := by
  unfold tailWord_1853727
  simp only [CollatzResearch.WordTrace]
  refine ⟨67610978155271145211583435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45073985436847430141055623 67610978155271145211583435)
  ·
    refine ⟨101416467232906717817375153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67610978155271145211583435 101416467232906717817375153)
    ·
      refine ⟨76062350424680038363031365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 101416467232906717817375153 76062350424680038363031365)
      ·
        refine ⟨14261690704627507193068381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 76062350424680038363031365 14261690704627507193068381)
        ·
          refine ⟨5348134014235315197400643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14261690704627507193068381 5348134014235315197400643)
          ·
            refine ⟨8022201021352972796100965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5348134014235315197400643 8022201021352972796100965)
            ·
              refine ⟨1504162691503682399268931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8022201021352972796100965 1504162691503682399268931)
              ·
                refine ⟨2256244037255523598903397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1504162691503682399268931 2256244037255523598903397)
                ·
                  refine ⟨423045756985410674794387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2256244037255523598903397 423045756985410674794387)
                  ·
                    rfl

theorem cell21_1853727_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 1, 4, 1, 4].length) (baseStart_1853727 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1853727 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1853727 prefixEnd_1853727 := by exact prefixLift 1853727
  have htrace : WordTrace (prefixWord ++ tailWord_1853727) baseStart_1853727 baseEnd_1853727 := by
    simpa [prefixWord, tailWord_1853727, baseEnd_1853727] using wordTrace_append hprefix tailTrace_1853727
  have hstable : (prefixWord ++ tailWord_1853727).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1853727).length < 2 ^ (prefixWord ++ tailWord_1853727).sum := by decide
  have hdescent : baseEnd_1853727 < baseStart_1853727 := by decide
  rcases family_descends (prefixWord ++ tailWord_1853727) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1853764 : List Nat := [2, 3, 4, 1, 3, 1, 2, 2, 3]
def baseStart_1853764 : Nat := 118140960795 + 1853764 * 2 ^ 59
def prefixEnd_1853764 : Nat := 4983230072969 + 3 ^ 40 * 1853764 * 2
def baseEnd_1853764 : Nat := 423054200889506832677645

theorem tailTrace_1853764 : CollatzResearch.WordTrace tailWord_1853764 prefixEnd_1853764 423054200889506832677645 := by
  unfold tailWord_1853764
  simp only [CollatzResearch.WordTrace]
  refine ⟨33806163828068550265340173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45074885104091400353786897 33806163828068550265340173)
  ·
    refine ⟨12677311435525706349502565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 33806163828068550265340173 12677311435525706349502565)
    ·
      refine ⟨2376995894161069940531731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 12677311435525706349502565 2376995894161069940531731)
      ·
        refine ⟨3565493841241604910797597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2376995894161069940531731 3565493841241604910797597)
        ·
          refine ⟨1337060190465601841549099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3565493841241604910797597 1337060190465601841549099)
          ·
            refine ⟨2005590285698402762323649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1337060190465601841549099 2005590285698402762323649)
            ·
              refine ⟨1504192714273802071742737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2005590285698402762323649 1504192714273802071742737)
              ·
                refine ⟨1128144535705351553807053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1504192714273802071742737 1128144535705351553807053)
                ·
                  refine ⟨423054200889506832677645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1128144535705351553807053 423054200889506832677645)
                  ·
                    rfl

theorem cell21_1853764_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 3, 1, 2, 2, 3].length) (baseStart_1853764 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1853764 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1853764 prefixEnd_1853764 := by exact prefixLift 1853764
  have htrace : WordTrace (prefixWord ++ tailWord_1853764) baseStart_1853764 baseEnd_1853764 := by
    simpa [prefixWord, tailWord_1853764, baseEnd_1853764] using wordTrace_append hprefix tailTrace_1853764
  have hstable : (prefixWord ++ tailWord_1853764).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1853764).length < 2 ^ (prefixWord ++ tailWord_1853764).sum := by decide
  have hdescent : baseEnd_1853764 < baseStart_1853764 := by decide
  rcases family_descends (prefixWord ++ tailWord_1853764) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1853772 : List Nat := [2, 2, 1, 3, 2, 1, 3, 4, 3]
def baseStart_1853772 : Nat := 118140960795 + 1853772 * 2 ^ 59
def prefixEnd_1853772 : Nat := 4983230072969 + 3 ^ 40 * 1853772 * 2
def baseEnd_1853772 : Nat := 423056026598500596544295

theorem tailTrace_1853772 : CollatzResearch.WordTrace tailWord_1853772 prefixEnd_1853772 423056026598500596544295 := by
  unfold tailWord_1853772
  simp only [CollatzResearch.WordTrace]
  refine ⟨33806309720054058948485785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45075079626738745264647713 33806309720054058948485785)
  ·
    refine ⟨25354732290040544211364339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33806309720054058948485785 25354732290040544211364339)
    ·
      refine ⟨38032098435060816317046509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25354732290040544211364339 38032098435060816317046509)
      ·
        refine ⟨14262036913147806118892441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 38032098435060816317046509 14262036913147806118892441)
        ·
          refine ⟨10696527684860854589169331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14262036913147806118892441 10696527684860854589169331)
          ·
            refine ⟨16044791527291281883753997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10696527684860854589169331 16044791527291281883753997)
            ·
              refine ⟨6016796822734230706407749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16044791527291281883753997 6016796822734230706407749)
              ·
                refine ⟨1128149404262668257451453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6016796822734230706407749 1128149404262668257451453)
                ·
                  refine ⟨423056026598500596544295, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1128149404262668257451453 423056026598500596544295)
                  ·
                    rfl

theorem cell21_1853772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 3, 4, 3].length) (baseStart_1853772 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1853772 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1853772 prefixEnd_1853772 := by exact prefixLift 1853772
  have htrace : WordTrace (prefixWord ++ tailWord_1853772) baseStart_1853772 baseEnd_1853772 := by
    simpa [prefixWord, tailWord_1853772, baseEnd_1853772] using wordTrace_append hprefix tailTrace_1853772
  have hstable : (prefixWord ++ tailWord_1853772).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1853772).length < 2 ^ (prefixWord ++ tailWord_1853772).sum := by decide
  have hdescent : baseEnd_1853772 < baseStart_1853772 := by decide
  rcases family_descends (prefixWord ++ tailWord_1853772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan21Incremental
