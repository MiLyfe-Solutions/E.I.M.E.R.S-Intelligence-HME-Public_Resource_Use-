import V185TrunkScan23Chunk0651

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_3854948 : List Nat := [2, 3, 1, 1, 2, 2, 2, 2, 4, 2, 2]
def baseStart_3854948 : Nat := 118140960795 + 3854948 * 2 ^ 59
def prefixEnd_3854948 : Nat := 4983230072969 + 3 ^ 40 * 3854948 * 2
def baseEnd_3854948 : Nat := 1979441222088488731921423

theorem tailTrace_3854948 : CollatzResearch.WordTrace tailWord_3854948 prefixEnd_3854948 1979441222088488731921423 := by
  unfold tailWord_3854948
  simp only [CollatzResearch.WordTrace]
  refine ⟨70300752219094621773890749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93734336292126162365187665 70300752219094621773890749)
  ·
    refine ⟨26362782082160483165209031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 70300752219094621773890749 26362782082160483165209031)
    ·
      refine ⟨39544173123240724747813547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26362782082160483165209031 39544173123240724747813547)
      ·
        refine ⟨59316259684861087121720321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39544173123240724747813547 59316259684861087121720321)
        ·
          refine ⟨44487194763645815341290241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59316259684861087121720321 44487194763645815341290241)
          ·
            refine ⟨33365396072734361505967681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44487194763645815341290241 33365396072734361505967681)
            ·
              refine ⟨25024047054550771129475761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33365396072734361505967681 25024047054550771129475761)
              ·
                refine ⟨18768035290913078347106821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25024047054550771129475761 18768035290913078347106821)
                ·
                  refine ⟨3519006617046202190082529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 18768035290913078347106821 3519006617046202190082529)
                  ·
                    refine ⟨2639254962784651642561897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3519006617046202190082529 2639254962784651642561897)
                    ·
                      refine ⟨1979441222088488731921423, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2639254962784651642561897 1979441222088488731921423)
                      ·
                        rfl

theorem cell23_3854948_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 2, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 2, 2, 4, 2, 2].length) (baseStart_3854948 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3854948 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3854948 prefixEnd_3854948 := by exact prefixLift 3854948
  have htrace : WordTrace (prefixWord ++ tailWord_3854948) baseStart_3854948 baseEnd_3854948 := by
    simpa [prefixWord, tailWord_3854948, baseEnd_3854948] using wordTrace_append hprefix tailTrace_3854948
  have hstable : (prefixWord ++ tailWord_3854948).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3854948).length < 2 ^ (prefixWord ++ tailWord_3854948).sum := by decide
  have hdescent : baseEnd_3854948 < baseStart_3854948 := by decide
  rcases family_descends (prefixWord ++ tailWord_3854948) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3854954 : List Nat := [3, 1, 3, 2, 1, 1, 1, 2, 9]
def baseStart_3854954 : Nat := 118140960795 + 3854954 * 2 ^ 59
def prefixEnd_3854954 : Nat := 4983230072969 + 3 ^ 40 * 3854954 * 2
def baseEnd_3854954 : Nat := 219938255885823967605155

theorem tailTrace_3854954 : CollatzResearch.WordTrace tailWord_3854954 prefixEnd_3854954 219938255885823967605155 := by
  unfold tailWord_3854954
  simp only [CollatzResearch.WordTrace]
  refine ⟨35150430819041876643124979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 93734482184111671048333277 35150430819041876643124979)
  ·
    refine ⟨52725646228562814964687469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35150430819041876643124979 52725646228562814964687469)
    ·
      refine ⟨19772117335711055611757801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 52725646228562814964687469 19772117335711055611757801)
      ·
        refine ⟨14829088001783291708818351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19772117335711055611757801 14829088001783291708818351)
        ·
          refine ⟨22243632002674937563227527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14829088001783291708818351 22243632002674937563227527)
          ·
            refine ⟨33365448004012406344841291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22243632002674937563227527 33365448004012406344841291)
            ·
              refine ⟨50048172006018609517261937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33365448004012406344841291 50048172006018609517261937)
              ·
                refine ⟨37536129004513957137946453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 50048172006018609517261937 37536129004513957137946453)
                ·
                  refine ⟨219938255885823967605155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 37536129004513957137946453 219938255885823967605155)
                  ·
                    rfl

theorem cell23_3854954_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 1, 2, 9].length) (baseStart_3854954 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3854954 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3854954 prefixEnd_3854954 := by exact prefixLift 3854954
  have htrace : WordTrace (prefixWord ++ tailWord_3854954) baseStart_3854954 baseEnd_3854954 := by
    simpa [prefixWord, tailWord_3854954, baseEnd_3854954] using wordTrace_append hprefix tailTrace_3854954
  have hstable : (prefixWord ++ tailWord_3854954).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3854954).length < 2 ^ (prefixWord ++ tailWord_3854954).sum := by decide
  have hdescent : baseEnd_3854954 < baseStart_3854954 := by decide
  rcases family_descends (prefixWord ++ tailWord_3854954) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3854981 : List Nat := [1, 3, 1, 1, 4, 2, 2, 1, 2, 3, 3]
def baseStart_3854981 : Nat := 118140960795 + 3854981 * 2 ^ 59
def prefixEnd_3854981 : Nat := 4983230072969 + 3 ^ 40 * 3854981 * 2
def baseEnd_3854981 : Nat := 1979458166950087102808771

theorem tailTrace_3854981 : CollatzResearch.WordTrace tailWord_3854981 prefixEnd_3854981 1979458166950087102808771 := by
  unfold tailWord_3854981
  simp only [CollatzResearch.WordTrace]
  refine ⟨140602708047069690183732797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93735138698046460122488531 140602708047069690183732797)
  ·
    refine ⟨52726015517651133818899799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 140602708047069690183732797 52726015517651133818899799)
    ·
      refine ⟨79089023276476700728349699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52726015517651133818899799 79089023276476700728349699)
      ·
        refine ⟨118633534914715051092524549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79089023276476700728349699 118633534914715051092524549)
        ·
          refine ⟨22243787796509072079848353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 118633534914715051092524549 22243787796509072079848353)
          ·
            refine ⟨16682840847381804059886265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22243787796509072079848353 16682840847381804059886265)
            ·
              refine ⟨12512130635536353044914699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16682840847381804059886265 12512130635536353044914699)
              ·
                refine ⟨18768195953304529567372049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12512130635536353044914699 18768195953304529567372049)
                ·
                  refine ⟨14076146964978397175529037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18768195953304529567372049 14076146964978397175529037)
                  ·
                    refine ⟨5278555111866898940823389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14076146964978397175529037 5278555111866898940823389)
                    ·
                      refine ⟨1979458166950087102808771, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5278555111866898940823389 1979458166950087102808771)
                      ·
                        rfl

theorem cell23_3854981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 2, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 2, 2, 1, 2, 3, 3].length) (baseStart_3854981 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3854981 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3854981 prefixEnd_3854981 := by exact prefixLift 3854981
  have htrace : WordTrace (prefixWord ++ tailWord_3854981) baseStart_3854981 baseEnd_3854981 := by
    simpa [prefixWord, tailWord_3854981, baseEnd_3854981] using wordTrace_append hprefix tailTrace_3854981
  have hstable : (prefixWord ++ tailWord_3854981).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3854981).length < 2 ^ (prefixWord ++ tailWord_3854981).sum := by decide
  have hdescent : baseEnd_3854981 < baseStart_3854981 := by decide
  rcases family_descends (prefixWord ++ tailWord_3854981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3855022 : List Nat := [4, 1, 4, 1, 1, 2, 3, 2, 5]
def baseStart_3855022 : Nat := 118140960795 + 3855022 * 2 ^ 59
def prefixEnd_3855022 : Nat := 4983230072969 + 3 ^ 40 * 3855022 * 2
def baseEnd_3855022 : Nat := 219942135517435715821787

theorem tailTrace_3855022 : CollatzResearch.WordTrace tailWord_3855022 prefixEnd_3855022 219942135517435715821787 := by
  unfold tailWord_3855022
  simp only [CollatzResearch.WordTrace]
  refine ⟨17575525429990144273246915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 93736135626614102790650213 17575525429990144273246915)
  ·
    refine ⟨26363288144985216409870373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17575525429990144273246915 26363288144985216409870373)
    ·
      refine ⟨4943116527184728076850695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 26363288144985216409870373 4943116527184728076850695)
      ·
        refine ⟨7414674790777092115276043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4943116527184728076850695 7414674790777092115276043)
        ·
          refine ⟨11122012186165638172914065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7414674790777092115276043 11122012186165638172914065)
          ·
            refine ⟨8341509139624228629685549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11122012186165638172914065 8341509139624228629685549)
            ·
              refine ⟨3128065927359085736132081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8341509139624228629685549 3128065927359085736132081)
              ·
                refine ⟨2346049445519314302099061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3128065927359085736132081 2346049445519314302099061)
                ·
                  refine ⟨219942135517435715821787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2346049445519314302099061 219942135517435715821787)
                  ·
                    rfl

theorem cell23_3855022_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 2, 3, 2, 5].length) (baseStart_3855022 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3855022 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3855022 prefixEnd_3855022 := by exact prefixLift 3855022
  have htrace : WordTrace (prefixWord ++ tailWord_3855022) baseStart_3855022 baseEnd_3855022 := by
    simpa [prefixWord, tailWord_3855022, baseEnd_3855022] using wordTrace_append hprefix tailTrace_3855022
  have hstable : (prefixWord ++ tailWord_3855022).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3855022).length < 2 ^ (prefixWord ++ tailWord_3855022).sum := by decide
  have hdescent : baseEnd_3855022 < baseStart_3855022 := by decide
  rcases family_descends (prefixWord ++ tailWord_3855022) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3855038 : List Nat := [4, 2, 1, 1, 2, 1, 2, 1, 1, 6, 2]
def baseStart_3855038 : Nat := 118140960795 + 3855038 * 2 ^ 59
def prefixEnd_3855038 : Nat := 4983230072969 + 3 ^ 40 * 3855038 * 2
def baseEnd_3855038 : Nat := 1979487435347393379796009

theorem tailTrace_3855038 : CollatzResearch.WordTrace tailWord_3855038 prefixEnd_3855038 1979487435347393379796009 := by
  unfold tailWord_3855038
  simp only [CollatzResearch.WordTrace]
  refine ⟨17575598375982898614819721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 93736524671908792612371845 17575598375982898614819721)
  ·
    refine ⟨13181698781987173961114791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17575598375982898614819721 13181698781987173961114791)
    ·
      refine ⟨19772548172980760941672187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13181698781987173961114791 19772548172980760941672187)
      ·
        refine ⟨29658822259471141412508281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19772548172980760941672187 29658822259471141412508281)
        ·
          refine ⟨22244116694603356059381211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29658822259471141412508281 22244116694603356059381211)
          ·
            refine ⟨33366175041905034089071817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22244116694603356059381211 33366175041905034089071817)
            ·
              refine ⟨25024631281428775566803863, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33366175041905034089071817 25024631281428775566803863)
              ·
                refine ⟨37536946922143163350205795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25024631281428775566803863 37536946922143163350205795)
                ·
                  refine ⟨56305420383214745025308693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37536946922143163350205795 56305420383214745025308693)
                  ·
                    refine ⟨2639316580463191173061345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 56305420383214745025308693 2639316580463191173061345)
                    ·
                      refine ⟨1979487435347393379796009, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2639316580463191173061345 1979487435347393379796009)
                      ·
                        rfl

theorem cell23_3855038_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 2, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 2, 1, 1, 6, 2].length) (baseStart_3855038 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3855038 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3855038 prefixEnd_3855038 := by exact prefixLift 3855038
  have htrace : WordTrace (prefixWord ++ tailWord_3855038) baseStart_3855038 baseEnd_3855038 := by
    simpa [prefixWord, tailWord_3855038, baseEnd_3855038] using wordTrace_append hprefix tailTrace_3855038
  have hstable : (prefixWord ++ tailWord_3855038).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3855038).length < 2 ^ (prefixWord ++ tailWord_3855038).sum := by decide
  have hdescent : baseEnd_3855038 < baseStart_3855038 := by decide
  rcases family_descends (prefixWord ++ tailWord_3855038) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3855088 : List Nat := [2, 1, 1, 1, 3, 1, 4, 3, 3, 1, 3]
def baseStart_3855088 : Nat := 118140960795 + 3855088 * 2 ^ 59
def prefixEnd_3855088 : Nat := 4983230072969 + 3 ^ 40 * 3855088 * 2
def baseEnd_3855088 : Nat := 1979513109380118184170779

theorem tailTrace_3855088 : CollatzResearch.WordTrace tailWord_3855088 prefixEnd_3855088 1979513109380118184170779 := by
  unfold tailWord_3855088
  simp only [CollatzResearch.WordTrace]
  refine ⟨70303305328841023728938959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93737740438454698305251945 70303305328841023728938959)
  ·
    refine ⟨105454957993261535593408439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70303305328841023728938959 105454957993261535593408439)
    ·
      refine ⟨158182436989892303390112659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105454957993261535593408439 158182436989892303390112659)
      ·
        refine ⟨237273655484838455085168989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 158182436989892303390112659 237273655484838455085168989)
        ·
          refine ⟨88977620806814420656938371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 237273655484838455085168989 88977620806814420656938371)
          ·
            refine ⟨133466431210221630985407557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 88977620806814420656938371 133466431210221630985407557)
            ·
              refine ⟨25024955851916555809763917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 133466431210221630985407557 25024955851916555809763917)
              ·
                refine ⟨9384358444468708428661469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25024955851916555809763917 9384358444468708428661469)
                ·
                  refine ⟨3519134416675765660748051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9384358444468708428661469 3519134416675765660748051)
                  ·
                    refine ⟨5278701625013648491122077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3519134416675765660748051 5278701625013648491122077)
                    ·
                      refine ⟨1979513109380118184170779, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5278701625013648491122077 1979513109380118184170779)
                      ·
                        rfl

theorem cell23_3855088_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 4, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 4, 3, 3, 1, 3].length) (baseStart_3855088 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3855088 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3855088 prefixEnd_3855088 := by exact prefixLift 3855088
  have htrace : WordTrace (prefixWord ++ tailWord_3855088) baseStart_3855088 baseEnd_3855088 := by
    simpa [prefixWord, tailWord_3855088, baseEnd_3855088] using wordTrace_append hprefix tailTrace_3855088
  have hstable : (prefixWord ++ tailWord_3855088).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3855088).length < 2 ^ (prefixWord ++ tailWord_3855088).sum := by decide
  have hdescent : baseEnd_3855088 < baseStart_3855088 := by decide
  rcases family_descends (prefixWord ++ tailWord_3855088) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3855098 : List Nat := [3, 1, 1, 1, 1, 3, 2, 2, 4, 3, 2]
def baseStart_3855098 : Nat := 118140960795 + 3855098 * 2 ^ 59
def prefixEnd_3855098 : Nat := 4983230072969 + 3 ^ 40 * 3855098 * 2
def baseEnd_3855098 : Nat := 1979518244186663145045733

theorem tailTrace_3855098 : CollatzResearch.WordTrace tailWord_3855098 prefixEnd_3855098 1979518244186663145045733 := by
  unfold tailWord_3855098
  simp only [CollatzResearch.WordTrace]
  refine ⟨35151743846911454791435487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 93737983591763879443827965 35151743846911454791435487)
  ·
    refine ⟨52727615770367182187153231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35151743846911454791435487 52727615770367182187153231)
    ·
      refine ⟨79091423655550773280729847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52727615770367182187153231 79091423655550773280729847)
      ·
        refine ⟨118637135483326159921094771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79091423655550773280729847 118637135483326159921094771)
        ·
          refine ⟨177955703224989239881642157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 118637135483326159921094771 177955703224989239881642157)
          ·
            refine ⟨66733388709370964955615809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 177955703224989239881642157 66733388709370964955615809)
            ·
              refine ⟨50050041532028223716711857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 66733388709370964955615809 50050041532028223716711857)
              ·
                refine ⟨37537531149021167787533893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 50050041532028223716711857 37537531149021167787533893)
                ·
                  refine ⟨7038287090441468960162605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 37537531149021167787533893 7038287090441468960162605)
                  ·
                    refine ⟨2639357658915550860060977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7038287090441468960162605 2639357658915550860060977)
                    ·
                      refine ⟨1979518244186663145045733, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2639357658915550860060977 1979518244186663145045733)
                      ·
                        rfl

theorem cell23_3855098_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 2, 2, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 2, 2, 4, 3, 2].length) (baseStart_3855098 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3855098 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3855098 prefixEnd_3855098 := by exact prefixLift 3855098
  have htrace : WordTrace (prefixWord ++ tailWord_3855098) baseStart_3855098 baseEnd_3855098 := by
    simpa [prefixWord, tailWord_3855098, baseEnd_3855098] using wordTrace_append hprefix tailTrace_3855098
  have hstable : (prefixWord ++ tailWord_3855098).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3855098).length < 2 ^ (prefixWord ++ tailWord_3855098).sum := by decide
  have hdescent : baseEnd_3855098 < baseStart_3855098 := by decide
  rcases family_descends (prefixWord ++ tailWord_3855098) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3855108 : List Nat := [2, 3, 2, 2, 1, 1, 2, 4, 1, 5]
def baseStart_3855108 : Nat := 118140960795 + 3855108 * 2 ^ 59
def prefixEnd_3855108 : Nat := 4983230072969 + 3 ^ 40 * 3855108 * 2
def baseEnd_3855108 : Nat := 659841126331069368640229

theorem tailTrace_3855108 : CollatzResearch.WordTrace tailWord_3855108 prefixEnd_3855108 659841126331069368640229 := by
  unfold tailWord_3855108
  simp only [CollatzResearch.WordTrace]
  refine ⟨70303670058804795436802989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93738226745073060582403985 70303670058804795436802989)
  ·
    refine ⟨26363876272051798288801121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 70303670058804795436802989 26363876272051798288801121)
    ·
      refine ⟨19772907204038848716600841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26363876272051798288801121 19772907204038848716600841)
      ·
        refine ⟨14829680403029136537450631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19772907204038848716600841 14829680403029136537450631)
        ·
          refine ⟨22244520604543704806175947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14829680403029136537450631 22244520604543704806175947)
          ·
            refine ⟨33366780906815557209263921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22244520604543704806175947 33366780906815557209263921)
            ·
              refine ⟨25025085680111667906947941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33366780906815557209263921 25025085680111667906947941)
              ·
                refine ⟨4692203565020937732552739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25025085680111667906947941 4692203565020937732552739)
                ·
                  refine ⟨7038305347531406598829109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4692203565020937732552739 7038305347531406598829109)
                  ·
                    refine ⟨659841126331069368640229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7038305347531406598829109 659841126331069368640229)
                    ·
                      rfl

theorem cell23_3855108_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 2, 4, 1, 5].length) (baseStart_3855108 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3855108 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3855108 prefixEnd_3855108 := by exact prefixLift 3855108
  have htrace : WordTrace (prefixWord ++ tailWord_3855108) baseStart_3855108 baseEnd_3855108 := by
    simpa [prefixWord, tailWord_3855108, baseEnd_3855108] using wordTrace_append hprefix tailTrace_3855108
  have hstable : (prefixWord ++ tailWord_3855108).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3855108).length < 2 ^ (prefixWord ++ tailWord_3855108).sum := by decide
  have hdescent : baseEnd_3855108 < baseStart_3855108 := by decide
  rcases family_descends (prefixWord ++ tailWord_3855108) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3855121 : List Nat := [1, 2, 2, 1, 1, 3, 4, 2, 1, 6]
def baseStart_3855121 : Nat := 118140960795 + 3855121 * 2 ^ 59
def prefixEnd_3855121 : Nat := 4983230072969 + 3 ^ 40 * 3855121 * 2
def baseEnd_3855121 : Nat := 659843351413905518352709

theorem tailTrace_3855121 : CollatzResearch.WordTrace tailWord_3855121 prefixEnd_3855121 659843351413905518352709 := by
  unfold tailWord_3855121
  simp only [CollatzResearch.WordTrace]
  refine ⟨140607814266562494093829217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93738542844374996062552811 140607814266562494093829217)
  ·
    refine ⟨105455860699921870570371913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 140607814266562494093829217 105455860699921870570371913)
    ·
      refine ⟨79091895524941402927778935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 105455860699921870570371913 79091895524941402927778935)
      ·
        refine ⟨118637843287412104391668403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79091895524941402927778935 118637843287412104391668403)
        ·
          refine ⟨177956764931118156587502605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 118637843287412104391668403 177956764931118156587502605)
          ·
            refine ⟨66733786849169308720313477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 177956764931118156587502605 66733786849169308720313477)
            ·
              refine ⟨12512585034219245385058777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 66733786849169308720313477 12512585034219245385058777)
              ·
                refine ⟨9384438775664434038794083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12512585034219245385058777 9384438775664434038794083)
                ·
                  refine ⟨14076658163496651058191125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9384438775664434038794083 14076658163496651058191125)
                  ·
                    refine ⟨659843351413905518352709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 14076658163496651058191125 659843351413905518352709)
                    ·
                      rfl

theorem cell23_3855121_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 6].length) (baseStart_3855121 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3855121 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3855121 prefixEnd_3855121 := by exact prefixLift 3855121
  have htrace : WordTrace (prefixWord ++ tailWord_3855121) baseStart_3855121 baseEnd_3855121 := by
    simpa [prefixWord, tailWord_3855121, baseEnd_3855121] using wordTrace_append hprefix tailTrace_3855121
  have hstable : (prefixWord ++ tailWord_3855121).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3855121).length < 2 ^ (prefixWord ++ tailWord_3855121).sum := by decide
  have hdescent : baseEnd_3855121 < baseStart_3855121 := by decide
  rcases family_descends (prefixWord ++ tailWord_3855121) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3855141 : List Nat := [1, 3, 1, 2, 3, 1, 2, 2, 1, 1, 6]
def baseStart_3855141 : Nat := 118140960795 + 3855141 * 2 ^ 59
def prefixEnd_3855141 : Nat := 4983230072969 + 3 ^ 40 * 3855141 * 2
def baseEnd_3855141 : Nat := 1979540323854806476808035

theorem tailTrace_3855141 : CollatzResearch.WordTrace tailWord_3855141 prefixEnd_3855141 1979540323854806476808035 := by
  unfold tailWord_3855141
  simp only [CollatzResearch.WordTrace]
  refine ⟨140608543726490037509557277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93739029150993358339704851 140608543726490037509557277)
  ·
    refine ⟨52728203897433764066083979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 140608543726490037509557277 52728203897433764066083979)
    ·
      refine ⟨79092305846150646099125969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52728203897433764066083979 79092305846150646099125969)
      ·
        refine ⟨59319229384612984574344477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 79092305846150646099125969 59319229384612984574344477)
        ·
          refine ⟨22244711019229869215379179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 59319229384612984574344477 22244711019229869215379179)
          ·
            refine ⟨33367066528844803823068769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22244711019229869215379179 33367066528844803823068769)
            ·
              refine ⟨25025299896633602867301577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33367066528844803823068769 25025299896633602867301577)
              ·
                refine ⟨18768974922475202150476183, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25025299896633602867301577 18768974922475202150476183)
                ·
                  refine ⟨28153462383712803225714275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18768974922475202150476183 28153462383712803225714275)
                  ·
                    refine ⟨42230193575569204838571413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 28153462383712803225714275 42230193575569204838571413)
                    ·
                      refine ⟨1979540323854806476808035, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 42230193575569204838571413 1979540323854806476808035)
                      ·
                        rfl

theorem cell23_3855141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 2, 2, 1, 1, 6].length) (baseStart_3855141 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3855141 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3855141 prefixEnd_3855141 := by exact prefixLift 3855141
  have htrace : WordTrace (prefixWord ++ tailWord_3855141) baseStart_3855141 baseEnd_3855141 := by
    simpa [prefixWord, tailWord_3855141, baseEnd_3855141] using wordTrace_append hprefix tailTrace_3855141
  have hstable : (prefixWord ++ tailWord_3855141).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3855141).length < 2 ^ (prefixWord ++ tailWord_3855141).sum := by decide
  have hdescent : baseEnd_3855141 < baseStart_3855141 := by decide
  rcases family_descends (prefixWord ++ tailWord_3855141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3855211 : List Nat := [1, 1, 1, 1, 2, 2, 4, 3, 2, 6]
def baseStart_3855211 : Nat := 118140960795 + 3855211 * 2 ^ 59
def prefixEnd_3855211 : Nat := 4983230072969 + 3 ^ 40 * 3855211 * 2
def baseEnd_3855211 : Nat := 659858755833540400977571

theorem tailTrace_3855211 : CollatzResearch.WordTrace tailWord_3855211 prefixEnd_3855211 659858755833540400977571 := by
  unfold tailWord_3855211
  simp only [CollatzResearch.WordTrace]
  refine ⟨140611096836236439464605487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93740731224157626309736991 140611096836236439464605487)
  ·
    refine ⟨210916645254354659196908231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140611096836236439464605487 210916645254354659196908231)
    ·
      refine ⟨316374967881531988795362347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 210916645254354659196908231 316374967881531988795362347)
      ·
        refine ⟨474562451822297983193043521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 316374967881531988795362347 474562451822297983193043521)
        ·
          refine ⟨355921838866723487394782641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 474562451822297983193043521 355921838866723487394782641)
          ·
            refine ⟨266941379150042615546086981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 355921838866723487394782641 266941379150042615546086981)
            ·
              refine ⟨50051508590632990414891309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 266941379150042615546086981 50051508590632990414891309)
              ·
                refine ⟨18769315721487371405584241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 50051508590632990414891309 18769315721487371405584241)
                ·
                  refine ⟨14076986791115528554188181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18769315721487371405584241 14076986791115528554188181)
                  ·
                    refine ⟨659858755833540400977571, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 14076986791115528554188181 659858755833540400977571)
                    ·
                      rfl

theorem cell23_3855211_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 4, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 4, 3, 2, 6].length) (baseStart_3855211 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3855211 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3855211 prefixEnd_3855211 := by exact prefixLift 3855211
  have htrace : WordTrace (prefixWord ++ tailWord_3855211) baseStart_3855211 baseEnd_3855211 := by
    simpa [prefixWord, tailWord_3855211, baseEnd_3855211] using wordTrace_append hprefix tailTrace_3855211
  have hstable : (prefixWord ++ tailWord_3855211).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3855211).length < 2 ^ (prefixWord ++ tailWord_3855211).sum := by decide
  have hdescent : baseEnd_3855211 < baseStart_3855211 := by decide
  rcases family_descends (prefixWord ++ tailWord_3855211) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3855235 : List Nat := [1, 1, 1, 3, 4, 1, 3, 2, 1, 4, 2]
def baseStart_3855235 : Nat := 118140960795 + 3855235 * 2 ^ 59
def prefixEnd_3855235 : Nat := 4983230072969 + 3 ^ 40 * 3855235 * 2
def baseEnd_3855235 : Nat := 1979588591036329109032603

theorem tailTrace_3855235 : CollatzResearch.WordTrace tailWord_3855235 prefixEnd_3855235 1979588591036329109032603 := by
  unfold tailWord_3855235
  simp only [CollatzResearch.WordTrace]
  refine ⟨140611972188149491563479159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93741314792099661042319439 140611972188149491563479159)
  ·
    refine ⟨210917958282224237345218739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140611972188149491563479159 210917958282224237345218739)
    ·
      refine ⟨316376937423336356017828109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 210917958282224237345218739 316376937423336356017828109)
      ·
        refine ⟨118641351533751133506685541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 316376937423336356017828109 118641351533751133506685541)
        ·
          refine ⟨22245253412578337532503539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 118641351533751133506685541 22245253412578337532503539)
          ·
            refine ⟨33367880118867506298755309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22245253412578337532503539 33367880118867506298755309)
            ·
              refine ⟨12512955044575314862033241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33367880118867506298755309 12512955044575314862033241)
              ·
                refine ⟨9384716283431486146524931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12512955044575314862033241 9384716283431486146524931)
                ·
                  refine ⟨14077074425147229219787397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9384716283431486146524931 14077074425147229219787397)
                  ·
                    refine ⟨2639451454715105478710137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 14077074425147229219787397 2639451454715105478710137)
                    ·
                      refine ⟨1979588591036329109032603, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2639451454715105478710137 1979588591036329109032603)
                      ·
                        rfl

theorem cell23_3855235_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 3, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 3, 2, 1, 4, 2].length) (baseStart_3855235 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3855235 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3855235 prefixEnd_3855235 := by exact prefixLift 3855235
  have htrace : WordTrace (prefixWord ++ tailWord_3855235) baseStart_3855235 baseEnd_3855235 := by
    simpa [prefixWord, tailWord_3855235, baseEnd_3855235] using wordTrace_append hprefix tailTrace_3855235
  have hstable : (prefixWord ++ tailWord_3855235).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3855235).length < 2 ^ (prefixWord ++ tailWord_3855235).sum := by decide
  have hdescent : baseEnd_3855235 < baseStart_3855235 := by decide
  rcases family_descends (prefixWord ++ tailWord_3855235) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3855239 : List Nat := [1, 1, 4, 2, 3, 2, 3, 1, 1, 3, 2]
def baseStart_3855239 : Nat := 118140960795 + 3855239 * 2 ^ 59
def prefixEnd_3855239 : Nat := 4983230072969 + 3 ^ 40 * 3855239 * 2
def baseEnd_3855239 : Nat := 1979590644958947093382585

theorem tailTrace_3855239 : CollatzResearch.WordTrace tailWord_3855239 prefixEnd_3855239 1979590644958947093382585 := by
  unfold tailWord_3855239
  simp only [CollatzResearch.WordTrace]
  refine ⟨140612118080135000246624771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93741412053423333497749847 140612118080135000246624771)
  ·
    refine ⟨210918177120202500369937157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140612118080135000246624771 210918177120202500369937157)
    ·
      refine ⟨39547158210037968819363217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 210918177120202500369937157 39547158210037968819363217)
      ·
        refine ⟨29660368657528476614522413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39547158210037968819363217 29660368657528476614522413)
        ·
          refine ⟨11122638246573178730445905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29660368657528476614522413 11122638246573178730445905)
          ·
            refine ⟨8341978684929884047834429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11122638246573178730445905 8341978684929884047834429)
            ·
              refine ⟨3128242006848706517937911, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8341978684929884047834429 3128242006848706517937911)
              ·
                refine ⟨4692363010273059776906867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3128242006848706517937911 4692363010273059776906867)
                ·
                  refine ⟨7038544515409589665360301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4692363010273059776906867 7038544515409589665360301)
                  ·
                    refine ⟨2639454193278596124510113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7038544515409589665360301 2639454193278596124510113)
                    ·
                      refine ⟨1979590644958947093382585, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2639454193278596124510113 1979590644958947093382585)
                      ·
                        rfl

theorem cell23_3855239_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 2, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 2, 3, 1, 1, 3, 2].length) (baseStart_3855239 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3855239 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3855239 prefixEnd_3855239 := by exact prefixLift 3855239
  have htrace : WordTrace (prefixWord ++ tailWord_3855239) baseStart_3855239 baseEnd_3855239 := by
    simpa [prefixWord, tailWord_3855239, baseEnd_3855239] using wordTrace_append hprefix tailTrace_3855239
  have hstable : (prefixWord ++ tailWord_3855239).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3855239).length < 2 ^ (prefixWord ++ tailWord_3855239).sum := by decide
  have hdescent : baseEnd_3855239 < baseStart_3855239 := by decide
  rcases family_descends (prefixWord ++ tailWord_3855239) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3855265 : List Nat := [1, 2, 3, 4, 1, 2, 1, 1, 2, 2, 4]
def baseStart_3855265 : Nat := 118140960795 + 3855265 * 2 ^ 59
def prefixEnd_3855265 : Nat := 4983230072969 + 3 ^ 40 * 3855265 * 2
def baseEnd_3855265 : Nat := 1979603995455963991657465

theorem tailTrace_3855265 : CollatzResearch.WordTrace tailWord_3855265 prefixEnd_3855265 1979603995455963991657465 := by
  unfold tailWord_3855265
  simp only [CollatzResearch.WordTrace]
  refine ⟨140613066378040806687071249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93742044252027204458047499 140613066378040806687071249)
  ·
    refine ⟨105459799783530605015303437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 140613066378040806687071249 105459799783530605015303437)
    ·
      refine ⟨39547424918823976880738789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 105459799783530605015303437 39547424918823976880738789)
      ·
        refine ⟨7415142172279495665138523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 39547424918823976880738789 7415142172279495665138523)
        ·
          refine ⟨11122713258419243497707785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7415142172279495665138523 11122713258419243497707785)
          ·
            refine ⟨8342034943814432623280839, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11122713258419243497707785 8342034943814432623280839)
            ·
              refine ⟨12513052415721648934921259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8342034943814432623280839 12513052415721648934921259)
              ·
                refine ⟨18769578623582473402381889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12513052415721648934921259 18769578623582473402381889)
                ·
                  refine ⟨14077183967686855051786417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18769578623582473402381889 14077183967686855051786417)
                  ·
                    refine ⟨10557887975765141288839813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14077183967686855051786417 10557887975765141288839813)
                    ·
                      refine ⟨1979603995455963991657465, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10557887975765141288839813 1979603995455963991657465)
                      ·
                        rfl

theorem cell23_3855265_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 2, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 2, 1, 1, 2, 2, 4].length) (baseStart_3855265 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3855265 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3855265 prefixEnd_3855265 := by exact prefixLift 3855265
  have htrace : WordTrace (prefixWord ++ tailWord_3855265) baseStart_3855265 baseEnd_3855265 := by
    simpa [prefixWord, tailWord_3855265, baseEnd_3855265] using wordTrace_append hprefix tailTrace_3855265
  have hstable : (prefixWord ++ tailWord_3855265).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3855265).length < 2 ^ (prefixWord ++ tailWord_3855265).sum := by decide
  have hdescent : baseEnd_3855265 < baseStart_3855265 := by decide
  rcases family_descends (prefixWord ++ tailWord_3855265) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3855288 : List Nat := [2, 1, 2, 1, 2, 5, 1, 1, 1, 7]
def baseStart_3855288 : Nat := 118140960795 + 3855288 * 2 ^ 59
def prefixEnd_3855288 : Nat := 4983230072969 + 3 ^ 40 * 3855288 * 2
def baseEnd_3855288 : Nat := 659871935170339133889953

theorem tailTrace_3855288 : CollatzResearch.WordTrace tailWord_3855288 prefixEnd_3855288 659871935170339133889953 := by
  unfold tailWord_3855288
  simp only [CollatzResearch.WordTrace]
  refine ⟨70306952628478740807579259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93742603504638321076772345 70306952628478740807579259)
  ·
    refine ⟨105460428942718111211368889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70306952628478740807579259 105460428942718111211368889)
    ·
      refine ⟨79095321707038583408526667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 105460428942718111211368889 79095321707038583408526667)
      ·
        refine ⟨118642982560557875112790001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79095321707038583408526667 118642982560557875112790001)
        ·
          refine ⟨88982236920418406334592501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 118642982560557875112790001 88982236920418406334592501)
          ·
            refine ⟨8342084711289225593868047, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 88982236920418406334592501 8342084711289225593868047)
            ·
              refine ⟨12513127066933838390802071, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8342084711289225593868047 12513127066933838390802071)
              ·
                refine ⟨18769690600400757586203107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12513127066933838390802071 18769690600400757586203107)
                ·
                  refine ⟨28154535900601136379304661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18769690600400757586203107 28154535900601136379304661)
                  ·
                    refine ⟨659871935170339133889953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 28154535900601136379304661 659871935170339133889953)
                    ·
                      rfl

theorem cell23_3855288_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 5, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 5, 1, 1, 1, 7].length) (baseStart_3855288 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3855288 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3855288 prefixEnd_3855288 := by exact prefixLift 3855288
  have htrace : WordTrace (prefixWord ++ tailWord_3855288) baseStart_3855288 baseEnd_3855288 := by
    simpa [prefixWord, tailWord_3855288, baseEnd_3855288] using wordTrace_append hprefix tailTrace_3855288
  have hstable : (prefixWord ++ tailWord_3855288).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3855288).length < 2 ^ (prefixWord ++ tailWord_3855288).sum := by decide
  have hdescent : baseEnd_3855288 < baseStart_3855288 := by decide
  rcases family_descends (prefixWord ++ tailWord_3855288) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3855291 : List Nat := [1, 1, 1, 1, 1, 2, 2, 2, 2, 2, 8]
def baseStart_3855291 : Nat := 118140960795 + 3855291 * 2 ^ 59
def prefixEnd_3855291 : Nat := 4983230072969 + 3 ^ 40 * 3855291 * 2
def baseEnd_3855291 : Nat := 1979617345952980889932345

theorem tailTrace_3855291 : CollatzResearch.WordTrace tailWord_3855291 prefixEnd_3855291 1979617345952980889932345 := by
  unfold tailWord_3855291
  simp only [CollatzResearch.WordTrace]
  refine ⟨140614014675946613127517727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93742676450631075418345151 140614014675946613127517727)
  ·
    refine ⟨210921022013919919691276591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140614014675946613127517727 210921022013919919691276591)
    ·
      refine ⟨316381533020879879536914887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 210921022013919919691276591 316381533020879879536914887)
      ·
        refine ⟨474572299531319819305372331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 316381533020879879536914887 474572299531319819305372331)
        ·
          refine ⟨711858449296979728958058497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 474572299531319819305372331 711858449296979728958058497)
          ·
            refine ⟨533893836972734796718543873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 711858449296979728958058497 533893836972734796718543873)
            ·
              refine ⟨400420377729551097538907905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 533893836972734796718543873 400420377729551097538907905)
              ·
                refine ⟨300315283297163323154180929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 400420377729551097538907905 300315283297163323154180929)
                ·
                  refine ⟨225236462472872492365635697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 300315283297163323154180929 225236462472872492365635697)
                  ·
                    refine ⟨168927346854654369274226773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 225236462472872492365635697 168927346854654369274226773)
                    ·
                      refine ⟨1979617345952980889932345, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 168927346854654369274226773 1979617345952980889932345)
                      ·
                        rfl

theorem cell23_3855291_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 2, 2, 8].length) (baseStart_3855291 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3855291 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3855291 prefixEnd_3855291 := by exact prefixLift 3855291
  have htrace : WordTrace (prefixWord ++ tailWord_3855291) baseStart_3855291 baseEnd_3855291 := by
    simpa [prefixWord, tailWord_3855291, baseEnd_3855291] using wordTrace_append hprefix tailTrace_3855291
  have hstable : (prefixWord ++ tailWord_3855291).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3855291).length < 2 ^ (prefixWord ++ tailWord_3855291).sum := by decide
  have hdescent : baseEnd_3855291 < baseStart_3855291 := by decide
  rcases family_descends (prefixWord ++ tailWord_3855291) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3855325 : List Nat := [1, 4, 3, 1, 2, 1, 1, 2, 1, 3, 4]
def baseStart_3855325 : Nat := 118140960795 + 3855325 * 2 ^ 59
def prefixEnd_3855325 : Nat := 4983230072969 + 3 ^ 40 * 3855325 * 2
def baseEnd_3855325 : Nat := 1979634804295233756907189

theorem tailTrace_3855325 : CollatzResearch.WordTrace tailWord_3855325 prefixEnd_3855325 1979634804295233756907189 := by
  unfold tailWord_3855325
  simp only [CollatzResearch.WordTrace]
  refine ⟨140615254757823436934255429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93743503171882291289503619 140615254757823436934255429)
  ·
    refine ⟨26365360267091894425172893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 140615254757823436934255429 26365360267091894425172893)
    ·
      refine ⟨9887010100159460409439835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26365360267091894425172893 9887010100159460409439835)
      ·
        refine ⟨14830515150239190614159753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9887010100159460409439835 14830515150239190614159753)
        ·
          refine ⟨11122886362679392960619815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14830515150239190614159753 11122886362679392960619815)
          ·
            refine ⟨16684329544019089440929723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11122886362679392960619815 16684329544019089440929723)
            ·
              refine ⟨25026494316028634161394585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16684329544019089440929723 25026494316028634161394585)
              ·
                refine ⟨18769870737021475621045939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25026494316028634161394585 18769870737021475621045939)
                ·
                  refine ⟨28154806105532213431568909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18769870737021475621045939 28154806105532213431568909)
                  ·
                    refine ⟨10558052289574580036838341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 28154806105532213431568909 10558052289574580036838341)
                    ·
                      refine ⟨1979634804295233756907189, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10558052289574580036838341 1979634804295233756907189)
                      ·
                        rfl

theorem cell23_3855325_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 1, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 1, 1, 2, 1, 3, 4].length) (baseStart_3855325 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3855325 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3855325 prefixEnd_3855325 := by exact prefixLift 3855325
  have htrace : WordTrace (prefixWord ++ tailWord_3855325) baseStart_3855325 baseEnd_3855325 := by
    simpa [prefixWord, tailWord_3855325, baseEnd_3855325] using wordTrace_append hprefix tailTrace_3855325
  have hstable : (prefixWord ++ tailWord_3855325).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3855325).length < 2 ^ (prefixWord ++ tailWord_3855325).sum := by decide
  have hdescent : baseEnd_3855325 < baseStart_3855325 := by decide
  rcases family_descends (prefixWord ++ tailWord_3855325) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3855345 : List Nat := [1, 2, 2, 2, 4, 1, 2, 1, 1, 4, 3]
def baseStart_3855345 : Nat := 118140960795 + 3855345 * 2 ^ 59
def prefixEnd_3855345 : Nat := 4983230072969 + 3 ^ 40 * 3855345 * 2
def baseEnd_3855345 : Nat := 1979645073908323678657097

theorem tailTrace_3855345 : CollatzResearch.WordTrace tailWord_3855345 prefixEnd_3855345 1979645073908323678657097 := by
  unfold tailWord_3855345
  simp only [CollatzResearch.WordTrace]
  refine ⟨140615984217750980349983489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93743989478500653566655659 140615984217750980349983489)
  ·
    refine ⟨105461988163313235262487617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 140615984217750980349983489 105461988163313235262487617)
    ·
      refine ⟨79096491122484926446865713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 105461988163313235262487617 79096491122484926446865713)
      ·
        refine ⟨59322368341863694835149285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 79096491122484926446865713 59322368341863694835149285)
        ·
          refine ⟨11122944064099442781590491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 59322368341863694835149285 11122944064099442781590491)
          ·
            refine ⟨16684416096149164172385737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11122944064099442781590491 16684416096149164172385737)
            ·
              refine ⟨12513312072111873129289303, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16684416096149164172385737 12513312072111873129289303)
              ·
                refine ⟨18769968108167809693933955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12513312072111873129289303 18769968108167809693933955)
                ·
                  refine ⟨28154952162251714540900933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18769968108167809693933955 28154952162251714540900933)
                  ·
                    refine ⟨5279053530422196476418925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 28154952162251714540900933 5279053530422196476418925)
                    ·
                      refine ⟨1979645073908323678657097, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5279053530422196476418925 1979645073908323678657097)
                      ·
                        rfl

theorem cell23_3855345_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 1, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 1, 2, 1, 1, 4, 3].length) (baseStart_3855345 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3855345 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3855345 prefixEnd_3855345 := by exact prefixLift 3855345
  have htrace : WordTrace (prefixWord ++ tailWord_3855345) baseStart_3855345 baseEnd_3855345 := by
    simpa [prefixWord, tailWord_3855345, baseEnd_3855345] using wordTrace_append hprefix tailTrace_3855345
  have hstable : (prefixWord ++ tailWord_3855345).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3855345).length < 2 ^ (prefixWord ++ tailWord_3855345).sum := by decide
  have hdescent : baseEnd_3855345 < baseStart_3855345 := by decide
  rcases family_descends (prefixWord ++ tailWord_3855345) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3855375 : List Nat := [1, 1, 2, 1, 1, 1, 2, 1, 9, 1, 3]
def baseStart_3855375 : Nat := 118140960795 + 3855375 * 2 ^ 59
def prefixEnd_3855375 : Nat := 4983230072969 + 3 ^ 40 * 3855375 * 2
def baseEnd_3855375 : Nat := 1979660478327958561281959

theorem tailTrace_3855375 : CollatzResearch.WordTrace tailWord_3855375 prefixEnd_3855375 1979660478327958561281959 := by
  unfold tailWord_3855375
  simp only [CollatzResearch.WordTrace]
  refine ⟨140617078407642295473575579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93744718938428196982383719 140617078407642295473575579)
  ·
    refine ⟨210925617611463443210363369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140617078407642295473575579 210925617611463443210363369)
    ·
      refine ⟨158194213208597582407772527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 210925617611463443210363369 158194213208597582407772527)
      ·
        refine ⟨237291319812896373611658791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 158194213208597582407772527 237291319812896373611658791)
        ·
          refine ⟨355936979719344560417488187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 237291319812896373611658791 355936979719344560417488187)
          ·
            refine ⟨533905469579016840626232281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 355936979719344560417488187 533905469579016840626232281)
            ·
              refine ⟨400429102184262630469674211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 533905469579016840626232281 400429102184262630469674211)
              ·
                refine ⟨600643653276393945704511317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 400429102184262630469674211 600643653276393945704511317)
                ·
                  refine ⟨3519396405916370775612371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 600643653276393945704511317 3519396405916370775612371)
                  ·
                    refine ⟨5279094608874556163418557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3519396405916370775612371 5279094608874556163418557)
                    ·
                      refine ⟨1979660478327958561281959, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5279094608874556163418557 1979660478327958561281959)
                      ·
                        rfl

theorem cell23_3855375_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 1, 9, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 1, 9, 1, 3].length) (baseStart_3855375 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3855375 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3855375 prefixEnd_3855375 := by exact prefixLift 3855375
  have htrace : WordTrace (prefixWord ++ tailWord_3855375) baseStart_3855375 baseEnd_3855375 := by
    simpa [prefixWord, tailWord_3855375, baseEnd_3855375] using wordTrace_append hprefix tailTrace_3855375
  have hstable : (prefixWord ++ tailWord_3855375).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3855375).length < 2 ^ (prefixWord ++ tailWord_3855375).sum := by decide
  have hdescent : baseEnd_3855375 < baseStart_3855375 := by decide
  rcases family_descends (prefixWord ++ tailWord_3855375) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3855385 : List Nat := [1, 2, 1, 2, 1, 1, 4, 1, 3, 5, 2]
def baseStart_3855385 : Nat := 118140960795 + 3855385 * 2 ^ 59
def prefixEnd_3855385 : Nat := 4983230072969 + 3 ^ 40 * 3855385 * 2
def baseEnd_3855385 : Nat := 1979665613134503522156913

theorem tailTrace_3855385 : CollatzResearch.WordTrace tailWord_3855385 prefixEnd_3855385 1979665613134503522156913 := by
  unfold tailWord_3855385
  simp only [CollatzResearch.WordTrace]
  refine ⟨140617443137606067181439609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93744962091737378120959739 140617443137606067181439609)
  ·
    refine ⟨105463082353204550386079707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 140617443137606067181439609 105463082353204550386079707)
    ·
      refine ⟨158194623529806825579119561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105463082353204550386079707 158194623529806825579119561)
      ·
        refine ⟨118645967647355119184339671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 158194623529806825579119561 118645967647355119184339671)
        ·
          refine ⟨177968951471032678776509507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 118645967647355119184339671 177968951471032678776509507)
          ·
            refine ⟨266953427206549018164764261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 177968951471032678776509507 266953427206549018164764261)
            ·
              refine ⟨50053767601227940905893299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 266953427206549018164764261 50053767601227940905893299)
              ·
                refine ⟨75080651401841911358839949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50053767601227940905893299 75080651401841911358839949)
                ·
                  refine ⟨28155244275690716759564981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 75080651401841911358839949 28155244275690716759564981)
                  ·
                    refine ⟨2639554150846004696209217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 28155244275690716759564981 2639554150846004696209217)
                    ·
                      refine ⟨1979665613134503522156913, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2639554150846004696209217 1979665613134503522156913)
                      ·
                        rfl

theorem cell23_3855385_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 4, 1, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 4, 1, 3, 5, 2].length) (baseStart_3855385 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3855385 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3855385 prefixEnd_3855385 := by exact prefixLift 3855385
  have htrace : WordTrace (prefixWord ++ tailWord_3855385) baseStart_3855385 baseEnd_3855385 := by
    simpa [prefixWord, tailWord_3855385, baseEnd_3855385] using wordTrace_append hprefix tailTrace_3855385
  have hstable : (prefixWord ++ tailWord_3855385).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3855385).length < 2 ^ (prefixWord ++ tailWord_3855385).sum := by decide
  have hdescent : baseEnd_3855385 < baseStart_3855385 := by decide
  rcases family_descends (prefixWord ++ tailWord_3855385) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3855395 : List Nat := [1, 1, 1, 4, 3, 3, 1, 1, 3, 5]
def baseStart_3855395 : Nat := 118140960795 + 3855395 * 2 ^ 59
def prefixEnd_3855395 : Nat := 4983230072969 + 3 ^ 40 * 3855395 * 2
def baseEnd_3855395 : Nat := 659890249313682827677289

theorem tailTrace_3855395 : CollatzResearch.WordTrace tailWord_3855395 prefixEnd_3855395 659890249313682827677289 := by
  unfold tailWord_3855395
  simp only [CollatzResearch.WordTrace]
  refine ⟨140617807867569838889303639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93745205245046559259535759 140617807867569838889303639)
  ·
    refine ⟨210926711801354758333955459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140617807867569838889303639 210926711801354758333955459)
    ·
      refine ⟨316390067702032137500933189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 210926711801354758333955459 316390067702032137500933189)
      ·
        refine ⟨59323137694131025781424973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 316390067702032137500933189 59323137694131025781424973)
        ·
          refine ⟨22246176635299134668034365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 59323137694131025781424973 22246176635299134668034365)
          ·
            refine ⟨8342316238237175500512887, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22246176635299134668034365 8342316238237175500512887)
            ·
              refine ⟨12513474357355763250769331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8342316238237175500512887 12513474357355763250769331)
              ·
                refine ⟨18770211536033644876153997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12513474357355763250769331 18770211536033644876153997)
                ·
                  refine ⟨7038829326012616828557749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18770211536033644876153997 7038829326012616828557749)
                  ·
                    refine ⟨659890249313682827677289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7038829326012616828557749 659890249313682827677289)
                    ·
                      rfl

theorem cell23_3855395_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 3, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 3, 1, 1, 3, 5].length) (baseStart_3855395 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3855395 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3855395 prefixEnd_3855395 := by exact prefixLift 3855395
  have htrace : WordTrace (prefixWord ++ tailWord_3855395) baseStart_3855395 baseEnd_3855395 := by
    simpa [prefixWord, tailWord_3855395, baseEnd_3855395] using wordTrace_append hprefix tailTrace_3855395
  have hstable : (prefixWord ++ tailWord_3855395).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3855395).length < 2 ^ (prefixWord ++ tailWord_3855395).sum := by decide
  have hdescent : baseEnd_3855395 < baseStart_3855395 := by decide
  rcases family_descends (prefixWord ++ tailWord_3855395) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3855409 : List Nat := [1, 2, 2, 3, 1, 2, 2, 5, 1, 1, 3]
def baseStart_3855409 : Nat := 118140960795 + 3855409 * 2 ^ 59
def prefixEnd_3855409 : Nat := 4983230072969 + 3 ^ 40 * 3855409 * 2
def baseEnd_3855409 : Nat := 1979677936670211428256803

theorem tailTrace_3855409 : CollatzResearch.WordTrace tailWord_3855409 prefixEnd_3855409 1979677936670211428256803 := by
  unfold tailWord_3855409
  simp only [CollatzResearch.WordTrace]
  refine ⟨140618318489519119280313281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93745545659679412853542187 140618318489519119280313281)
  ·
    refine ⟨105463738867139339460234961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 140618318489519119280313281 105463738867139339460234961)
    ·
      refine ⟨79097804150354504595176221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 105463738867139339460234961 79097804150354504595176221)
      ·
        refine ⟨29661676556382939223191083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 79097804150354504595176221 29661676556382939223191083)
        ·
          refine ⟨44492514834574408834786625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29661676556382939223191083 44492514834574408834786625)
          ·
            refine ⟨33369386125930806626089969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44492514834574408834786625 33369386125930806626089969)
            ·
              refine ⟨25027039594448104969567477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33369386125930806626089969 25027039594448104969567477)
              ·
                refine ⟨2346284961979509840896951, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 25027039594448104969567477 2346284961979509840896951)
                ·
                  refine ⟨3519427442969264761345427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2346284961979509840896951 3519427442969264761345427)
                  ·
                    refine ⟨5279141164453897142018141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3519427442969264761345427 5279141164453897142018141)
                    ·
                      refine ⟨1979677936670211428256803, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5279141164453897142018141 1979677936670211428256803)
                      ·
                        rfl

theorem cell23_3855409_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 2, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 2, 5, 1, 1, 3].length) (baseStart_3855409 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3855409 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3855409 prefixEnd_3855409 := by exact prefixLift 3855409
  have htrace : WordTrace (prefixWord ++ tailWord_3855409) baseStart_3855409 baseEnd_3855409 := by
    simpa [prefixWord, tailWord_3855409, baseEnd_3855409] using wordTrace_append hprefix tailTrace_3855409
  have hstable : (prefixWord ++ tailWord_3855409).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3855409).length < 2 ^ (prefixWord ++ tailWord_3855409).sum := by decide
  have hdescent : baseEnd_3855409 < baseStart_3855409 := by decide
  rcases family_descends (prefixWord ++ tailWord_3855409) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3855442 : List Nat := [3, 2, 2, 1, 3, 2, 2, 1, 1, 6]
def baseStart_3855442 : Nat := 118140960795 + 3855442 * 2 ^ 59
def prefixEnd_3855442 : Nat := 4983230072969 + 3 ^ 40 * 3855442 * 2
def baseEnd_3855442 : Nat := 659898293843936599714717

theorem tailTrace_3855442 : CollatzResearch.WordTrace tailWord_3855442 prefixEnd_3855442 659898293843936599714717 := by
  unfold tailWord_3855442
  simp only [CollatzResearch.WordTrace]
  refine ⟨35154880524599891479066145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 93746348065599710610843053 35154880524599891479066145)
  ·
    refine ⟨26366160393449918609299609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35154880524599891479066145 26366160393449918609299609)
    ·
      refine ⟨19774620295087438956974707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26366160393449918609299609 19774620295087438956974707)
      ·
        refine ⟨29661930442631158435462061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19774620295087438956974707 29661930442631158435462061)
        ·
          refine ⟨11123223915986684413298273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29661930442631158435462061 11123223915986684413298273)
          ·
            refine ⟨8342417936990013309973705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11123223915986684413298273 8342417936990013309973705)
            ·
              refine ⟨6256813452742509982480279, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8342417936990013309973705 6256813452742509982480279)
              ·
                refine ⟨9385220179113764973720419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6256813452742509982480279 9385220179113764973720419)
                ·
                  refine ⟨14077830268670647460580629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9385220179113764973720419 14077830268670647460580629)
                  ·
                    refine ⟨659898293843936599714717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 14077830268670647460580629 659898293843936599714717)
                    ·
                      rfl

theorem cell23_3855442_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 2, 2, 1, 1, 6].length) (baseStart_3855442 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3855442 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3855442 prefixEnd_3855442 := by exact prefixLift 3855442
  have htrace : WordTrace (prefixWord ++ tailWord_3855442) baseStart_3855442 baseEnd_3855442 := by
    simpa [prefixWord, tailWord_3855442, baseEnd_3855442] using wordTrace_append hprefix tailTrace_3855442
  have hstable : (prefixWord ++ tailWord_3855442).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3855442).length < 2 ^ (prefixWord ++ tailWord_3855442).sum := by decide
  have hdescent : baseEnd_3855442 < baseStart_3855442 := by decide
  rcases family_descends (prefixWord ++ tailWord_3855442) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3855452 : List Nat := [2, 2, 4, 1, 1, 1, 1, 3, 3, 2, 3]
def baseStart_3855452 : Nat := 118140960795 + 3855452 * 2 ^ 59
def prefixEnd_3855452 : Nat := 4983230072969 + 3 ^ 40 * 3855452 * 2
def baseEnd_3855452 : Nat := 1979700016338354760019105

theorem tailTrace_3855452 : CollatzResearch.WordTrace tailWord_3855452 prefixEnd_3855452 1979700016338354760019105 := by
  unfold tailWord_3855452
  simp only [CollatzResearch.WordTrace]
  refine ⟨70309943414181668812064305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93746591218908891749419073 70309943414181668812064305)
  ·
    refine ⟨52732457560636251609048229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70309943414181668812064305 52732457560636251609048229)
    ·
      refine ⟨9887335792619297176696543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 52732457560636251609048229 9887335792619297176696543)
      ·
        refine ⟨14831003688928945765044815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9887335792619297176696543 14831003688928945765044815)
        ·
          refine ⟨22246505533393418647567223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14831003688928945765044815 22246505533393418647567223)
          ·
            refine ⟨33369758300090127971350835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22246505533393418647567223 33369758300090127971350835)
            ·
              refine ⟨50054637450135191957026253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33369758300090127971350835 50054637450135191957026253)
              ·
                refine ⟨18770489043800696983884845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 50054637450135191957026253 18770489043800696983884845)
                ·
                  refine ⟨7038933391425261368956817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18770489043800696983884845 7038933391425261368956817)
                  ·
                    refine ⟨5279200043568946026717613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7038933391425261368956817 5279200043568946026717613)
                    ·
                      refine ⟨1979700016338354760019105, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5279200043568946026717613 1979700016338354760019105)
                      ·
                        rfl

theorem cell23_3855452_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 1, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 1, 3, 3, 2, 3].length) (baseStart_3855452 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3855452 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3855452 prefixEnd_3855452 := by exact prefixLift 3855452
  have htrace : WordTrace (prefixWord ++ tailWord_3855452) baseStart_3855452 baseEnd_3855452 := by
    simpa [prefixWord, tailWord_3855452, baseEnd_3855452] using wordTrace_append hprefix tailTrace_3855452
  have hstable : (prefixWord ++ tailWord_3855452).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3855452).length < 2 ^ (prefixWord ++ tailWord_3855452).sum := by decide
  have hdescent : baseEnd_3855452 < baseStart_3855452 := by decide
  rcases family_descends (prefixWord ++ tailWord_3855452) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3855453 : List Nat := [1, 4, 4, 1, 2, 2, 1, 1, 2, 3, 2]
def baseStart_3855453 : Nat := 118140960795 + 3855453 * 2 ^ 59
def prefixEnd_3855453 : Nat := 4983230072969 + 3 ^ 40 * 3855453 * 2
def baseEnd_3855453 : Nat := 1979700529819009256106601

theorem tailTrace_3855453 : CollatzResearch.WordTrace tailWord_3855453 prefixEnd_3855453 1979700529819009256106601 := by
  unfold tailWord_3855453
  simp only [CollatzResearch.WordTrace]
  refine ⟨140619923301359714794915013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93746615534239809863276675 140619923301359714794915013)
  ·
    refine ⟨26366235619004946524046565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 140619923301359714794915013 26366235619004946524046565)
    ·
      refine ⟨4943669178563427473258731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 26366235619004946524046565 4943669178563427473258731)
      ·
        refine ⟨7415503767845141209888097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4943669178563427473258731 7415503767845141209888097)
        ·
          refine ⟨5561627825883855907416073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7415503767845141209888097 5561627825883855907416073)
          ·
            refine ⟨4171220869412891930562055, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5561627825883855907416073 4171220869412891930562055)
            ·
              refine ⟨6256831304119337895843083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4171220869412891930562055 6256831304119337895843083)
              ·
                refine ⟨9385246956179006843764625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6256831304119337895843083 9385246956179006843764625)
                ·
                  refine ⟨7038935217134255132823469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9385246956179006843764625 7038935217134255132823469)
                  ·
                    refine ⟨2639600706425345674808801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7038935217134255132823469 2639600706425345674808801)
                    ·
                      refine ⟨1979700529819009256106601, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2639600706425345674808801 1979700529819009256106601)
                      ·
                        rfl

theorem cell23_3855453_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 2, 2, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 2, 2, 1, 1, 2, 3, 2].length) (baseStart_3855453 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3855453 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3855453 prefixEnd_3855453 := by exact prefixLift 3855453
  have htrace : WordTrace (prefixWord ++ tailWord_3855453) baseStart_3855453 baseEnd_3855453 := by
    simpa [prefixWord, tailWord_3855453, baseEnd_3855453] using wordTrace_append hprefix tailTrace_3855453
  have hstable : (prefixWord ++ tailWord_3855453).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3855453).length < 2 ^ (prefixWord ++ tailWord_3855453).sum := by decide
  have hdescent : baseEnd_3855453 < baseStart_3855453 := by decide
  rcases family_descends (prefixWord ++ tailWord_3855453) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3855455 : List Nat := [1, 1, 2, 3, 1, 1, 7, 7]
def baseStart_3855455 : Nat := 118140960795 + 3855455 * 2 ^ 59
def prefixEnd_3855455 : Nat := 4983230072969 + 3 ^ 40 * 3855455 * 2
def baseEnd_3855455 : Nat := 73322279880752527714133

theorem tailTrace_3855455 : CollatzResearch.WordTrace tailWord_3855455 prefixEnd_3855455 73322279880752527714133 := by
  unfold tailWord_3855455
  simp only [CollatzResearch.WordTrace]
  refine ⟨140619996247352469136487819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93746664164901646090991879 140619996247352469136487819)
  ·
    refine ⟨210929994371028703704731729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140619996247352469136487819 210929994371028703704731729)
    ·
      refine ⟨158197495778271527778548797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 210929994371028703704731729 158197495778271527778548797)
      ·
        refine ⟨59324060916851822916955799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 158197495778271527778548797 59324060916851822916955799)
        ·
          refine ⟨88986091375277734375433699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59324060916851822916955799 88986091375277734375433699)
          ·
            refine ⟨133479137062916601563150549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 88986091375277734375433699 133479137062916601563150549)
            ·
              refine ⟨3128417274912107849136341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 133479137062916601563150549 3128417274912107849136341)
              ·
                refine ⟨73322279880752527714133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3128417274912107849136341 73322279880752527714133)
                ·
                  rfl

theorem cell23_3855455_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 7, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 7, 7].length) (baseStart_3855455 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3855455 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3855455 prefixEnd_3855455 := by exact prefixLift 3855455
  have htrace : WordTrace (prefixWord ++ tailWord_3855455) baseStart_3855455 baseEnd_3855455 := by
    simpa [prefixWord, tailWord_3855455, baseEnd_3855455] using wordTrace_append hprefix tailTrace_3855455
  have hstable : (prefixWord ++ tailWord_3855455).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3855455).length < 2 ^ (prefixWord ++ tailWord_3855455).sum := by decide
  have hdescent : baseEnd_3855455 < baseStart_3855455 := by decide
  rcases family_descends (prefixWord ++ tailWord_3855455) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3855466 : List Nat := [3, 1, 3, 2, 2, 3, 2, 1, 1, 1, 4]
def baseStart_3855466 : Nat := 118140960795 + 3855466 * 2 ^ 59
def prefixEnd_3855466 : Nat := 4983230072969 + 3 ^ 40 * 3855466 * 2
def baseEnd_3855466 : Nat := 1979707205067517705244041

theorem tailTrace_3855466 : CollatzResearch.WordTrace tailWord_3855466 prefixEnd_3855466 1979707205067517705244041 := by
  unfold tailWord_3855466
  simp only [CollatzResearch.WordTrace]
  refine ⟨35155099362578154503784563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 93746931633541745343425501 35155099362578154503784563)
  ·
    refine ⟨52732649043867231755676845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35155099362578154503784563 52732649043867231755676845)
    ·
      refine ⟨19774743391450211908378817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 52732649043867231755676845 19774743391450211908378817)
      ·
        refine ⟨14831057543587658931284113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19774743391450211908378817 14831057543587658931284113)
        ·
          refine ⟨11123293157690744198463085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14831057543587658931284113 11123293157690744198463085)
          ·
            refine ⟨4171234934134029074423657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11123293157690744198463085 4171234934134029074423657)
            ·
              refine ⟨3128426200600521805817743, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4171234934134029074423657 3128426200600521805817743)
              ·
                refine ⟨4692639300900782708726615, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3128426200600521805817743 4692639300900782708726615)
                ·
                  refine ⟨7038958951351174063089923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4692639300900782708726615 7038958951351174063089923)
                  ·
                    refine ⟨10558438427026761094634885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7038958951351174063089923 10558438427026761094634885)
                    ·
                      refine ⟨1979707205067517705244041, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10558438427026761094634885 1979707205067517705244041)
                      ·
                        rfl

theorem cell23_3855466_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 3, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 3, 2, 1, 1, 1, 4].length) (baseStart_3855466 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3855466 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3855466 prefixEnd_3855466 := by exact prefixLift 3855466
  have htrace : WordTrace (prefixWord ++ tailWord_3855466) baseStart_3855466 baseEnd_3855466 := by
    simpa [prefixWord, tailWord_3855466, baseEnd_3855466] using wordTrace_append hprefix tailTrace_3855466
  have hstable : (prefixWord ++ tailWord_3855466).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3855466).length < 2 ^ (prefixWord ++ tailWord_3855466).sum := by decide
  have hdescent : baseEnd_3855466 < baseStart_3855466 := by decide
  rcases family_descends (prefixWord ++ tailWord_3855466) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3855469 : List Nat := [1, 5, 1, 1, 2, 3, 1, 3, 1, 2, 3]
def baseStart_3855469 : Nat := 118140960795 + 3855469 * 2 ^ 59
def prefixEnd_3855469 : Nat := 4983230072969 + 3 ^ 40 * 3855469 * 2
def baseEnd_3855469 : Nat := 1979708745509481193506527

theorem tailTrace_3855469 : CollatzResearch.WordTrace tailWord_3855469 prefixEnd_3855469 1979708745509481193506527 := by
  unfold tailWord_3855469
  simp only [CollatzResearch.WordTrace]
  refine ⟨140620506869301749527497461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93747004579534499684998307 140620506869301749527497461)
  ·
    refine ⟨13183172518997039018202887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 140620506869301749527497461 13183172518997039018202887)
    ·
      refine ⟨19774758778495558527304331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13183172518997039018202887 19774758778495558527304331)
      ·
        refine ⟨29662138167743337790956497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19774758778495558527304331 29662138167743337790956497)
        ·
          refine ⟨22246603625807503343217373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29662138167743337790956497 22246603625807503343217373)
          ·
            refine ⟨8342476359677813753706515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22246603625807503343217373 8342476359677813753706515)
            ·
              refine ⟨12513714539516720630559773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8342476359677813753706515 12513714539516720630559773)
              ·
                refine ⟨4692642952318770236459915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12513714539516720630559773 4692642952318770236459915)
                ·
                  refine ⟨7038964428478155354689873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4692642952318770236459915 7038964428478155354689873)
                  ·
                    refine ⟨5279223321358616516017405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7038964428478155354689873 5279223321358616516017405)
                    ·
                      refine ⟨1979708745509481193506527, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5279223321358616516017405 1979708745509481193506527)
                      ·
                        rfl

theorem cell23_3855469_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 3, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 3, 1, 3, 1, 2, 3].length) (baseStart_3855469 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3855469 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3855469 prefixEnd_3855469 := by exact prefixLift 3855469
  have htrace : WordTrace (prefixWord ++ tailWord_3855469) baseStart_3855469 baseEnd_3855469 := by
    simpa [prefixWord, tailWord_3855469, baseEnd_3855469] using wordTrace_append hprefix tailTrace_3855469
  have hstable : (prefixWord ++ tailWord_3855469).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3855469).length < 2 ^ (prefixWord ++ tailWord_3855469).sum := by decide
  have hdescent : baseEnd_3855469 < baseStart_3855469 := by decide
  rcases family_descends (prefixWord ++ tailWord_3855469) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3855496 : List Nat := [2, 1, 3, 4, 3, 1, 1, 1, 1, 2, 4]
def baseStart_3855496 : Nat := 118140960795 + 3855496 * 2 ^ 59
def prefixEnd_3855496 : Nat := 4983230072969 + 3 ^ 40 * 3855496 * 2
def baseEnd_3855496 : Nat := 1979722609487152587868903

theorem tailTrace_3855496 : CollatzResearch.WordTrace tailWord_3855496 prefixEnd_3855496 1979722609487152587868903 := by
  unfold tailWord_3855496
  simp only [CollatzResearch.WordTrace]
  refine ⟨70310745820101966569365171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93747661093469288759153561 70310745820101966569365171)
  ·
    refine ⟨105466118730152949854047757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70310745820101966569365171 105466118730152949854047757)
    ·
      refine ⟨39549794523807356195267909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 105466118730152949854047757 39549794523807356195267909)
      ·
        refine ⟨7415586473213879286612733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 39549794523807356195267909 7415586473213879286612733)
        ·
          refine ⟨2780844927455204732479775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7415586473213879286612733 2780844927455204732479775)
          ·
            refine ⟨4171267391182807098719663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2780844927455204732479775 4171267391182807098719663)
            ·
              refine ⟨6256901086774210648079495, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4171267391182807098719663 6256901086774210648079495)
              ·
                refine ⟨9385351630161315972119243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6256901086774210648079495 9385351630161315972119243)
                ·
                  refine ⟨14078027445241973958178865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9385351630161315972119243 14078027445241973958178865)
                  ·
                    refine ⟨10558520583931480468634149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14078027445241973958178865 10558520583931480468634149)
                    ·
                      refine ⟨1979722609487152587868903, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10558520583931480468634149 1979722609487152587868903)
                      ·
                        rfl

theorem cell23_3855496_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 3, 1, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 3, 1, 1, 1, 1, 2, 4].length) (baseStart_3855496 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3855496 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3855496 prefixEnd_3855496 := by exact prefixLift 3855496
  have htrace : WordTrace (prefixWord ++ tailWord_3855496) baseStart_3855496 baseEnd_3855496 := by
    simpa [prefixWord, tailWord_3855496, baseEnd_3855496] using wordTrace_append hprefix tailTrace_3855496
  have hstable : (prefixWord ++ tailWord_3855496).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3855496).length < 2 ^ (prefixWord ++ tailWord_3855496).sum := by decide
  have hdescent : baseEnd_3855496 < baseStart_3855496 := by decide
  rcases family_descends (prefixWord ++ tailWord_3855496) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3855525 : List Nat := [1, 3, 1, 2, 1, 4, 1, 1, 1, 3, 5]
def baseStart_3855525 : Nat := 118140960795 + 3855525 * 2 ^ 59
def prefixEnd_3855525 : Nat := 4983230072969 + 3 ^ 40 * 3855525 * 2
def baseEnd_3855525 : Nat := 1979737500426132974406269

theorem tailTrace_3855525 : CollatzResearch.WordTrace tailWord_3855525 prefixEnd_3855525 1979737500426132974406269 := by
  unfold tailWord_3855525
  simp only [CollatzResearch.WordTrace]
  refine ⟨140622549357098871091536029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93748366238065914061024019 140622549357098871091536029)
  ·
    refine ⟨52733456008912076659326011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 140622549357098871091536029 52733456008912076659326011)
    ·
      refine ⟨79100184013368114988989017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52733456008912076659326011 79100184013368114988989017)
      ·
        refine ⟨59325138010026086241741763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 79100184013368114988989017 59325138010026086241741763)
        ·
          refine ⟨88987707015039129362612645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59325138010026086241741763 88987707015039129362612645)
          ·
            refine ⟨16685195065319836755489871, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 88987707015039129362612645 16685195065319836755489871)
            ·
              refine ⟨25027792597979755133234807, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16685195065319836755489871 25027792597979755133234807)
              ·
                refine ⟨37541688896969632699852211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25027792597979755133234807 37541688896969632699852211)
                ·
                  refine ⟨56312533345454449049778317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37541688896969632699852211 56312533345454449049778317)
                  ·
                    refine ⟨21117200004545418393666869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 56312533345454449049778317 21117200004545418393666869)
                    ·
                      refine ⟨1979737500426132974406269, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 21117200004545418393666869 1979737500426132974406269)
                      ·
                        rfl

theorem cell23_3855525_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 4, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 4, 1, 1, 1, 3, 5].length) (baseStart_3855525 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3855525 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3855525 prefixEnd_3855525 := by exact prefixLift 3855525
  have htrace : WordTrace (prefixWord ++ tailWord_3855525) baseStart_3855525 baseEnd_3855525 := by
    simpa [prefixWord, tailWord_3855525, baseEnd_3855525] using wordTrace_append hprefix tailTrace_3855525
  have hstable : (prefixWord ++ tailWord_3855525).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3855525).length < 2 ^ (prefixWord ++ tailWord_3855525).sum := by decide
  have hdescent : baseEnd_3855525 < baseStart_3855525 := by decide
  rcases family_descends (prefixWord ++ tailWord_3855525) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3855535 : List Nat := [1, 1, 2, 1, 2, 3, 2, 1, 4, 2, 4]
def baseStart_3855535 : Nat := 118140960795 + 3855535 * 2 ^ 59
def prefixEnd_3855535 : Nat := 4983230072969 + 3 ^ 40 * 3855535 * 2
def baseEnd_3855535 : Nat := 1979742635232677935281223

theorem tailTrace_3855535 : CollatzResearch.WordTrace tailWord_3855535 prefixEnd_3855535 1979742635232677935281223 := by
  unfold tailWord_3855535
  simp only [CollatzResearch.WordTrace]
  refine ⟨140622914087062642799400059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93748609391375095199600039 140622914087062642799400059)
  ·
    refine ⟨210934371130593964199100089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140622914087062642799400059 210934371130593964199100089)
    ·
      refine ⟨158200778347945473149325067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 210934371130593964199100089 158200778347945473149325067)
      ·
        refine ⟨237301167521918209723987601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 158200778347945473149325067 237301167521918209723987601)
        ·
          refine ⟨177975875641438657292990701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 237301167521918209723987601 177975875641438657292990701)
          ·
            refine ⟨66740953365539496484871513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 177975875641438657292990701 66740953365539496484871513)
            ·
              refine ⟨50055715024154622363653635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 66740953365539496484871513 50055715024154622363653635)
              ·
                refine ⟨75083572536231933545480453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50055715024154622363653635 75083572536231933545480453)
                ·
                  refine ⟨14078169850543487539777585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 75083572536231933545480453 14078169850543487539777585)
                  ·
                    refine ⟨10558627387907615654833189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14078169850543487539777585 10558627387907615654833189)
                    ·
                      refine ⟨1979742635232677935281223, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10558627387907615654833189 1979742635232677935281223)
                      ·
                        rfl

theorem cell23_3855535_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 2, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 2, 1, 4, 2, 4].length) (baseStart_3855535 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3855535 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3855535 prefixEnd_3855535 := by exact prefixLift 3855535
  have htrace : WordTrace (prefixWord ++ tailWord_3855535) baseStart_3855535 baseEnd_3855535 := by
    simpa [prefixWord, tailWord_3855535, baseEnd_3855535] using wordTrace_append hprefix tailTrace_3855535
  have hstable : (prefixWord ++ tailWord_3855535).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3855535).length < 2 ^ (prefixWord ++ tailWord_3855535).sum := by decide
  have hdescent : baseEnd_3855535 < baseStart_3855535 := by decide
  rcases family_descends (prefixWord ++ tailWord_3855535) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3855539 : List Nat := [1, 1, 1, 2, 3, 2, 4, 1, 4, 2, 2]
def baseStart_3855539 : Nat := 118140960795 + 3855539 * 2 ^ 59
def prefixEnd_3855539 : Nat := 4983230072969 + 3 ^ 40 * 3855539 * 2
def baseEnd_3855539 : Nat := 1979744689155295919631205

theorem tailTrace_3855539 : CollatzResearch.WordTrace tailWord_3855539 prefixEnd_3855539 1979744689155295919631205 := by
  unfold tailWord_3855539
  simp only [CollatzResearch.WordTrace]
  refine ⟨140623059979048151482545671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93748706652698767655030447 140623059979048151482545671)
  ·
    refine ⟨210934589968572227223818507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140623059979048151482545671 210934589968572227223818507)
    ·
      refine ⟨316401884952858340835727761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 210934589968572227223818507 316401884952858340835727761)
      ·
        refine ⟨237301413714643755626795821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 316401884952858340835727761 237301413714643755626795821)
        ·
          refine ⟨88988030142991408360048433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 237301413714643755626795821 88988030142991408360048433)
          ·
            refine ⟨66741022607243556270036325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 88988030142991408360048433 66741022607243556270036325)
            ·
              refine ⟨12513941738858166800631811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 66741022607243556270036325 12513941738858166800631811)
              ·
                refine ⟨18770912608287250200947717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12513941738858166800631811 18770912608287250200947717)
                ·
                  refine ⟨3519546114053859412677697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 18770912608287250200947717 3519546114053859412677697)
                  ·
                    refine ⟨2639659585540394559508273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3519546114053859412677697 2639659585540394559508273)
                    ·
                      refine ⟨1979744689155295919631205, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2639659585540394559508273 1979744689155295919631205)
                      ·
                        rfl

theorem cell23_3855539_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 4, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 4, 1, 4, 2, 2].length) (baseStart_3855539 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3855539 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3855539 prefixEnd_3855539 := by exact prefixLift 3855539
  have htrace : WordTrace (prefixWord ++ tailWord_3855539) baseStart_3855539 baseEnd_3855539 := by
    simpa [prefixWord, tailWord_3855539, baseEnd_3855539] using wordTrace_append hprefix tailTrace_3855539
  have hstable : (prefixWord ++ tailWord_3855539).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3855539).length < 2 ^ (prefixWord ++ tailWord_3855539).sum := by decide
  have hdescent : baseEnd_3855539 < baseStart_3855539 := by decide
  rcases family_descends (prefixWord ++ tailWord_3855539) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3855575 : List Nat := [1, 1, 3, 2, 1, 2, 2, 3, 1, 7]
def baseStart_3855575 : Nat := 118140960795 + 3855575 * 2 ^ 59
def prefixEnd_3855575 : Nat := 4983230072969 + 3 ^ 40 * 3855575 * 2
def baseEnd_3855575 : Nat := 659921058152952592927013

theorem tailTrace_3855575 : CollatzResearch.WordTrace tailWord_3855575 prefixEnd_3855575 659921058152952592927013 := by
  unfold tailWord_3855575
  simp only [CollatzResearch.WordTrace]
  refine ⟨140624373006917729630856179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93749582004611819753904119 140624373006917729630856179)
  ·
    refine ⟨210936559510376594446284269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140624373006917729630856179 210936559510376594446284269)
    ·
      refine ⟨79101209816391222917356601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 210936559510376594446284269 79101209816391222917356601)
      ·
        refine ⟨59325907362293417188017451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 79101209816391222917356601 59325907362293417188017451)
        ·
          refine ⟨88988861043440125782026177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59325907362293417188017451 88988861043440125782026177)
          ·
            refine ⟨66741645782580094336519633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 88988861043440125782026177 66741645782580094336519633)
            ·
              refine ⟨50056234336935070752389725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 66741645782580094336519633 50056234336935070752389725)
              ·
                refine ⟨18771087876350651532146147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 50056234336935070752389725 18771087876350651532146147)
                ·
                  refine ⟨28156631814525977298219221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18771087876350651532146147 28156631814525977298219221)
                  ·
                    refine ⟨659921058152952592927013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 28156631814525977298219221 659921058152952592927013)
                    ·
                      rfl

theorem cell23_3855575_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 2, 3, 1, 7].length) (baseStart_3855575 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3855575 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3855575 prefixEnd_3855575 := by exact prefixLift 3855575
  have htrace : WordTrace (prefixWord ++ tailWord_3855575) baseStart_3855575 baseEnd_3855575 := by
    simpa [prefixWord, tailWord_3855575, baseEnd_3855575] using wordTrace_append hprefix tailTrace_3855575
  have hstable : (prefixWord ++ tailWord_3855575).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3855575).length < 2 ^ (prefixWord ++ tailWord_3855575).sum := by decide
  have hdescent : baseEnd_3855575 < baseStart_3855575 := by decide
  rcases family_descends (prefixWord ++ tailWord_3855575) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3855592 : List Nat := [2, 1, 4, 1, 2, 1, 1, 4, 2, 5]
def baseStart_3855592 : Nat := 118140960795 + 3855592 * 2 ^ 59
def prefixEnd_3855592 : Nat := 4983230072969 + 3 ^ 40 * 3855592 * 2
def baseEnd_3855592 : Nat := 659923967876661404089487

theorem tailTrace_3855592 : CollatzResearch.WordTrace tailWord_3855592 prefixEnd_3855592 659923967876661404089487 := by
  unfold tailWord_3855592
  simp only [CollatzResearch.WordTrace]
  refine ⟨70312496523928070767112515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93749995365237427689483353 70312496523928070767112515)
  ·
    refine ⟨105468744785892106150668773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70312496523928070767112515 105468744785892106150668773)
    ·
      refine ⟨19775389647354769903250395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 105468744785892106150668773 19775389647354769903250395)
      ·
        refine ⟨29663084471032154854875593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19775389647354769903250395 29663084471032154854875593)
        ·
          refine ⟨22247313353274116141156695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29663084471032154854875593 22247313353274116141156695)
          ·
            refine ⟨33370970029911174211735043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22247313353274116141156695 33370970029911174211735043)
            ·
              refine ⟨50056455044866761317602565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33370970029911174211735043 50056455044866761317602565)
              ·
                refine ⟨9385585320912517747050481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 50056455044866761317602565 9385585320912517747050481)
                ·
                  refine ⟨7039188990684388310287861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9385585320912517747050481 7039188990684388310287861)
                  ·
                    refine ⟨659923967876661404089487, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7039188990684388310287861 659923967876661404089487)
                    ·
                      rfl

theorem cell23_3855592_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 1, 4, 2, 5].length) (baseStart_3855592 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3855592 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3855592 prefixEnd_3855592 := by exact prefixLift 3855592
  have htrace : WordTrace (prefixWord ++ tailWord_3855592) baseStart_3855592 baseEnd_3855592 := by
    simpa [prefixWord, tailWord_3855592, baseEnd_3855592] using wordTrace_append hprefix tailTrace_3855592
  have hstable : (prefixWord ++ tailWord_3855592).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3855592).length < 2 ^ (prefixWord ++ tailWord_3855592).sum := by decide
  have hdescent : baseEnd_3855592 < baseStart_3855592 := by decide
  rcases family_descends (prefixWord ++ tailWord_3855592) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3855596 : List Nat := [2, 2, 1, 1, 2, 6, 2, 2, 5]
def baseStart_3855596 : Nat := 118140960795 + 3855596 * 2 ^ 59
def prefixEnd_3855596 : Nat := 4983230072969 + 3 ^ 40 * 3855596 * 2
def baseEnd_3855596 : Nat := 219974884172511355179827

theorem tailTrace_3855596 : CollatzResearch.WordTrace tailWord_3855596 prefixEnd_3855596 219974884172511355179827 := by
  unfold tailWord_3855596
  simp only [CollatzResearch.WordTrace]
  refine ⟨70312569469920825108685321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93750092626561100144913761 70312569469920825108685321)
  ·
    refine ⟨52734427102440618831513991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70312569469920825108685321 52734427102440618831513991)
    ·
      refine ⟨79101640653660928247270987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52734427102440618831513991 79101640653660928247270987)
      ·
        refine ⟨118652460980491392370906481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79101640653660928247270987 118652460980491392370906481)
        ·
          refine ⟨88989345735368544278179861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 118652460980491392370906481 88989345735368544278179861)
          ·
            refine ⟨4171375581345400513039681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 88989345735368544278179861 4171375581345400513039681)
            ·
              refine ⟨3128531686009050384779761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4171375581345400513039681 3128531686009050384779761)
              ·
                refine ⟨2346398764506787788584821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3128531686009050384779761 2346398764506787788584821)
                ·
                  refine ⟨219974884172511355179827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2346398764506787788584821 219974884172511355179827)
                  ·
                    rfl

theorem cell23_3855596_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 6, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 6, 2, 2, 5].length) (baseStart_3855596 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3855596 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3855596 prefixEnd_3855596 := by exact prefixLift 3855596
  have htrace : WordTrace (prefixWord ++ tailWord_3855596) baseStart_3855596 baseEnd_3855596 := by
    simpa [prefixWord, tailWord_3855596, baseEnd_3855596] using wordTrace_append hprefix tailTrace_3855596
  have hstable : (prefixWord ++ tailWord_3855596).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3855596).length < 2 ^ (prefixWord ++ tailWord_3855596).sum := by decide
  have hdescent : baseEnd_3855596 < baseStart_3855596 := by decide
  rcases family_descends (prefixWord ++ tailWord_3855596) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3855642 : List Nat := [3, 1, 1, 3, 3, 1, 1, 1, 2, 1, 6]
def baseStart_3855642 : Nat := 118140960795 + 3855642 * 2 ^ 59
def prefixEnd_3855642 : Nat := 4983230072969 + 3 ^ 40 * 3855642 * 2
def baseEnd_3855642 : Nat := 1979797577662709016643231

theorem tailTrace_3855642 : CollatzResearch.WordTrace tailWord_3855642 prefixEnd_3855642 1979797577662709016643231 := by
  unfold tailWord_3855642
  simp only [CollatzResearch.WordTrace]
  refine ⟨35156704174418750018386295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 93751211131783333382363453 35156704174418750018386295)
  ·
    refine ⟨52735056261628125027579443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35156704174418750018386295 52735056261628125027579443)
    ·
      refine ⟨79102584392442187541369165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52735056261628125027579443 79102584392442187541369165)
      ·
        refine ⟨29663469147165820328013437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 79102584392442187541369165 29663469147165820328013437)
        ·
          refine ⟨11123800930187182623005039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29663469147165820328013437 11123800930187182623005039)
          ·
            refine ⟨16685701395280773934507559, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11123800930187182623005039 16685701395280773934507559)
            ·
              refine ⟨25028552092921160901761339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16685701395280773934507559 25028552092921160901761339)
              ·
                refine ⟨37542828139381741352642009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25028552092921160901761339 37542828139381741352642009)
                ·
                  refine ⟨28157121104536306014481507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 37542828139381741352642009 28157121104536306014481507)
                  ·
                    refine ⟨42235681656804459021722261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 28157121104536306014481507 42235681656804459021722261)
                    ·
                      refine ⟨1979797577662709016643231, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 42235681656804459021722261 1979797577662709016643231)
                      ·
                        rfl

theorem cell23_3855642_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 1, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 1, 1, 1, 2, 1, 6].length) (baseStart_3855642 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3855642 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3855642 prefixEnd_3855642 := by exact prefixLift 3855642
  have htrace : WordTrace (prefixWord ++ tailWord_3855642) baseStart_3855642 baseEnd_3855642 := by
    simpa [prefixWord, tailWord_3855642, baseEnd_3855642] using wordTrace_append hprefix tailTrace_3855642
  have hstable : (prefixWord ++ tailWord_3855642).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3855642).length < 2 ^ (prefixWord ++ tailWord_3855642).sum := by decide
  have hdescent : baseEnd_3855642 < baseStart_3855642 := by decide
  rcases family_descends (prefixWord ++ tailWord_3855642) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3855652 : List Nat := [2, 3, 1, 3, 1, 1, 3, 1, 8]
def baseStart_3855652 : Nat := 118140960795 + 3855652 * 2 ^ 59
def prefixEnd_3855652 : Nat := 4983230072969 + 3 ^ 40 * 3855652 * 2
def baseEnd_3855652 : Nat := 219978079163250441946465

theorem tailTrace_3855652 : CollatzResearch.WordTrace tailWord_3855652 prefixEnd_3855652 219978079163250441946465 := by
  unfold tailWord_3855652
  simp only [CollatzResearch.WordTrace]
  refine ⟨70313590713819385890704605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93751454285092514520939473 70313590713819385890704605)
  ·
    refine ⟨26367596517682269709014227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 70313590713819385890704605 26367596517682269709014227)
    ·
      refine ⟨39551394776523404563521341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26367596517682269709014227 39551394776523404563521341)
      ·
        refine ⟨14831773041196276711320503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 39551394776523404563521341 14831773041196276711320503)
        ·
          refine ⟨22247659561794415066980755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14831773041196276711320503 22247659561794415066980755)
          ·
            refine ⟨33371489342691622600471133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22247659561794415066980755 33371489342691622600471133)
            ·
              refine ⟨12514308503509358475176675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33371489342691622600471133 12514308503509358475176675)
              ·
                refine ⟨18771462755264037712765013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12514308503509358475176675 18771462755264037712765013)
                ·
                  refine ⟨219978079163250441946465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 18771462755264037712765013 219978079163250441946465)
                  ·
                    rfl

theorem cell23_3855652_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 3, 1, 8].length) (baseStart_3855652 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3855652 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3855652 prefixEnd_3855652 := by exact prefixLift 3855652
  have htrace : WordTrace (prefixWord ++ tailWord_3855652) baseStart_3855652 baseEnd_3855652 := by
    simpa [prefixWord, tailWord_3855652, baseEnd_3855652] using wordTrace_append hprefix tailTrace_3855652
  have hstable : (prefixWord ++ tailWord_3855652).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3855652).length < 2 ^ (prefixWord ++ tailWord_3855652).sum := by decide
  have hdescent : baseEnd_3855652 < baseStart_3855652 := by decide
  rcases family_descends (prefixWord ++ tailWord_3855652) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3855656 : List Nat := [2, 1, 5, 1, 2, 2, 2, 1, 3, 4]
def baseStart_3855656 : Nat := 118140960795 + 3855656 * 2 ^ 59
def prefixEnd_3855656 : Nat := 4983230072969 + 3 ^ 40 * 3855656 * 2
def baseEnd_3855656 : Nat := 659934922130623987289389

theorem tailTrace_3855656 : CollatzResearch.WordTrace tailWord_3855656 prefixEnd_3855656 659934922130623987289389 := by
  unfold tailWord_3855656
  simp only [CollatzResearch.WordTrace]
  refine ⟨70313663659812140232277411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93751551546416186976369881 70313663659812140232277411)
  ·
    refine ⟨105470495489718210348416117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70313663659812140232277411 105470495489718210348416117)
    ·
      refine ⟨9887858952161082220164011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 105470495489718210348416117 9887858952161082220164011)
      ·
        refine ⟨14831788428241623330246017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9887858952161082220164011 14831788428241623330246017)
        ·
          refine ⟨11123841321181217497684513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14831788428241623330246017 11123841321181217497684513)
          ·
            refine ⟨8342880990885913123263385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11123841321181217497684513 8342880990885913123263385)
            ·
              refine ⟨6257160743164434842447539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8342880990885913123263385 6257160743164434842447539)
              ·
                refine ⟨9385741114746652263671309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6257160743164434842447539 9385741114746652263671309)
                ·
                  refine ⟨3519652918029994598876741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9385741114746652263671309 3519652918029994598876741)
                  ·
                    refine ⟨659934922130623987289389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3519652918029994598876741 659934922130623987289389)
                    ·
                      rfl

theorem cell23_3855656_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 2, 2, 1, 3, 4].length) (baseStart_3855656 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3855656 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3855656 prefixEnd_3855656 := by exact prefixLift 3855656
  have htrace : WordTrace (prefixWord ++ tailWord_3855656) baseStart_3855656 baseEnd_3855656 := by
    simpa [prefixWord, tailWord_3855656, baseEnd_3855656] using wordTrace_append hprefix tailTrace_3855656
  have hstable : (prefixWord ++ tailWord_3855656).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3855656).length < 2 ^ (prefixWord ++ tailWord_3855656).sum := by decide
  have hdescent : baseEnd_3855656 < baseStart_3855656 := by decide
  rcases family_descends (prefixWord ++ tailWord_3855656) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3855689 : List Nat := [1, 2, 1, 1, 2, 3, 4, 1, 1, 5, 2]
def baseStart_3855689 : Nat := 118140960795 + 3855689 * 2 ^ 59
def prefixEnd_3855689 : Nat := 4983230072969 + 3 ^ 40 * 3855689 * 2
def baseEnd_3855689 : Nat := 1979821711253470332755515

theorem tailTrace_3855689 : CollatzResearch.WordTrace tailWord_3855689 prefixEnd_3855689 1979821711253470332755515 := by
  unfold tailWord_3855689
  simp only [CollatzResearch.WordTrace]
  refine ⟨140628530928504727100506121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93752353952336484733670747 140628530928504727100506121)
  ·
    refine ⟨105471398196378545325379591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 140628530928504727100506121 105471398196378545325379591)
    ·
      refine ⟨158207097294567817988069387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105471398196378545325379591 158207097294567817988069387)
      ·
        refine ⟨237310645941851726982104081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 158207097294567817988069387 237310645941851726982104081)
        ·
          refine ⟨177982984456388795236578061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 237310645941851726982104081 177982984456388795236578061)
          ·
            refine ⟨66743619171145798213716773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 177982984456388795236578061 66743619171145798213716773)
            ·
              refine ⟨12514428594589837165071895, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 66743619171145798213716773 12514428594589837165071895)
              ·
                refine ⟨18771642891884755747607843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12514428594589837165071895 18771642891884755747607843)
                ·
                  refine ⟨28157464337827133621411765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18771642891884755747607843 28157464337827133621411765)
                  ·
                    refine ⟨2639762281671293777007353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 28157464337827133621411765 2639762281671293777007353)
                    ·
                      refine ⟨1979821711253470332755515, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2639762281671293777007353 1979821711253470332755515)
                      ·
                        rfl

theorem cell23_3855689_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 4, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 4, 1, 1, 5, 2].length) (baseStart_3855689 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3855689 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3855689 prefixEnd_3855689 := by exact prefixLift 3855689
  have htrace : WordTrace (prefixWord ++ tailWord_3855689) baseStart_3855689 baseEnd_3855689 := by
    simpa [prefixWord, tailWord_3855689, baseEnd_3855689] using wordTrace_append hprefix tailTrace_3855689
  have hstable : (prefixWord ++ tailWord_3855689).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3855689).length < 2 ^ (prefixWord ++ tailWord_3855689).sum := by decide
  have hdescent : baseEnd_3855689 < baseStart_3855689 := by decide
  rcases family_descends (prefixWord ++ tailWord_3855689) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3855733 : List Nat := [1, 3, 4, 1, 3, 2, 1, 2, 1, 5]
def baseStart_3855733 : Nat := 118140960795 + 3855733 * 2 ^ 59
def prefixEnd_3855733 : Nat := 4983230072969 + 3 ^ 40 * 3855733 * 2
def baseEnd_3855733 : Nat := 659948101467422720201771

theorem tailTrace_3855733 : CollatzResearch.WordTrace tailWord_3855733 prefixEnd_3855733 659948101467422720201771 := by
  unfold tailWord_3855733
  simp only [CollatzResearch.WordTrace]
  refine ⟨140630135740345322615107853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93753423826896881743405235 140630135740345322615107853)
  ·
    refine ⟨52736300902629495980665445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 140630135740345322615107853 52736300902629495980665445)
    ·
      refine ⟨9888056419243030496374771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 52736300902629495980665445 9888056419243030496374771)
      ·
        refine ⟨14832084628864545744562157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9888056419243030496374771 14832084628864545744562157)
        ·
          refine ⟨5562031735824204654210809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14832084628864545744562157 5562031735824204654210809)
          ·
            refine ⟨4171523801868153490658107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5562031735824204654210809 4171523801868153490658107)
            ·
              refine ⟨6257285702802230235987161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4171523801868153490658107 6257285702802230235987161)
              ·
                refine ⟨4692964277101672676990371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6257285702802230235987161 4692964277101672676990371)
                ·
                  refine ⟨7039446415652509015485557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4692964277101672676990371 7039446415652509015485557)
                  ·
                    refine ⟨659948101467422720201771, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7039446415652509015485557 659948101467422720201771)
                    ·
                      rfl

theorem cell23_3855733_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 3, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 3, 2, 1, 2, 1, 5].length) (baseStart_3855733 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3855733 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3855733 prefixEnd_3855733 := by exact prefixLift 3855733
  have htrace : WordTrace (prefixWord ++ tailWord_3855733) baseStart_3855733 baseEnd_3855733 := by
    simpa [prefixWord, tailWord_3855733, baseEnd_3855733] using wordTrace_append hprefix tailTrace_3855733
  have hstable : (prefixWord ++ tailWord_3855733).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3855733).length < 2 ^ (prefixWord ++ tailWord_3855733).sum := by decide
  have hdescent : baseEnd_3855733 < baseStart_3855733 := by decide
  rcases family_descends (prefixWord ++ tailWord_3855733) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3855739 : List Nat := [1, 1, 1, 1, 1, 6, 3, 1, 3, 2, 3]
def baseStart_3855739 : Nat := 118140960795 + 3855739 * 2 ^ 59
def prefixEnd_3855739 : Nat := 4983230072969 + 3 ^ 40 * 3855739 * 2
def baseEnd_3855739 : Nat := 1979847385286195137130285

theorem tailTrace_3855739 : CollatzResearch.WordTrace tailWord_3855739 prefixEnd_3855739 1979847385286195137130285 := by
  unfold tailWord_3855739
  simp only [CollatzResearch.WordTrace]
  refine ⟨140630354578323585639826271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93753569718882390426550847 140630354578323585639826271)
  ·
    refine ⟨210945531867485378459739407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140630354578323585639826271 210945531867485378459739407)
    ·
      refine ⟨316418297801228067689609111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 210945531867485378459739407 316418297801228067689609111)
      ·
        refine ⟨474627446701842101534413667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 316418297801228067689609111 474627446701842101534413667)
        ·
          refine ⟨711941170052763152301620501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 474627446701842101534413667 711941170052763152301620501)
          ·
            refine ⟨33372242346223272764138461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 711941170052763152301620501 33372242346223272764138461)
            ·
              refine ⟨12514590879833727286551923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33372242346223272764138461 12514590879833727286551923)
              ·
                refine ⟨18771886319750590929827885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12514590879833727286551923 18771886319750590929827885)
                ·
                  refine ⟨7039457369906471598685457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18771886319750590929827885 7039457369906471598685457)
                  ·
                    refine ⟨5279593027429853699014093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7039457369906471598685457 5279593027429853699014093)
                    ·
                      refine ⟨1979847385286195137130285, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5279593027429853699014093 1979847385286195137130285)
                      ·
                        rfl

theorem cell23_3855739_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 3, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 3, 1, 3, 2, 3].length) (baseStart_3855739 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3855739 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3855739 prefixEnd_3855739 := by exact prefixLift 3855739
  have htrace : WordTrace (prefixWord ++ tailWord_3855739) baseStart_3855739 baseEnd_3855739 := by
    simpa [prefixWord, tailWord_3855739, baseEnd_3855739] using wordTrace_append hprefix tailTrace_3855739
  have hstable : (prefixWord ++ tailWord_3855739).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3855739).length < 2 ^ (prefixWord ++ tailWord_3855739).sum := by decide
  have hdescent : baseEnd_3855739 < baseStart_3855739 := by decide
  rcases family_descends (prefixWord ++ tailWord_3855739) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3855746 : List Nat := [3, 4, 2, 1, 1, 1, 1, 1, 3, 6]
def baseStart_3855746 : Nat := 118140960795 + 3855746 * 2 ^ 59
def prefixEnd_3855746 : Nat := 4983230072969 + 3 ^ 40 * 3855746 * 2
def baseEnd_3855746 : Nat := 659950326550258869914251

theorem tailTrace_3855746 : CollatzResearch.WordTrace tailWord_3855746 prefixEnd_3855746 659950326550258869914251 := by
  unfold tailWord_3855746
  simp only [CollatzResearch.WordTrace]
  refine ⟨35157652472324556458832773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 93753739926198817223554061 35157652472324556458832773)
  ·
    refine ⟨6592059838560854336031145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 35157652472324556458832773 6592059838560854336031145)
    ·
      refine ⟨4944044878920640752023359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6592059838560854336031145 4944044878920640752023359)
      ·
        refine ⟨7416067318380961128035039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4944044878920640752023359 7416067318380961128035039)
        ·
          refine ⟨11124100977571441692052559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7416067318380961128035039 11124100977571441692052559)
          ·
            refine ⟨16686151466357162538078839, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11124100977571441692052559 16686151466357162538078839)
            ·
              refine ⟨25029227199535743807118259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16686151466357162538078839 25029227199535743807118259)
              ·
                refine ⟨37543840799303615710677389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25029227199535743807118259 37543840799303615710677389)
                ·
                  refine ⟨14078940299738855891504021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 37543840799303615710677389 14078940299738855891504021)
                  ·
                    refine ⟨659950326550258869914251, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 14078940299738855891504021 659950326550258869914251)
                    ·
                      rfl

theorem cell23_3855746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 1, 1, 1, 3, 6].length) (baseStart_3855746 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3855746 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3855746 prefixEnd_3855746 := by exact prefixLift 3855746
  have htrace : WordTrace (prefixWord ++ tailWord_3855746) baseStart_3855746 baseEnd_3855746 := by
    simpa [prefixWord, tailWord_3855746, baseEnd_3855746] using wordTrace_append hprefix tailTrace_3855746
  have hstable : (prefixWord ++ tailWord_3855746).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3855746).length < 2 ^ (prefixWord ++ tailWord_3855746).sum := by decide
  have hdescent : baseEnd_3855746 < baseStart_3855746 := by decide
  rcases family_descends (prefixWord ++ tailWord_3855746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3855753 : List Nat := [1, 2, 1, 1, 7, 1, 3, 1, 1, 1, 4]
def baseStart_3855753 : Nat := 118140960795 + 3855753 * 2 ^ 59
def prefixEnd_3855753 : Nat := 4983230072969 + 3 ^ 40 * 3855753 * 2
def baseEnd_3855753 : Nat := 1979854574015358082355221

theorem tailTrace_3855753 : CollatzResearch.WordTrace tailWord_3855753 prefixEnd_3855753 1979854574015358082355221 := by
  unfold tailWord_3855753
  simp only [CollatzResearch.WordTrace]
  refine ⟨140630865200272866030835913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93753910133515244020557275 140630865200272866030835913)
  ·
    refine ⟨105473148900204649523126935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 140630865200272866030835913 105473148900204649523126935)
    ·
      refine ⟨158209723350306974284690403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105473148900204649523126935 158209723350306974284690403)
      ·
        refine ⟨237314585025460461427035605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 158209723350306974284690403 237314585025460461427035605)
        ·
          refine ⟨5562060586534229564696147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 237314585025460461427035605 5562060586534229564696147)
          ·
            refine ⟨8343090879801344347044221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5562060586534229564696147 8343090879801344347044221)
            ·
              refine ⟨3128659079925504130141583, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8343090879801344347044221 3128659079925504130141583)
              ·
                refine ⟨4692988619888256195212375, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3128659079925504130141583 4692988619888256195212375)
                ·
                  refine ⟨7039482929832384292818563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4692988619888256195212375 7039482929832384292818563)
                  ·
                    refine ⟨10559224394748576439227845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7039482929832384292818563 10559224394748576439227845)
                    ·
                      refine ⟨1979854574015358082355221, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10559224394748576439227845 1979854574015358082355221)
                      ·
                        rfl

theorem cell23_3855753_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 7, 1, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 7, 1, 3, 1, 1, 1, 4].length) (baseStart_3855753 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3855753 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3855753 prefixEnd_3855753 := by exact prefixLift 3855753
  have htrace : WordTrace (prefixWord ++ tailWord_3855753) baseStart_3855753 baseEnd_3855753 := by
    simpa [prefixWord, tailWord_3855753, baseEnd_3855753] using wordTrace_append hprefix tailTrace_3855753
  have hstable : (prefixWord ++ tailWord_3855753).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3855753).length < 2 ^ (prefixWord ++ tailWord_3855753).sum := by decide
  have hdescent : baseEnd_3855753 < baseStart_3855753 := by decide
  rcases family_descends (prefixWord ++ tailWord_3855753) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3855770 : List Nat := [3, 1, 1, 4, 1, 1, 3, 4, 1, 2, 2]
def baseStart_3855770 : Nat := 118140960795 + 3855770 * 2 ^ 59
def prefixEnd_3855770 : Nat := 4983230072969 + 3 ^ 40 * 3855770 * 2
def baseEnd_3855770 : Nat := 1979863303186484515842643

theorem tailTrace_3855770 : CollatzResearch.WordTrace tailWord_3855770 prefixEnd_3855770 1979863303186484515842643 := by
  unfold tailWord_3855770
  simp only [CollatzResearch.WordTrace]
  refine ⟨35157871310302819483551191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 93754323494140851956136509 35157871310302819483551191)
  ·
    refine ⟨52736806965454229225326787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35157871310302819483551191 52736806965454229225326787)
    ·
      refine ⟨79105210448181343837990181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52736806965454229225326787 79105210448181343837990181)
      ·
        refine ⟨14832226959034001969623159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 79105210448181343837990181 14832226959034001969623159)
        ·
          refine ⟨22248340438551002954434739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14832226959034001969623159 22248340438551002954434739)
          ·
            refine ⟨33372510657826504431652109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22248340438551002954434739 33372510657826504431652109)
            ·
              refine ⟨12514691496684939161869541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33372510657826504431652109 12514691496684939161869541)
              ·
                refine ⟨2346504655628426092850539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12514691496684939161869541 2346504655628426092850539)
                ·
                  refine ⟨3519756983442639139275809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2346504655628426092850539 3519756983442639139275809)
                  ·
                    refine ⟨2639817737581979354456857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3519756983442639139275809 2639817737581979354456857)
                    ·
                      refine ⟨1979863303186484515842643, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2639817737581979354456857 1979863303186484515842643)
                      ·
                        rfl

theorem cell23_3855770_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 3, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 3, 4, 1, 2, 2].length) (baseStart_3855770 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3855770 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3855770 prefixEnd_3855770 := by exact prefixLift 3855770
  have htrace : WordTrace (prefixWord ++ tailWord_3855770) baseStart_3855770 baseEnd_3855770 := by
    simpa [prefixWord, tailWord_3855770, baseEnd_3855770] using wordTrace_append hprefix tailTrace_3855770
  have hstable : (prefixWord ++ tailWord_3855770).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3855770).length < 2 ^ (prefixWord ++ tailWord_3855770).sum := by decide
  have hdescent : baseEnd_3855770 < baseStart_3855770 := by decide
  rcases family_descends (prefixWord ++ tailWord_3855770) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3855810 : List Nat := [3, 5, 2, 1, 1, 1, 10]
def baseStart_3855810 : Nat := 118140960795 + 3855810 * 2 ^ 59
def prefixEnd_3855810 : Nat := 4983230072969 + 3 ^ 40 * 3855810 * 2
def baseEnd_3855810 : Nat := 24443010400156350115339

theorem tailTrace_3855810 : CollatzResearch.WordTrace tailWord_3855810 prefixEnd_3855810 24443010400156350115339 := by
  unfold tailWord_3855810
  simp only [CollatzResearch.WordTrace]
  refine ⟨35158236040266591191415221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 93755296107377576510440589 35158236040266591191415221)
  ·
    refine ⟨3296084628774992924195177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 35158236040266591191415221 3296084628774992924195177)
    ·
      refine ⟨2472063471581244693146383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3296084628774992924195177 2472063471581244693146383)
      ·
        refine ⟨3708095207371867039719575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2472063471581244693146383 3708095207371867039719575)
        ·
          refine ⟨5562142811057800559579363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3708095207371867039719575 5562142811057800559579363)
          ·
            refine ⟨8343214216586700839369045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5562142811057800559579363 8343214216586700839369045)
            ·
              refine ⟨24443010400156350115339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 8343214216586700839369045 24443010400156350115339)
              ·
                rfl

theorem cell23_3855810_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 2, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 2, 1, 1, 1, 10].length) (baseStart_3855810 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3855810 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3855810 prefixEnd_3855810 := by exact prefixLift 3855810
  have htrace : WordTrace (prefixWord ++ tailWord_3855810) baseStart_3855810 baseEnd_3855810 := by
    simpa [prefixWord, tailWord_3855810, baseEnd_3855810] using wordTrace_append hprefix tailTrace_3855810
  have hstable : (prefixWord ++ tailWord_3855810).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3855810).length < 2 ^ (prefixWord ++ tailWord_3855810).sum := by decide
  have hdescent : baseEnd_3855810 < baseStart_3855810 := by decide
  rcases family_descends (prefixWord ++ tailWord_3855810) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3855820 : List Nat := [2, 2, 1, 4, 2, 3, 1, 2, 2, 1, 3]
def baseStart_3855820 : Nat := 118140960795 + 3855820 * 2 ^ 59
def prefixEnd_3855820 : Nat := 4983230072969 + 3 ^ 40 * 3855820 * 2
def baseEnd_3855820 : Nat := 1979888977219209320217413

theorem tailTrace_3855820 : CollatzResearch.WordTrace tailWord_3855820 prefixEnd_3855820 1979888977219209320217413 := by
  unfold tailWord_3855820
  simp only [CollatzResearch.WordTrace]
  refine ⟨70316654445515068236762457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93755539260686757649016609 70316654445515068236762457)
  ·
    refine ⟨52737490834136301177571843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70316654445515068236762457 52737490834136301177571843)
    ·
      refine ⟨79106236251204451766357765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52737490834136301177571843 79106236251204451766357765)
      ·
        refine ⟨14832419297100834706192081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 79106236251204451766357765 14832419297100834706192081)
        ·
          refine ⟨11124314472825626029644061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14832419297100834706192081 11124314472825626029644061)
          ·
            refine ⟨4171617927309609761116523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11124314472825626029644061 4171617927309609761116523)
            ·
              refine ⟨6257426890964414641674785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4171617927309609761116523 6257426890964414641674785)
              ·
                refine ⟨4693070168223310981256089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6257426890964414641674785 4693070168223310981256089)
                ·
                  refine ⟨3519802626167483235942067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4693070168223310981256089 3519802626167483235942067)
                  ·
                    refine ⟨5279703939251224853913101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3519802626167483235942067 5279703939251224853913101)
                    ·
                      refine ⟨1979888977219209320217413, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5279703939251224853913101 1979888977219209320217413)
                      ·
                        rfl

theorem cell23_3855820_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 3, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 3, 1, 2, 2, 1, 3].length) (baseStart_3855820 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3855820 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3855820 prefixEnd_3855820 := by exact prefixLift 3855820
  have htrace : WordTrace (prefixWord ++ tailWord_3855820) baseStart_3855820 baseEnd_3855820 := by
    simpa [prefixWord, tailWord_3855820, baseEnd_3855820] using wordTrace_append hprefix tailTrace_3855820
  have hstable : (prefixWord ++ tailWord_3855820).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3855820).length < 2 ^ (prefixWord ++ tailWord_3855820).sum := by decide
  have hdescent : baseEnd_3855820 < baseStart_3855820 := by decide
  rcases family_descends (prefixWord ++ tailWord_3855820) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3855839 : List Nat := [1, 1, 2, 3, 3, 1, 1, 3, 2, 2, 4]
def baseStart_3855839 : Nat := 118140960795 + 3855839 * 2 ^ 59
def prefixEnd_3855839 : Nat := 4983230072969 + 3 ^ 40 * 3855839 * 2
def baseEnd_3855839 : Nat := 1979898733351644745879825

theorem tailTrace_3855839 : CollatzResearch.WordTrace tailWord_3855839 prefixEnd_3855839 1979898733351644745879825 := by
  unfold tailWord_3855839
  simp only [CollatzResearch.WordTrace]
  refine ⟨140634001877961302718466571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93756001251974201812311047 140634001877961302718466571)
  ·
    refine ⟨210951002816941954077699857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140634001877961302718466571 210951002816941954077699857)
    ·
      refine ⟨158213252112706465558274893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 210951002816941954077699857 158213252112706465558274893)
      ·
        refine ⟨59329969542264924584353085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 158213252112706465558274893 59329969542264924584353085)
        ·
          refine ⟨22248738578349346719132407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 59329969542264924584353085 22248738578349346719132407)
          ·
            refine ⟨33373107867524020078698611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22248738578349346719132407 33373107867524020078698611)
            ·
              refine ⟨50059661801286030118047917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33373107867524020078698611 50059661801286030118047917)
              ·
                refine ⟨18772373175482261294267969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 50059661801286030118047917 18772373175482261294267969)
                ·
                  refine ⟨14079279881611695970700977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18772373175482261294267969 14079279881611695970700977)
                  ·
                    refine ⟨10559459911208771978025733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14079279881611695970700977 10559459911208771978025733)
                    ·
                      refine ⟨1979898733351644745879825, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10559459911208771978025733 1979898733351644745879825)
                      ·
                        rfl

theorem cell23_3855839_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 1, 3, 2, 2, 4].length) (baseStart_3855839 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3855839 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3855839 prefixEnd_3855839 := by exact prefixLift 3855839
  have htrace : WordTrace (prefixWord ++ tailWord_3855839) baseStart_3855839 baseEnd_3855839 := by
    simpa [prefixWord, tailWord_3855839, baseEnd_3855839] using wordTrace_append hprefix tailTrace_3855839
  have hstable : (prefixWord ++ tailWord_3855839).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3855839).length < 2 ^ (prefixWord ++ tailWord_3855839).sum := by decide
  have hdescent : baseEnd_3855839 < baseStart_3855839 := by decide
  rcases family_descends (prefixWord ++ tailWord_3855839) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3855843 : List Nat := [1, 1, 1, 6, 2, 1, 3, 1, 1, 4, 2]
def baseStart_3855843 : Nat := 118140960795 + 3855843 * 2 ^ 59
def prefixEnd_3855843 : Nat := 4983230072969 + 3 ^ 40 * 3855843 * 2
def baseEnd_3855843 : Nat := 1979900787274262730229807

theorem tailTrace_3855843 : CollatzResearch.WordTrace tailWord_3855843 prefixEnd_3855843 1979900787274262730229807 := by
  unfold tailWord_3855843
  simp only [CollatzResearch.WordTrace]
  refine ⟨140634147769946811401612183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93756098513297874267741455 140634147769946811401612183)
  ·
    refine ⟨210951221654920217102418275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140634147769946811401612183 210951221654920217102418275)
    ·
      refine ⟨316426832482380325653627413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 210951221654920217102418275 316426832482380325653627413)
      ·
        refine ⟨14832507772611577765013785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 316426832482380325653627413 14832507772611577765013785)
        ·
          refine ⟨11124380829458683323760339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14832507772611577765013785 11124380829458683323760339)
          ·
            refine ⟨16686571244188024985640509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11124380829458683323760339 16686571244188024985640509)
            ·
              refine ⟨6257464216570509369615191, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16686571244188024985640509 6257464216570509369615191)
              ·
                refine ⟨9386196324855764054422787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6257464216570509369615191 9386196324855764054422787)
                ·
                  refine ⟨14079294487283646081634181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9386196324855764054422787 14079294487283646081634181)
                  ·
                    refine ⟨2639867716365683640306409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 14079294487283646081634181 2639867716365683640306409)
                    ·
                      refine ⟨1979900787274262730229807, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2639867716365683640306409 1979900787274262730229807)
                      ·
                        rfl

theorem cell23_3855843_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 1, 3, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 1, 3, 1, 1, 4, 2].length) (baseStart_3855843 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3855843 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3855843 prefixEnd_3855843 := by exact prefixLift 3855843
  have htrace : WordTrace (prefixWord ++ tailWord_3855843) baseStart_3855843 baseEnd_3855843 := by
    simpa [prefixWord, tailWord_3855843, baseEnd_3855843] using wordTrace_append hprefix tailTrace_3855843
  have hstable : (prefixWord ++ tailWord_3855843).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3855843).length < 2 ^ (prefixWord ++ tailWord_3855843).sum := by decide
  have hdescent : baseEnd_3855843 < baseStart_3855843 := by decide
  rcases family_descends (prefixWord ++ tailWord_3855843) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3855859 : List Nat := [1, 1, 1, 2, 2, 2, 2, 2, 4, 3, 3]
def baseStart_3855859 : Nat := 118140960795 + 3855859 * 2 ^ 59
def prefixEnd_3855859 : Nat := 4983230072969 + 3 ^ 40 * 3855859 * 2
def baseEnd_3855859 : Nat := 1979909002964734667629733

theorem tailTrace_3855859 : CollatzResearch.WordTrace tailWord_3855859 prefixEnd_3855859 1979909002964734667629733 := by
  unfold tailWord_3855859
  simp only [CollatzResearch.WordTrace]
  refine ⟨140634731337888846134194631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93756487558592564089463087 140634731337888846134194631)
  ·
    refine ⟨210952097006833269201291947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140634731337888846134194631 210952097006833269201291947)
    ·
      refine ⟨316428145510249903801937921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 210952097006833269201291947 316428145510249903801937921)
      ·
        refine ⟨237321109132687427851453441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 316428145510249903801937921 237321109132687427851453441)
        ·
          refine ⟨177990831849515570888590081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 237321109132687427851453441 177990831849515570888590081)
          ·
            refine ⟨133493123887136678166442561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 177990831849515570888590081 133493123887136678166442561)
            ·
              refine ⟨100119842915352508624831921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 133493123887136678166442561 100119842915352508624831921)
              ·
                refine ⟨75089882186514381468623941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 100119842915352508624831921 75089882186514381468623941)
                ·
                  refine ⟨14079352909971446525366989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 75089882186514381468623941 14079352909971446525366989)
                  ·
                    refine ⟨5279757341239292447012621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14079352909971446525366989 5279757341239292447012621)
                    ·
                      refine ⟨1979909002964734667629733, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5279757341239292447012621 1979909002964734667629733)
                      ·
                        rfl

theorem cell23_3855859_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 2, 2, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 2, 2, 4, 3, 3].length) (baseStart_3855859 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3855859 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3855859 prefixEnd_3855859 := by exact prefixLift 3855859
  have htrace : WordTrace (prefixWord ++ tailWord_3855859) baseStart_3855859 baseEnd_3855859 := by
    simpa [prefixWord, tailWord_3855859, baseEnd_3855859] using wordTrace_append hprefix tailTrace_3855859
  have hstable : (prefixWord ++ tailWord_3855859).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3855859).length < 2 ^ (prefixWord ++ tailWord_3855859).sum := by decide
  have hdescent : baseEnd_3855859 < baseStart_3855859 := by decide
  rcases family_descends (prefixWord ++ tailWord_3855859) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3855883 : List Nat := [1, 1, 1, 1, 9, 1, 1, 1, 7]
def baseStart_3855883 : Nat := 118140960795 + 3855883 * 2 ^ 59
def prefixEnd_3855883 : Nat := 4983230072969 + 3 ^ 40 * 3855883 * 2
def baseEnd_3855883 : Nat := 219991258500049174858847

theorem tailTrace_3855883 : CollatzResearch.WordTrace tailWord_3855883 prefixEnd_3855883 219991258500049174858847 := by
  unfold tailWord_3855883
  simp only [CollatzResearch.WordTrace]
  refine ⟨140635606689801898233068303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93757071126534598822045535 140635606689801898233068303)
  ·
    refine ⟨210953410034702847349602455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140635606689801898233068303 210953410034702847349602455)
    ·
      refine ⟨316430115052054271024403683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 210953410034702847349602455 316430115052054271024403683)
      ·
        refine ⟨474645172578081406536605525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 316430115052054271024403683 474645172578081406536605525)
        ·
          refine ⟨2781124058074695741425423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 9 474645172578081406536605525 2781124058074695741425423)
          ·
            refine ⟨4171686087112043612138135, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2781124058074695741425423 4171686087112043612138135)
            ·
              refine ⟨6257529130668065418207203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4171686087112043612138135 6257529130668065418207203)
              ·
                refine ⟨9386293696002098127310805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6257529130668065418207203 9386293696002098127310805)
                ·
                  refine ⟨219991258500049174858847, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 9386293696002098127310805 219991258500049174858847)
                  ·
                    rfl

theorem cell23_3855883_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 9, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 9, 1, 1, 1, 7].length) (baseStart_3855883 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3855883 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3855883 prefixEnd_3855883 := by exact prefixLift 3855883
  have htrace : WordTrace (prefixWord ++ tailWord_3855883) baseStart_3855883 baseEnd_3855883 := by
    simpa [prefixWord, tailWord_3855883, baseEnd_3855883] using wordTrace_append hprefix tailTrace_3855883
  have hstable : (prefixWord ++ tailWord_3855883).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3855883).length < 2 ^ (prefixWord ++ tailWord_3855883).sum := by decide
  have hdescent : baseEnd_3855883 < baseStart_3855883 := by decide
  rcases family_descends (prefixWord ++ tailWord_3855883) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3855889 : List Nat := [1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 5]
def baseStart_3855889 : Nat := 118140960795 + 3855889 * 2 ^ 59
def prefixEnd_3855889 : Nat := 4983230072969 + 3 ^ 40 * 3855889 * 2
def baseEnd_3855889 : Nat := 1979924407384369550254595

theorem tailTrace_3855889 : CollatzResearch.WordTrace tailWord_3855889 prefixEnd_3855889 1979924407384369550254595 := by
  unfold tailWord_3855889
  simp only [CollatzResearch.WordTrace]
  refine ⟨140635825527780161257786721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93757217018520107505191147 140635825527780161257786721)
  ·
    refine ⟨105476869145835120943340041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 140635825527780161257786721 105476869145835120943340041)
    ·
      refine ⟨79107651859376340707505031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 105476869145835120943340041 79107651859376340707505031)
      ·
        refine ⟨118661477789064511061257547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79107651859376340707505031 118661477789064511061257547)
        ·
          refine ⟨177992216683596766591886321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 118661477789064511061257547 177992216683596766591886321)
          ·
            refine ⟨133494162512697574943914741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 177992216683596766591886321 133494162512697574943914741)
            ·
              refine ⟨12515077735565397650992007, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 133494162512697574943914741 12515077735565397650992007)
              ·
                refine ⟨18772616603348096476488011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12515077735565397650992007 18772616603348096476488011)
                ·
                  refine ⟨28158924905022144714732017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18772616603348096476488011 28158924905022144714732017)
                  ·
                    refine ⟨21119193678766608536049013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 28158924905022144714732017 21119193678766608536049013)
                    ·
                      refine ⟨1979924407384369550254595, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 21119193678766608536049013 1979924407384369550254595)
                      ·
                        rfl

theorem cell23_3855889_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 5].length) (baseStart_3855889 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3855889 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3855889 prefixEnd_3855889 := by exact prefixLift 3855889
  have htrace : WordTrace (prefixWord ++ tailWord_3855889) baseStart_3855889 baseEnd_3855889 := by
    simpa [prefixWord, tailWord_3855889, baseEnd_3855889] using wordTrace_append hprefix tailTrace_3855889
  have hstable : (prefixWord ++ tailWord_3855889).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3855889).length < 2 ^ (prefixWord ++ tailWord_3855889).sum := by decide
  have hdescent : baseEnd_3855889 < baseStart_3855889 := by decide
  rcases family_descends (prefixWord ++ tailWord_3855889) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3855916 : List Nat := [2, 2, 1, 1, 1, 2, 1, 1, 6, 4, 2]
def baseStart_3855916 : Nat := 118140960795 + 3855916 * 2 ^ 59
def prefixEnd_3855916 : Nat := 4983230072969 + 3 ^ 40 * 3855916 * 2
def baseEnd_3855916 : Nat := 1979938271362040944616971

theorem tailTrace_3855916 : CollatzResearch.WordTrace tailWord_3855916 prefixEnd_3855916 1979938271362040944616971 := by
  unfold tailWord_3855916
  simp only [CollatzResearch.WordTrace]
  refine ⟨70318405149341172434509801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93757873532454896579346401 70318405149341172434509801)
  ·
    refine ⟨52738803862005879325882351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70318405149341172434509801 52738803862005879325882351)
    ·
      refine ⟨79108205793008818988823527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52738803862005879325882351 79108205793008818988823527)
      ·
        refine ⟨118662308689513228483235291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79108205793008818988823527 118662308689513228483235291)
        ·
          refine ⟨177993463034269842724852937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 118662308689513228483235291 177993463034269842724852937)
          ·
            refine ⟨133495097275702382043639703, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 177993463034269842724852937 133495097275702382043639703)
            ·
              refine ⟨200242645913553573065459555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 133495097275702382043639703 200242645913553573065459555)
              ·
                refine ⟨300363968870330359598189333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 200242645913553573065459555 300363968870330359598189333)
                ·
                  refine ⟨14079561040796735606165125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 300363968870330359598189333 14079561040796735606165125)
                  ·
                    refine ⟨2639917695149387926155961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 14079561040796735606165125 2639917695149387926155961)
                    ·
                      refine ⟨1979938271362040944616971, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2639917695149387926155961 1979938271362040944616971)
                      ·
                        rfl

theorem cell23_3855916_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 4, 2].length) (baseStart_3855916 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3855916 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3855916 prefixEnd_3855916 := by exact prefixLift 3855916
  have htrace : WordTrace (prefixWord ++ tailWord_3855916) baseStart_3855916 baseEnd_3855916 := by
    simpa [prefixWord, tailWord_3855916, baseEnd_3855916] using wordTrace_append hprefix tailTrace_3855916
  have hstable : (prefixWord ++ tailWord_3855916).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3855916).length < 2 ^ (prefixWord ++ tailWord_3855916).sum := by decide
  have hdescent : baseEnd_3855916 < baseStart_3855916 := by decide
  rcases family_descends (prefixWord ++ tailWord_3855916) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3855956 : List Nat := [2, 4, 1, 1, 1, 2, 1, 5, 6]
def baseStart_3855956 : Nat := 118140960795 + 3855956 * 2 ^ 59
def prefixEnd_3855956 : Nat := 4983230072969 + 3 ^ 40 * 3855956 * 2
def baseEnd_3855956 : Nat := 219995423398691198679643

theorem tailTrace_3855956 : CollatzResearch.WordTrace tailWord_3855956 prefixEnd_3855956 219995423398691198679643 := by
  unfold tailWord_3855956
  simp only [CollatzResearch.WordTrace]
  refine ⟨70319134609268715850237861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93758846145691621133650481 70319134609268715850237861)
  ·
    refine ⟨13184837739237884221919599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 70319134609268715850237861 13184837739237884221919599)
    ·
      refine ⟨19777256608856826332879399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13184837739237884221919599 19777256608856826332879399)
      ·
        refine ⟨29665884913285239499319099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19777256608856826332879399 29665884913285239499319099)
        ·
          refine ⟨44498827369927859248978649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29665884913285239499319099 44498827369927859248978649)
          ·
            refine ⟨33374120527445894436733987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44498827369927859248978649 33374120527445894436733987)
            ·
              refine ⟨50061180791168841655100981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33374120527445894436733987 50061180791168841655100981)
              ·
                refine ⟨4693235699172078905165717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 50061180791168841655100981 4693235699172078905165717)
                ·
                  refine ⟨219995423398691198679643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4693235699172078905165717 219995423398691198679643)
                  ·
                    rfl

theorem cell23_3855956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 1, 5, 6].length) (baseStart_3855956 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3855956 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3855956 prefixEnd_3855956 := by exact prefixLift 3855956
  have htrace : WordTrace (prefixWord ++ tailWord_3855956) baseStart_3855956 baseEnd_3855956 := by
    simpa [prefixWord, tailWord_3855956, baseEnd_3855956] using wordTrace_append hprefix tailTrace_3855956
  have hstable : (prefixWord ++ tailWord_3855956).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3855956).length < 2 ^ (prefixWord ++ tailWord_3855956).sum := by decide
  have hdescent : baseEnd_3855956 < baseStart_3855956 := by decide
  rcases family_descends (prefixWord ++ tailWord_3855956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3855990 : List Nat := [5, 1, 1, 2, 2, 3, 1, 2, 6]
def baseStart_3855990 : Nat := 118140960795 + 3855990 * 2 ^ 59
def prefixEnd_3855990 : Nat := 4983230072969 + 3 ^ 40 * 3855990 * 2
def baseEnd_3855990 : Nat := 219997363214497072787959

theorem tailTrace_3855990 : CollatzResearch.WordTrace tailWord_3855990 prefixEnd_3855990 219997363214497072787959 := by
  unfold tailWord_3855990
  simp only [CollatzResearch.WordTrace]
  refine ⟨8789969331275890969200839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 93759672866942837004808949 8789969331275890969200839)
  ·
    refine ⟨13184953996913836453801259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8789969331275890969200839 13184953996913836453801259)
    ·
      refine ⟨19777430995370754680701889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13184953996913836453801259 19777430995370754680701889)
      ·
        refine ⟨14833073246528066010526417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19777430995370754680701889 14833073246528066010526417)
        ·
          refine ⟨11124804934896049507894813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14833073246528066010526417 11124804934896049507894813)
          ·
            refine ⟨4171801850586018565460555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11124804934896049507894813 4171801850586018565460555)
            ·
              refine ⟨6257702775879027848190833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4171801850586018565460555 6257702775879027848190833)
              ·
                refine ⟨4693277081909270886143125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6257702775879027848190833 4693277081909270886143125)
                ·
                  refine ⟨219997363214497072787959, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4693277081909270886143125 219997363214497072787959)
                  ·
                    rfl

theorem cell23_3855990_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 3, 1, 2, 6].length) (baseStart_3855990 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3855990 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3855990 prefixEnd_3855990 := by exact prefixLift 3855990
  have htrace : WordTrace (prefixWord ++ tailWord_3855990) baseStart_3855990 baseEnd_3855990 := by
    simpa [prefixWord, tailWord_3855990, baseEnd_3855990] using wordTrace_append hprefix tailTrace_3855990
  have hstable : (prefixWord ++ tailWord_3855990).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3855990).length < 2 ^ (prefixWord ++ tailWord_3855990).sum := by decide
  have hdescent : baseEnd_3855990 < baseStart_3855990 := by decide
  rcases family_descends (prefixWord ++ tailWord_3855990) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3855993 : List Nat := [1, 2, 1, 3, 3, 1, 2, 1, 4, 3, 2]
def baseStart_3855993 : Nat := 118140960795 + 3855993 * 2 ^ 59
def prefixEnd_3855993 : Nat := 4983230072969 + 3 ^ 40 * 3855993 * 2
def baseEnd_3855993 : Nat := 1979977809372437143354117

theorem tailTrace_3855993 : CollatzResearch.WordTrace tailWord_3855993 prefixEnd_3855993 1979977809372437143354117 := by
  unfold tailWord_3855993
  simp only [CollatzResearch.WordTrace]
  refine ⟨140639618719403387019572633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93759745812935591346381755 140639618719403387019572633)
  ·
    refine ⟨105479714039552540264679475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 140639618719403387019572633 105479714039552540264679475)
    ·
      refine ⟨158219571059328810397019213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105479714039552540264679475 158219571059328810397019213)
      ·
        refine ⟨59332339147248303898882205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 158219571059328810397019213 59332339147248303898882205)
        ·
          refine ⟨22249627180218113962080827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 59332339147248303898882205 22249627180218113962080827)
          ·
            refine ⟨33374440770327170943121241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22249627180218113962080827 33374440770327170943121241)
            ·
              refine ⟨25030830577745378207340931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33374440770327170943121241 25030830577745378207340931)
              ·
                refine ⟨37546245866618067311011397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25030830577745378207340931 37546245866618067311011397)
                ·
                  refine ⟨7039921099990887620814637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 37546245866618067311011397 7039921099990887620814637)
                  ·
                    refine ⟨2639970412496582857805489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7039921099990887620814637 2639970412496582857805489)
                    ·
                      refine ⟨1979977809372437143354117, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2639970412496582857805489 1979977809372437143354117)
                      ·
                        rfl

theorem cell23_3855993_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 2, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 2, 1, 4, 3, 2].length) (baseStart_3855993 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3855993 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3855993 prefixEnd_3855993 := by exact prefixLift 3855993
  have htrace : WordTrace (prefixWord ++ tailWord_3855993) baseStart_3855993 baseEnd_3855993 := by
    simpa [prefixWord, tailWord_3855993, baseEnd_3855993] using wordTrace_append hprefix tailTrace_3855993
  have hstable : (prefixWord ++ tailWord_3855993).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3855993).length < 2 ^ (prefixWord ++ tailWord_3855993).sum := by decide
  have hdescent : baseEnd_3855993 < baseStart_3855993 := by decide
  rcases family_descends (prefixWord ++ tailWord_3855993) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3856000 : List Nat := [2, 1, 1, 2, 1, 4, 1, 6, 1, 1, 3]
def baseStart_3856000 : Nat := 118140960795 + 3856000 * 2 ^ 59
def prefixEnd_3856000 : Nat := 4983230072969 + 3 ^ 40 * 3856000 * 2
def baseEnd_3856000 : Nat := 1979981403737018615966585

theorem tailTrace_3856000 : CollatzResearch.WordTrace tailWord_3856000 prefixEnd_3856000 1979981403737018615966585 := by
  unfold tailWord_3856000
  simp only [CollatzResearch.WordTrace]
  refine ⟨70319937015189013607538727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93759916020252018143384969 70319937015189013607538727)
  ·
    refine ⟨105479905522783520411308091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70319937015189013607538727 105479905522783520411308091)
    ·
      refine ⟨158219858284175280616962137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105479905522783520411308091 158219858284175280616962137)
      ·
        refine ⟨118664893713131460462721603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 158219858284175280616962137 118664893713131460462721603)
        ·
          refine ⟨177997340569697190694082405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 118664893713131460462721603 177997340569697190694082405)
          ·
            refine ⟨33374501356818223255140451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 177997340569697190694082405 33374501356818223255140451)
            ·
              refine ⟨50061752035227334882710677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33374501356818223255140451 50061752035227334882710677)
              ·
                refine ⟨2346644626651281322627063, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 50061752035227334882710677 2346644626651281322627063)
                ·
                  refine ⟨3519966939976921983940595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2346644626651281322627063 3519966939976921983940595)
                  ·
                    refine ⟨5279950409965382975910893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3519966939976921983940595 5279950409965382975910893)
                    ·
                      refine ⟨1979981403737018615966585, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5279950409965382975910893 1979981403737018615966585)
                      ·
                        rfl

theorem cell23_3856000_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 1, 6, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 1, 6, 1, 1, 3].length) (baseStart_3856000 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3856000 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3856000 prefixEnd_3856000 := by exact prefixLift 3856000
  have htrace : WordTrace (prefixWord ++ tailWord_3856000) baseStart_3856000 baseEnd_3856000 := by
    simpa [prefixWord, tailWord_3856000, baseEnd_3856000] using wordTrace_append hprefix tailTrace_3856000
  have hstable : (prefixWord ++ tailWord_3856000).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3856000).length < 2 ^ (prefixWord ++ tailWord_3856000).sum := by decide
  have hdescent : baseEnd_3856000 < baseStart_3856000 := by decide
  rcases family_descends (prefixWord ++ tailWord_3856000) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3856023 : List Nat := [1, 1, 3, 3, 2, 2, 1, 4, 1, 1, 4]
def baseStart_3856023 : Nat := 118140960795 + 3856023 * 2 ^ 59
def prefixEnd_3856023 : Nat := 4983230072969 + 3 ^ 40 * 3856023 * 2
def baseEnd_3856023 : Nat := 1979993213792072025978979

theorem tailTrace_3856023 : CollatzResearch.WordTrace tailWord_3856023 prefixEnd_3856023 1979993213792072025978979 := by
  unfold tailWord_3856023
  simp only [CollatzResearch.WordTrace]
  refine ⟨140640712909294702143164723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93760475272863134762109815 140640712909294702143164723)
  ·
    refine ⟨210961069363942053214747085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140640712909294702143164723 210961069363942053214747085)
    ·
      refine ⟨79110401011478269955530157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 210961069363942053214747085 79110401011478269955530157)
      ·
        refine ⟨29666400379304351233323809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 79110401011478269955530157 29666400379304351233323809)
        ·
          refine ⟨22249800284478263424992857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29666400379304351233323809 22249800284478263424992857)
          ·
            refine ⟨16687350213358697568744643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22249800284478263424992857 16687350213358697568744643)
            ·
              refine ⟨25031025320038046353116965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16687350213358697568744643 25031025320038046353116965)
              ·
                refine ⟨4693317247507133691209431, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25031025320038046353116965 4693317247507133691209431)
                ·
                  refine ⟨7039975871260700536814147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4693317247507133691209431 7039975871260700536814147)
                  ·
                    refine ⟨10559963806891050805221221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7039975871260700536814147 10559963806891050805221221)
                    ·
                      refine ⟨1979993213792072025978979, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10559963806891050805221221 1979993213792072025978979)
                      ·
                        rfl

theorem cell23_3856023_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 2, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 2, 1, 4, 1, 1, 4].length) (baseStart_3856023 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3856023 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3856023 prefixEnd_3856023 := by exact prefixLift 3856023
  have htrace : WordTrace (prefixWord ++ tailWord_3856023) baseStart_3856023 baseEnd_3856023 := by
    simpa [prefixWord, tailWord_3856023, baseEnd_3856023] using wordTrace_append hprefix tailTrace_3856023
  have hstable : (prefixWord ++ tailWord_3856023).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3856023).length < 2 ^ (prefixWord ++ tailWord_3856023).sum := by decide
  have hdescent : baseEnd_3856023 < baseStart_3856023 := by decide
  rcases family_descends (prefixWord ++ tailWord_3856023) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3856033 : List Nat := [1, 2, 3, 3, 2, 1, 1, 2, 4, 4]
def baseStart_3856033 : Nat := 118140960795 + 3856033 * 2 ^ 59
def prefixEnd_3856033 : Nat := 4983230072969 + 3 ^ 40 * 3856033 * 2
def baseEnd_3856033 : Nat := 659999449532872328951311

theorem tailTrace_3856033 : CollatzResearch.WordTrace tailWord_3856033 prefixEnd_3856033 659999449532872328951311 := by
  unfold tailWord_3856033
  simp only [CollatzResearch.WordTrace]
  refine ⟨140641077639258473851028753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93760718426172315900685835 140641077639258473851028753)
  ·
    refine ⟨105480808229443855388271565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 140641077639258473851028753 105480808229443855388271565)
    ·
      refine ⟨39555303086041445770601837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 105480808229443855388271565 39555303086041445770601837)
      ·
        refine ⟨14833238657265542163975689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 39555303086041445770601837 14833238657265542163975689)
        ·
          refine ⟨11124928992949156622981767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14833238657265542163975689 11124928992949156622981767)
          ·
            refine ⟨16687393489423734934472651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11124928992949156622981767 16687393489423734934472651)
            ·
              refine ⟨25031090234135602401708977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16687393489423734934472651 25031090234135602401708977)
              ·
                refine ⟨18773317675601701801281733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25031090234135602401708977 18773317675601701801281733)
                ·
                  refine ⟨3519997064175319087740325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 18773317675601701801281733 3519997064175319087740325)
                  ·
                    refine ⟨659999449532872328951311, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3519997064175319087740325 659999449532872328951311)
                    ·
                      rfl

theorem cell23_3856033_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 1, 1, 2, 4, 4].length) (baseStart_3856033 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3856033 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3856033 prefixEnd_3856033 := by exact prefixLift 3856033
  have htrace : WordTrace (prefixWord ++ tailWord_3856033) baseStart_3856033 baseEnd_3856033 := by
    simpa [prefixWord, tailWord_3856033, baseEnd_3856033] using wordTrace_append hprefix tailTrace_3856033
  have hstable : (prefixWord ++ tailWord_3856033).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3856033).length < 2 ^ (prefixWord ++ tailWord_3856033).sum := by decide
  have hdescent : baseEnd_3856033 < baseStart_3856033 := by decide
  rcases family_descends (prefixWord ++ tailWord_3856033) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3856057 : List Nat := [1, 2, 1, 4, 1, 1, 2, 6, 1, 2, 2]
def baseStart_3856057 : Nat := 118140960795 + 3856057 * 2 ^ 59
def prefixEnd_3856057 : Nat := 4983230072969 + 3 ^ 40 * 3856057 * 2
def baseEnd_3856057 : Nat := 1980010672134324892953823

theorem tailTrace_3856057 : CollatzResearch.WordTrace tailWord_3856057 prefixEnd_3856057 1980010672134324892953823 := by
  unfold tailWord_3856057
  simp only [CollatzResearch.WordTrace]
  refine ⟨140641952991171525949902425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93761301994114350633268283 140641952991171525949902425)
  ·
    refine ⟨105481464743378644462426819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 140641952991171525949902425 105481464743378644462426819)
    ·
      refine ⟨158222197115067966693640229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105481464743378644462426819 158222197115067966693640229)
      ·
        refine ⟨29666661959075243755057543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 158222197115067966693640229 29666661959075243755057543)
        ·
          refine ⟨44499992938612865632586315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29666661959075243755057543 44499992938612865632586315)
          ·
            refine ⟨66749989407919298448879473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44499992938612865632586315 66749989407919298448879473)
            ·
              refine ⟨50062492055939473836659605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 66749989407919298448879473 50062492055939473836659605)
              ·
                refine ⟨2346679315122162836093419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 50062492055939473836659605 2346679315122162836093419)
                ·
                  refine ⟨3520018972683244254140129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2346679315122162836093419 3520018972683244254140129)
                  ·
                    refine ⟨2640014229512433190605097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3520018972683244254140129 2640014229512433190605097)
                    ·
                      refine ⟨1980010672134324892953823, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2640014229512433190605097 1980010672134324892953823)
                      ·
                        rfl

theorem cell23_3856057_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 2, 6, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 2, 6, 1, 2, 2].length) (baseStart_3856057 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3856057 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3856057 prefixEnd_3856057 := by exact prefixLift 3856057
  have htrace : WordTrace (prefixWord ++ tailWord_3856057) baseStart_3856057 baseEnd_3856057 := by
    simpa [prefixWord, tailWord_3856057, baseEnd_3856057] using wordTrace_append hprefix tailTrace_3856057
  have hstable : (prefixWord ++ tailWord_3856057).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3856057).length < 2 ^ (prefixWord ++ tailWord_3856057).sum := by decide
  have hdescent : baseEnd_3856057 < baseStart_3856057 := by decide
  rcases family_descends (prefixWord ++ tailWord_3856057) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3856077 : List Nat := [1, 6, 2, 1, 1, 2, 1, 1, 3, 2, 3]
def baseStart_3856077 : Nat := 118140960795 + 3856077 * 2 ^ 59
def prefixEnd_3856077 : Nat := 4983230072969 + 3 ^ 40 * 3856077 * 2
def baseEnd_3856077 : Nat := 1980020941747414814703731

theorem tailTrace_3856077 : CollatzResearch.WordTrace tailWord_3856077 prefixEnd_3856077 1980020941747414814703731 := by
  unfold tailWord_3856077
  simp only [CollatzResearch.WordTrace]
  refine ⟨140642682451099069365630485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93761788300732712910420323 140642682451099069365630485)
  ·
    refine ⟨6592625739895268876513929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 140642682451099069365630485 6592625739895268876513929)
    ·
      refine ⟨4944469304921451657385447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6592625739895268876513929 4944469304921451657385447)
      ·
        refine ⟨7416703957382177486078171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4944469304921451657385447 7416703957382177486078171)
        ·
          refine ⟨11125055936073266229117257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7416703957382177486078171 11125055936073266229117257)
          ·
            refine ⟨8343791952054949671837943, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11125055936073266229117257 8343791952054949671837943)
            ·
              refine ⟨12515687928082424507756915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8343791952054949671837943 12515687928082424507756915)
              ·
                refine ⟨18773531892123636761635373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12515687928082424507756915 18773531892123636761635373)
                ·
                  refine ⟨7040074459546363785613265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18773531892123636761635373 7040074459546363785613265)
                  ·
                    refine ⟨5280055844659772839209949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7040074459546363785613265 5280055844659772839209949)
                    ·
                      refine ⟨1980020941747414814703731, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5280055844659772839209949 1980020941747414814703731)
                      ·
                        rfl

theorem cell23_3856077_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 2, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 2, 1, 1, 3, 2, 3].length) (baseStart_3856077 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3856077 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3856077 prefixEnd_3856077 := by exact prefixLift 3856077
  have htrace : WordTrace (prefixWord ++ tailWord_3856077) baseStart_3856077 baseEnd_3856077 := by
    simpa [prefixWord, tailWord_3856077, baseEnd_3856077] using wordTrace_append hprefix tailTrace_3856077
  have hstable : (prefixWord ++ tailWord_3856077).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3856077).length < 2 ^ (prefixWord ++ tailWord_3856077).sum := by decide
  have hdescent : baseEnd_3856077 < baseStart_3856077 := by decide
  rcases family_descends (prefixWord ++ tailWord_3856077) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3856158 : List Nat := [4, 3, 2, 2, 1, 2, 1, 2, 2, 1, 3]
def baseStart_3856158 : Nat := 118140960795 + 3856158 * 2 ^ 59
def prefixEnd_3856158 : Nat := 4983230072969 + 3 ^ 40 * 3856158 * 2
def baseEnd_3856158 : Nat := 1980062533680428997790859

theorem tailTrace_3856158 : CollatzResearch.WordTrace tailWord_3856158 prefixEnd_3856158 1980062533680428997790859 := by
  unfold tailWord_3856158
  simp only [CollatzResearch.WordTrace]
  refine ⟨17580704595475702524916141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 93763757842537080132886085 17580704595475702524916141)
  ·
    refine ⟨6592764223303388446843553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17580704595475702524916141 6592764223303388446843553)
    ·
      refine ⟨4944573167477541335132665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6592764223303388446843553 4944573167477541335132665)
      ·
        refine ⟨3708429875608156001349499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4944573167477541335132665 3708429875608156001349499)
        ·
          refine ⟨5562644813412234002024249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3708429875608156001349499 5562644813412234002024249)
          ·
            refine ⟨4171983610059175501518187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5562644813412234002024249 4171983610059175501518187)
            ·
              refine ⟨6257975415088763252277281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4171983610059175501518187 6257975415088763252277281)
              ·
                refine ⟨4693481561316572439207961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6257975415088763252277281 4693481561316572439207961)
                ·
                  refine ⟨3520111170987429329405971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4693481561316572439207961 3520111170987429329405971)
                  ·
                    refine ⟨5280166756481143994108957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3520111170987429329405971 5280166756481143994108957)
                    ·
                      refine ⟨1980062533680428997790859, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5280166756481143994108957 1980062533680428997790859)
                      ·
                        rfl

theorem cell23_3856158_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 2, 1, 2, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 2, 1, 2, 1, 2, 2, 1, 3].length) (baseStart_3856158 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3856158 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3856158 prefixEnd_3856158 := by exact prefixLift 3856158
  have htrace : WordTrace (prefixWord ++ tailWord_3856158) baseStart_3856158 baseEnd_3856158 := by
    simpa [prefixWord, tailWord_3856158, baseEnd_3856158] using wordTrace_append hprefix tailTrace_3856158
  have hstable : (prefixWord ++ tailWord_3856158).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3856158).length < 2 ^ (prefixWord ++ tailWord_3856158).sum := by decide
  have hdescent : baseEnd_3856158 < baseStart_3856158 := by decide
  rcases family_descends (prefixWord ++ tailWord_3856158) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3856163 : List Nat := [1, 1, 1, 4, 2, 1, 3, 2, 2, 3, 3]
def baseStart_3856163 : Nat := 118140960795 + 3856163 * 2 ^ 59
def prefixEnd_3856163 : Nat := 4983230072969 + 3 ^ 40 * 3856163 * 2
def baseEnd_3856163 : Nat := 1980065101083701478228335

theorem tailTrace_3856163 : CollatzResearch.WordTrace tailWord_3856163 prefixEnd_3856163 1980065101083701478228335 := by
  unfold tailWord_3856163
  simp only [CollatzResearch.WordTrace]
  refine ⟨140645819128787506053261143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93763879419191670702174095 140645819128787506053261143)
  ·
    refine ⟨210968728693181259079891715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140645819128787506053261143 210968728693181259079891715)
    ·
      refine ⟨316453093039771888619837573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 210968728693181259079891715 316453093039771888619837573)
      ·
        refine ⟨59334954944957229116219545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 316453093039771888619837573 59334954944957229116219545)
        ·
          refine ⟨44501216208717921837164659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59334954944957229116219545 44501216208717921837164659)
          ·
            refine ⟨66751824313076882755746989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44501216208717921837164659 66751824313076882755746989)
            ·
              refine ⟨25031934117403831033405121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 66751824313076882755746989 25031934117403831033405121)
              ·
                refine ⟨18773950588052873275053841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25031934117403831033405121 18773950588052873275053841)
                ·
                  refine ⟨14080462941039654956290381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18773950588052873275053841 14080462941039654956290381)
                  ·
                    refine ⟨5280173602889870608608893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14080462941039654956290381 5280173602889870608608893)
                    ·
                      refine ⟨1980065101083701478228335, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5280173602889870608608893 1980065101083701478228335)
                      ·
                        rfl

theorem cell23_3856163_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 3, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 3, 2, 2, 3, 3].length) (baseStart_3856163 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3856163 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3856163 prefixEnd_3856163 := by exact prefixLift 3856163
  have htrace : WordTrace (prefixWord ++ tailWord_3856163) baseStart_3856163 baseEnd_3856163 := by
    simpa [prefixWord, tailWord_3856163, baseEnd_3856163] using wordTrace_append hprefix tailTrace_3856163
  have hstable : (prefixWord ++ tailWord_3856163).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3856163).length < 2 ^ (prefixWord ++ tailWord_3856163).sum := by decide
  have hdescent : baseEnd_3856163 < baseStart_3856163 := by decide
  rcases family_descends (prefixWord ++ tailWord_3856163) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3856164 : List Nat := [2, 3, 1, 3, 2, 1, 3, 2, 2, 2, 2]
def baseStart_3856164 : Nat := 118140960795 + 3856164 * 2 ^ 59
def prefixEnd_3856164 : Nat := 4983230072969 + 3 ^ 40 * 3856164 * 2
def baseEnd_3856164 : Nat := 1980065614564355974315831

theorem tailTrace_3856164 : CollatzResearch.WordTrace tailWord_3856164 prefixEnd_3856164 1980065614564355974315831 := by
  unfold tailWord_3856164
  simp only [CollatzResearch.WordTrace]
  refine ⟨70322927800891941612023773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93763903734522588816031697 70322927800891941612023773)
  ·
    refine ⟨26371097925334478104508915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 70322927800891941612023773 26371097925334478104508915)
    ·
      refine ⟨39556646888001717156763373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26371097925334478104508915 39556646888001717156763373)
      ·
        refine ⟨14833742583000643933786265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 39556646888001717156763373 14833742583000643933786265)
        ·
          refine ⟨11125306937250482950339699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14833742583000643933786265 11125306937250482950339699)
          ·
            refine ⟨16687960405875724425509549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11125306937250482950339699 16687960405875724425509549)
            ·
              refine ⟨6257985152203396659566081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16687960405875724425509549 6257985152203396659566081)
              ·
                refine ⟨4693488864152547494674561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6257985152203396659566081 4693488864152547494674561)
                ·
                  refine ⟨3520116648114410621005921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4693488864152547494674561 3520116648114410621005921)
                  ·
                    refine ⟨2640087486085807965754441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3520116648114410621005921 2640087486085807965754441)
                    ·
                      refine ⟨1980065614564355974315831, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2640087486085807965754441 1980065614564355974315831)
                      ·
                        rfl

theorem cell23_3856164_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 1, 3, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 1, 3, 2, 2, 2, 2].length) (baseStart_3856164 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3856164 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3856164 prefixEnd_3856164 := by exact prefixLift 3856164
  have htrace : WordTrace (prefixWord ++ tailWord_3856164) baseStart_3856164 baseEnd_3856164 := by
    simpa [prefixWord, tailWord_3856164, baseEnd_3856164] using wordTrace_append hprefix tailTrace_3856164
  have hstable : (prefixWord ++ tailWord_3856164).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3856164).length < 2 ^ (prefixWord ++ tailWord_3856164).sum := by decide
  have hdescent : baseEnd_3856164 < baseStart_3856164 := by decide
  rcases family_descends (prefixWord ++ tailWord_3856164) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3856181 : List Nat := [1, 3, 3, 1, 4, 1, 3, 1, 2, 2, 2]
def baseStart_3856181 : Nat := 118140960795 + 3856181 * 2 ^ 59
def prefixEnd_3856181 : Nat := 4983230072969 + 3 ^ 40 * 3856181 * 2
def baseEnd_3856181 : Nat := 1980074343735482407803253

theorem tailTrace_3856181 : CollatzResearch.WordTrace tailWord_3856181 prefixEnd_3856181 1980074343735482407803253 := by
  unfold tailWord_3856181
  simp only [CollatzResearch.WordTrace]
  refine ⟨140646475642722295127416397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93764317095148196751610931 140646475642722295127416397)
  ·
    refine ⟨52742428366020860672781149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 140646475642722295127416397 52742428366020860672781149)
    ·
      refine ⟨19778410637257822752292931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 52742428366020860672781149 19778410637257822752292931)
      ·
        refine ⟨29667615955886734128439397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19778410637257822752292931 29667615955886734128439397)
        ·
          refine ⟨5562677991728762649082387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 29667615955886734128439397 5562677991728762649082387)
          ·
            refine ⟨8344016987593143973623581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5562677991728762649082387 8344016987593143973623581)
            ·
              refine ⟨3129006370347428990108843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8344016987593143973623581 3129006370347428990108843)
              ·
                refine ⟨4693509555521143485163265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3129006370347428990108843 4693509555521143485163265)
                ·
                  refine ⟨3520132166640857613872449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4693509555521143485163265 3520132166640857613872449)
                  ·
                    refine ⟨2640099124980643210404337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3520132166640857613872449 2640099124980643210404337)
                    ·
                      refine ⟨1980074343735482407803253, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2640099124980643210404337 1980074343735482407803253)
                      ·
                        rfl

theorem cell23_3856181_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 4, 1, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 4, 1, 3, 1, 2, 2, 2].length) (baseStart_3856181 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3856181 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3856181 prefixEnd_3856181 := by exact prefixLift 3856181
  have htrace : WordTrace (prefixWord ++ tailWord_3856181) baseStart_3856181 baseEnd_3856181 := by
    simpa [prefixWord, tailWord_3856181, baseEnd_3856181] using wordTrace_append hprefix tailTrace_3856181
  have hstable : (prefixWord ++ tailWord_3856181).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3856181).length < 2 ^ (prefixWord ++ tailWord_3856181).sum := by decide
  have hdescent : baseEnd_3856181 < baseStart_3856181 := by decide
  rcases family_descends (prefixWord ++ tailWord_3856181) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3856204 : List Nat := [2, 2, 1, 3, 5, 1, 1, 3, 5]
def baseStart_3856204 : Nat := 118140960795 + 3856204 * 2 ^ 59
def prefixEnd_3856204 : Nat := 4983230072969 + 3 ^ 40 * 3856204 * 2
def baseEnd_3856204 : Nat := 220009572643392868646183

theorem tailTrace_3856204 : CollatzResearch.WordTrace tailWord_3856204 prefixEnd_3856204 220009572643392868646183 := by
  unfold tailWord_3856204
  simp only [CollatzResearch.WordTrace]
  refine ⟨70323657260819485027751833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93764876347759313370335777 70323657260819485027751833)
  ·
    refine ⟨52742742945614613770813875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70323657260819485027751833 52742742945614613770813875)
    ·
      refine ⟨79114114418421920656220813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52742742945614613770813875 79114114418421920656220813)
      ·
        refine ⟨29667792906908220246082805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 79114114418421920656220813 29667792906908220246082805)
        ·
          refine ⟨2781355585022645648070263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 29667792906908220246082805 2781355585022645648070263)
          ·
            refine ⟨4172033377533968472105395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2781355585022645648070263 4172033377533968472105395)
            ·
              refine ⟨6258050066300952708158093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4172033377533968472105395 6258050066300952708158093)
              ·
                refine ⟨2346768774862857265559285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6258050066300952708158093 2346768774862857265559285)
                ·
                  refine ⟨220009572643392868646183, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2346768774862857265559285 220009572643392868646183)
                  ·
                    rfl

theorem cell23_3856204_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 5, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 5, 1, 1, 3, 5].length) (baseStart_3856204 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3856204 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3856204 prefixEnd_3856204 := by exact prefixLift 3856204
  have htrace : WordTrace (prefixWord ++ tailWord_3856204) baseStart_3856204 baseEnd_3856204 := by
    simpa [prefixWord, tailWord_3856204, baseEnd_3856204] using wordTrace_append hprefix tailTrace_3856204
  have hstable : (prefixWord ++ tailWord_3856204).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3856204).length < 2 ^ (prefixWord ++ tailWord_3856204).sum := by decide
  have hdescent : baseEnd_3856204 < baseStart_3856204 := by decide
  rcases family_descends (prefixWord ++ tailWord_3856204) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3856254 : List Nat := [4, 2, 3, 1, 1, 2, 2, 1, 2, 1, 4]
def baseStart_3856254 : Nat := 118140960795 + 3856254 * 2 ^ 59
def prefixEnd_3856254 : Nat := 4983230072969 + 3 ^ 40 * 3856254 * 2
def baseEnd_3856254 : Nat := 1980111827823260622190417

theorem tailTrace_3856254 : CollatzResearch.WordTrace tailWord_3856254 prefixEnd_3856254 1980111827823260622190417 := by
  unfold tailWord_3856254
  simp only [CollatzResearch.WordTrace]
  refine ⟨17581142271432228574352977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 93766092114305219063215877 17581142271432228574352977)
  ·
    refine ⟨13185856703574171430764733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17581142271432228574352977 13185856703574171430764733)
    ·
      refine ⟨4944696263840314286536775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13185856703574171430764733 4944696263840314286536775)
      ·
        refine ⟨7417044395760471429805163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4944696263840314286536775 7417044395760471429805163)
        ·
          refine ⟨11125566593640707144707745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7417044395760471429805163 11125566593640707144707745)
          ·
            refine ⟨8344174945230530358530809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11125566593640707144707745 8344174945230530358530809)
            ·
              refine ⟨6258131208922897768898107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8344174945230530358530809 6258131208922897768898107)
              ·
                refine ⟨9387196813384346653347161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6258131208922897768898107 9387196813384346653347161)
                ·
                  refine ⟨7040397610038259990010371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9387196813384346653347161 7040397610038259990010371)
                  ·
                    refine ⟨10560596415057389985015557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7040397610038259990010371 10560596415057389985015557)
                    ·
                      refine ⟨1980111827823260622190417, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10560596415057389985015557 1980111827823260622190417)
                      ·
                        rfl

theorem cell23_3856254_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 2, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 2, 2, 1, 2, 1, 4].length) (baseStart_3856254 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3856254 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3856254 prefixEnd_3856254 := by exact prefixLift 3856254
  have htrace : WordTrace (prefixWord ++ tailWord_3856254) baseStart_3856254 baseEnd_3856254 := by
    simpa [prefixWord, tailWord_3856254, baseEnd_3856254] using wordTrace_append hprefix tailTrace_3856254
  have hstable : (prefixWord ++ tailWord_3856254).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3856254).length < 2 ^ (prefixWord ++ tailWord_3856254).sum := by decide
  have hdescent : baseEnd_3856254 < baseStart_3856254 := by decide
  rcases family_descends (prefixWord ++ tailWord_3856254) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3856308 : List Nat := [2, 5, 2, 1, 3, 1, 1, 1, 2, 2, 3]
def baseStart_3856308 : Nat := 118140960795 + 3856308 * 2 ^ 59
def prefixEnd_3856308 : Nat := 4983230072969 + 3 ^ 40 * 3856308 * 2
def baseEnd_3856308 : Nat := 1980139555778603410915169

theorem tailTrace_3856308 : CollatzResearch.WordTrace tailWord_3856308 prefixEnd_3856308 1980139555778603410915169 := by
  unfold tailWord_3856308
  simp only [CollatzResearch.WordTrace]
  refine ⟨70325553856631097908644789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93767405142174797211526385 70325553856631097908644789)
  ·
    refine ⟨6593020674059165428935449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 70325553856631097908644789 6593020674059165428935449)
    ·
      refine ⟨4944765505544374071701587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6593020674059165428935449 4944765505544374071701587)
      ·
        refine ⟨7417148258316561107552381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4944765505544374071701587 7417148258316561107552381)
        ·
          refine ⟨2781430596868710415332143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7417148258316561107552381 2781430596868710415332143)
          ·
            refine ⟨4172145895303065622998215, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2781430596868710415332143 4172145895303065622998215)
            ·
              refine ⟨6258218842954598434497323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4172145895303065622998215 6258218842954598434497323)
              ·
                refine ⟨9387328264431897651745985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6258218842954598434497323 9387328264431897651745985)
                ·
                  refine ⟨7040496198323923238809489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9387328264431897651745985 7040496198323923238809489)
                  ·
                    refine ⟨5280372148742942429107117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7040496198323923238809489 5280372148742942429107117)
                    ·
                      refine ⟨1980139555778603410915169, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5280372148742942429107117 1980139555778603410915169)
                      ·
                        rfl

theorem cell23_3856308_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 3, 1, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 3, 1, 1, 1, 2, 2, 3].length) (baseStart_3856308 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3856308 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3856308 prefixEnd_3856308 := by exact prefixLift 3856308
  have htrace : WordTrace (prefixWord ++ tailWord_3856308) baseStart_3856308 baseEnd_3856308 := by
    simpa [prefixWord, tailWord_3856308, baseEnd_3856308] using wordTrace_append hprefix tailTrace_3856308
  have hstable : (prefixWord ++ tailWord_3856308).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3856308).length < 2 ^ (prefixWord ++ tailWord_3856308).sum := by decide
  have hdescent : baseEnd_3856308 < baseStart_3856308 := by decide
  rcases family_descends (prefixWord ++ tailWord_3856308) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3856320 : List Nat := [2, 1, 1, 2, 3, 2, 2, 2, 4, 4]
def baseStart_3856320 : Nat := 118140960795 + 3856320 * 2 ^ 59
def prefixEnd_3856320 : Nat := 4983230072969 + 3 ^ 40 * 3856320 * 2
def baseEnd_3856320 : Nat := 660048572515485787988371

theorem tailTrace_3856320 : CollatzResearch.WordTrace tailWord_3856320 prefixEnd_3856320 660048572515485787988371 := by
  unfold tailWord_3856320
  simp only [CollatzResearch.WordTrace]
  refine ⟨70325772694609360933363207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93767696926145814577817609 70325772694609360933363207)
  ·
    refine ⟨105488659041914041400044811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70325772694609360933363207 105488659041914041400044811)
    ·
      refine ⟨158232988562871062100067217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105488659041914041400044811 158232988562871062100067217)
      ·
        refine ⟨118674741422153296575050413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 158232988562871062100067217 118674741422153296575050413)
        ·
          refine ⟨44503028033307486215643905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 118674741422153296575050413 44503028033307486215643905)
          ·
            refine ⟨33377271024980614661732929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44503028033307486215643905 33377271024980614661732929)
            ·
              refine ⟨25032953268735460996299697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33377271024980614661732929 25032953268735460996299697)
              ·
                refine ⟨18774714951551595747224773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25032953268735460996299697 18774714951551595747224773)
                ·
                  refine ⟨3520259053415924202604645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 18774714951551595747224773 3520259053415924202604645)
                  ·
                    refine ⟨660048572515485787988371, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3520259053415924202604645 660048572515485787988371)
                    ·
                      rfl

theorem cell23_3856320_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 2, 2, 4, 4].length) (baseStart_3856320 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3856320 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3856320 prefixEnd_3856320 := by exact prefixLift 3856320
  have htrace : WordTrace (prefixWord ++ tailWord_3856320) baseStart_3856320 baseEnd_3856320 := by
    simpa [prefixWord, tailWord_3856320, baseEnd_3856320] using wordTrace_append hprefix tailTrace_3856320
  have hstable : (prefixWord ++ tailWord_3856320).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3856320).length < 2 ^ (prefixWord ++ tailWord_3856320).sum := by decide
  have hdescent : baseEnd_3856320 < baseStart_3856320 := by decide
  rcases family_descends (prefixWord ++ tailWord_3856320) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3856327 : List Nat := [1, 1, 4, 1, 1, 2, 1, 1, 7, 2, 2]
def baseStart_3856327 : Nat := 118140960795 + 3856327 * 2 ^ 59
def prefixEnd_3856327 : Nat := 4983230072969 + 3 ^ 40 * 3856327 * 2
def baseEnd_3856327 : Nat := 1980149311911038836577581

theorem tailTrace_3856327 : CollatzResearch.WordTrace tailWord_3856327 prefixEnd_3856327 1980149311911038836577581 := by
  unfold tailWord_3856327
  simp only [CollatzResearch.WordTrace]
  refine ⟨140651800700193362062231235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93767867133462241374820823 140651800700193362062231235)
  ·
    refine ⟨210977701050290043093346853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140651800700193362062231235 210977701050290043093346853)
    ·
      refine ⟨39558318946929383080002535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 210977701050290043093346853 39558318946929383080002535)
      ·
        refine ⟨59337478420394074620003803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39558318946929383080002535 59337478420394074620003803)
        ·
          refine ⟨89006217630591111930005705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59337478420394074620003803 89006217630591111930005705)
          ·
            refine ⟨66754663222943333947504279, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 89006217630591111930005705 66754663222943333947504279)
            ·
              refine ⟨100131994834415000921256419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 66754663222943333947504279 100131994834415000921256419)
              ·
                refine ⟨150197992251622501381884629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 100131994834415000921256419 150197992251622501381884629)
                ·
                  refine ⟨3520265443397402376137921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 150197992251622501381884629 3520265443397402376137921)
                  ·
                    refine ⟨2640199082548051782103441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3520265443397402376137921 2640199082548051782103441)
                    ·
                      refine ⟨1980149311911038836577581, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2640199082548051782103441 1980149311911038836577581)
                      ·
                        rfl

theorem cell23_3856327_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 1, 1, 7, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 1, 1, 7, 2, 2].length) (baseStart_3856327 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3856327 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3856327 prefixEnd_3856327 := by exact prefixLift 3856327
  have htrace : WordTrace (prefixWord ++ tailWord_3856327) baseStart_3856327 baseEnd_3856327 := by
    simpa [prefixWord, tailWord_3856327, baseEnd_3856327] using wordTrace_append hprefix tailTrace_3856327
  have hstable : (prefixWord ++ tailWord_3856327).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3856327).length < 2 ^ (prefixWord ++ tailWord_3856327).sum := by decide
  have hdescent : baseEnd_3856327 < baseStart_3856327 := by decide
  rcases family_descends (prefixWord ++ tailWord_3856327) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3856340 : List Nat := [2, 4, 1, 2, 1, 1, 2, 2, 1, 1, 6]
def baseStart_3856340 : Nat := 118140960795 + 3856340 * 2 ^ 59
def prefixEnd_3856340 : Nat := 4983230072969 + 3 ^ 40 * 3856340 * 2
def baseEnd_3856340 : Nat := 1980155987159547285715021

theorem tailTrace_3856340 : CollatzResearch.WordTrace tailWord_3856340 prefixEnd_3856340 1980155987159547285715021 := by
  unfold tailWord_3856340
  simp only [CollatzResearch.WordTrace]
  refine ⟨70326137424573132641227237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93768183232764176854969649 70326137424573132641227237)
  ·
    refine ⟨13186150767107462370230107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 70326137424573132641227237 13186150767107462370230107)
    ·
      refine ⟨19779226150661193555345161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13186150767107462370230107 19779226150661193555345161)
      ·
        refine ⟨14834419612995895166508871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19779226150661193555345161 14834419612995895166508871)
        ·
          refine ⟨22251629419493842749763307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14834419612995895166508871 22251629419493842749763307)
          ·
            refine ⟨33377444129240764124644961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22251629419493842749763307 33377444129240764124644961)
            ·
              refine ⟨25033083096930573093483721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33377444129240764124644961 25033083096930573093483721)
              ·
                refine ⟨18774812322697929820112791, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25033083096930573093483721 18774812322697929820112791)
                ·
                  refine ⟨28162218484046894730169187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18774812322697929820112791 28162218484046894730169187)
                  ·
                    refine ⟨42243327726070342095253781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 28162218484046894730169187 42243327726070342095253781)
                    ·
                      refine ⟨1980155987159547285715021, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 42243327726070342095253781 1980155987159547285715021)
                      ·
                        rfl

theorem cell23_3856340_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 2, 2, 1, 1, 6].length) (baseStart_3856340 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3856340 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3856340 prefixEnd_3856340 := by exact prefixLift 3856340
  have htrace : WordTrace (prefixWord ++ tailWord_3856340) baseStart_3856340 baseEnd_3856340 := by
    simpa [prefixWord, tailWord_3856340, baseEnd_3856340] using wordTrace_append hprefix tailTrace_3856340
  have hstable : (prefixWord ++ tailWord_3856340).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3856340).length < 2 ^ (prefixWord ++ tailWord_3856340).sum := by decide
  have hdescent : baseEnd_3856340 < baseStart_3856340 := by decide
  rcases family_descends (prefixWord ++ tailWord_3856340) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3856344 : List Nat := [2, 1, 2, 2, 2, 2, 4, 1, 3, 2, 2]
def baseStart_3856344 : Nat := 118140960795 + 3856344 * 2 ^ 59
def prefixEnd_3856344 : Nat := 4983230072969 + 3 ^ 40 * 3856344 * 2
def baseEnd_3856344 : Nat := 1980158041082165270065003

theorem tailTrace_3856344 : CollatzResearch.WordTrace tailWord_3856344 prefixEnd_3856344 1980158041082165270065003 := by
  unfold tailWord_3856344
  simp only [CollatzResearch.WordTrace]
  refine ⟨70326210370565886982800043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93768280494087849310400057 70326210370565886982800043)
  ·
    refine ⟨105489315555848830474200065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70326210370565886982800043 105489315555848830474200065)
    ·
      refine ⟨79116986666886622855650049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 105489315555848830474200065 79116986666886622855650049)
      ·
        refine ⟨59337740000164967141737537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 79116986666886622855650049 59337740000164967141737537)
        ·
          refine ⟨44503305000123725356303153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59337740000164967141737537 44503305000123725356303153)
          ·
            refine ⟨33377478750092794017227365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44503305000123725356303153 33377478750092794017227365)
            ·
              refine ⟨6258277265642398878230131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 33377478750092794017227365 6258277265642398878230131)
              ·
                refine ⟨9387415898463598317345197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6258277265642398878230131 9387415898463598317345197)
                ·
                  refine ⟨3520280961923849369004449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9387415898463598317345197 3520280961923849369004449)
                  ·
                    refine ⟨2640210721442887026753337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3520280961923849369004449 2640210721442887026753337)
                    ·
                      refine ⟨1980158041082165270065003, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2640210721442887026753337 1980158041082165270065003)
                      ·
                        rfl

theorem cell23_3856344_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 4, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 4, 1, 3, 2, 2].length) (baseStart_3856344 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3856344 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3856344 prefixEnd_3856344 := by exact prefixLift 3856344
  have htrace : WordTrace (prefixWord ++ tailWord_3856344) baseStart_3856344 baseEnd_3856344 := by
    simpa [prefixWord, tailWord_3856344, baseEnd_3856344] using wordTrace_append hprefix tailTrace_3856344
  have hstable : (prefixWord ++ tailWord_3856344).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3856344).length < 2 ^ (prefixWord ++ tailWord_3856344).sum := by decide
  have hdescent : baseEnd_3856344 < baseStart_3856344 := by decide
  rcases family_descends (prefixWord ++ tailWord_3856344) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3856363 : List Nat := [1, 1, 1, 1, 2, 3, 1, 4, 2, 7]
def baseStart_3856363 : Nat := 118140960795 + 3856363 * 2 ^ 59
def prefixEnd_3856363 : Nat := 4983230072969 + 3 ^ 40 * 3856363 * 2
def baseEnd_3856363 : Nat := 660055932404866898575805

theorem tailTrace_3856363 : CollatzResearch.WordTrace tailWord_3856363 prefixEnd_3856363 660055932404866898575805 := by
  unfold tailWord_3856363
  simp only [CollatzResearch.WordTrace]
  refine ⟨140653113728062940210541743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93768742485375293473694495 140653113728062940210541743)
  ·
    refine ⟨210979670592094410315812615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140653113728062940210541743 210979670592094410315812615)
    ·
      refine ⟨316469505888141615473718923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 210979670592094410315812615 316469505888141615473718923)
      ·
        refine ⟨474704258832212423210578385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 316469505888141615473718923 474704258832212423210578385)
        ·
          refine ⟨356028194124159317407933789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 474704258832212423210578385 356028194124159317407933789)
          ·
            refine ⟨133510572796559744027975171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 356028194124159317407933789 133510572796559744027975171)
            ·
              refine ⟨200265859194839616041962757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 133510572796559744027975171 200265859194839616041962757)
              ·
                refine ⟨37549848599032428007868017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 200265859194839616041962757 37549848599032428007868017)
                ·
                  refine ⟨28162386449274321005901013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 37549848599032428007868017 28162386449274321005901013)
                  ·
                    refine ⟨660055932404866898575805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 28162386449274321005901013 660055932404866898575805)
                    ·
                      rfl

theorem cell23_3856363_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 1, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 1, 4, 2, 7].length) (baseStart_3856363 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3856363 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3856363 prefixEnd_3856363 := by exact prefixLift 3856363
  have htrace : WordTrace (prefixWord ++ tailWord_3856363) baseStart_3856363 baseEnd_3856363 := by
    simpa [prefixWord, tailWord_3856363, baseEnd_3856363] using wordTrace_append hprefix tailTrace_3856363
  have hstable : (prefixWord ++ tailWord_3856363).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3856363).length < 2 ^ (prefixWord ++ tailWord_3856363).sum := by decide
  have hdescent : baseEnd_3856363 < baseStart_3856363 := by decide
  rcases family_descends (prefixWord ++ tailWord_3856363) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3856377 : List Nat := [1, 2, 1, 3, 1, 4, 1, 2, 4, 1, 3]
def baseStart_3856377 : Nat := 118140960795 + 3856377 * 2 ^ 59
def prefixEnd_3856377 : Nat := 4983230072969 + 3 ^ 40 * 3856377 * 2
def baseEnd_3856377 : Nat := 1980174985943763640952351

theorem tailTrace_3856377 : CollatzResearch.WordTrace tailWord_3856377 prefixEnd_3856377 1980174985943763640952351 := by
  unfold tailWord_3856377
  simp only [CollatzResearch.WordTrace]
  refine ⟨140653624350012220601551385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93769082900008147067700923 140653624350012220601551385)
  ·
    refine ⟨105490218262509165451163539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 140653624350012220601551385 105490218262509165451163539)
    ·
      refine ⟨158235327393763748176745309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105490218262509165451163539 158235327393763748176745309)
      ·
        refine ⟨59338247772661405566279491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 158235327393763748176745309 59338247772661405566279491)
        ·
          refine ⟨89007371658992108349419237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59338247772661405566279491 89007371658992108349419237)
          ·
            refine ⟨16688882186061020315516107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 89007371658992108349419237 16688882186061020315516107)
            ·
              refine ⟨25033323279091530473274161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16688882186061020315516107 25033323279091530473274161)
              ·
                refine ⟨18774992459318647854955621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25033323279091530473274161 18774992459318647854955621)
                ·
                  refine ⟨3520311086122246472804179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 18774992459318647854955621 3520311086122246472804179)
                  ·
                    refine ⟨5280466629183369709206269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3520311086122246472804179 5280466629183369709206269)
                    ·
                      refine ⟨1980174985943763640952351, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5280466629183369709206269 1980174985943763640952351)
                      ·
                        rfl

theorem cell23_3856377_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 4, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 4, 1, 2, 4, 1, 3].length) (baseStart_3856377 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3856377 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3856377 prefixEnd_3856377 := by exact prefixLift 3856377
  have htrace : WordTrace (prefixWord ++ tailWord_3856377) baseStart_3856377 baseEnd_3856377 := by
    simpa [prefixWord, tailWord_3856377, baseEnd_3856377] using wordTrace_append hprefix tailTrace_3856377
  have hstable : (prefixWord ++ tailWord_3856377).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3856377).length < 2 ^ (prefixWord ++ tailWord_3856377).sum := by decide
  have hdescent : baseEnd_3856377 < baseStart_3856377 := by decide
  rcases family_descends (prefixWord ++ tailWord_3856377) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3856383 : List Nat := [1, 1, 2, 2, 1, 2, 1, 2, 1, 2, 8]
def baseStart_3856383 : Nat := 118140960795 + 3856383 * 2 ^ 59
def prefixEnd_3856383 : Nat := 4983230072969 + 3 ^ 40 * 3856383 * 2
def baseEnd_3856383 : Nat := 1980178066827690617477323

theorem tailTrace_3856383 : CollatzResearch.WordTrace tailWord_3856383 prefixEnd_3856383 1980178066827690617477323 := by
  unfold tailWord_3856383
  simp only [CollatzResearch.WordTrace]
  refine ⟨140653843187990483626269803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93769228791993655750846535 140653843187990483626269803)
  ·
    refine ⟨210980764781985725439404705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140653843187990483626269803 210980764781985725439404705)
    ·
      refine ⟨158235573586489294079553529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 210980764781985725439404705 158235573586489294079553529)
      ·
        refine ⟨118676680189866970559665147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 158235573586489294079553529 118676680189866970559665147)
        ·
          refine ⟨178015020284800455839497721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 118676680189866970559665147 178015020284800455839497721)
          ·
            refine ⟨133511265213600341879623291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 178015020284800455839497721 133511265213600341879623291)
            ·
              refine ⟨200266897820400512819434937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 133511265213600341879623291 200266897820400512819434937)
              ·
                refine ⟨150200173365300384614576203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 200266897820400512819434937 150200173365300384614576203)
                ·
                  refine ⟨225300260047950576921864305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 150200173365300384614576203 225300260047950576921864305)
                  ·
                    refine ⟨168975195035962932691398229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 225300260047950576921864305 168975195035962932691398229)
                    ·
                      refine ⟨1980178066827690617477323, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 168975195035962932691398229 1980178066827690617477323)
                      ·
                        rfl

theorem cell23_3856383_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 2, 1, 2, 8].length) (baseStart_3856383 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3856383 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3856383 prefixEnd_3856383 := by exact prefixLift 3856383
  have htrace : WordTrace (prefixWord ++ tailWord_3856383) baseStart_3856383 baseEnd_3856383 := by
    simpa [prefixWord, tailWord_3856383, baseEnd_3856383] using wordTrace_append hprefix tailTrace_3856383
  have hstable : (prefixWord ++ tailWord_3856383).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3856383).length < 2 ^ (prefixWord ++ tailWord_3856383).sum := by decide
  have hdescent : baseEnd_3856383 < baseStart_3856383 := by decide
  rcases family_descends (prefixWord ++ tailWord_3856383) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3856421 : List Nat := [1, 3, 1, 2, 2, 5, 1, 2, 1, 3, 2]
def baseStart_3856421 : Nat := 118140960795 + 3856421 * 2 ^ 59
def prefixEnd_3856421 : Nat := 4983230072969 + 3 ^ 40 * 3856421 * 2
def baseEnd_3856421 : Nat := 1980197579092561468802149

theorem tailTrace_3856421 : CollatzResearch.WordTrace tailWord_3856421 prefixEnd_3856421 1980197579092561468802149 := by
  unfold tailWord_3856421
  simp only [CollatzResearch.WordTrace]
  refine ⟨140655229161852816116153117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93770152774568544077435411 140655229161852816116153117)
  ·
    refine ⟨52745710935694806043557419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 140655229161852816116153117 52745710935694806043557419)
    ·
      refine ⟨79118566403542209065336129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52745710935694806043557419 79118566403542209065336129)
      ·
        refine ⟨59338924802656656799002097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 79118566403542209065336129 59338924802656656799002097)
        ·
          refine ⟨44504193601992492599251573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59338924802656656799002097 44504193601992492599251573)
          ·
            refine ⟨4172268150186796181179835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 44504193601992492599251573 4172268150186796181179835)
            ·
              refine ⟨6258402225280194271769753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4172268150186796181179835 6258402225280194271769753)
              ·
                refine ⟨4693801668960145703827315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6258402225280194271769753 4693801668960145703827315)
                ·
                  refine ⟨7040702503440218555740973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4693801668960145703827315 7040702503440218555740973)
                  ·
                    refine ⟨2640263438790081958402865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7040702503440218555740973 2640263438790081958402865)
                    ·
                      refine ⟨1980197579092561468802149, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2640263438790081958402865 1980197579092561468802149)
                      ·
                        rfl

theorem cell23_3856421_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 5, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 5, 1, 2, 1, 3, 2].length) (baseStart_3856421 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3856421 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3856421 prefixEnd_3856421 := by exact prefixLift 3856421
  have htrace : WordTrace (prefixWord ++ tailWord_3856421) baseStart_3856421 baseEnd_3856421 := by
    simpa [prefixWord, tailWord_3856421, baseEnd_3856421] using wordTrace_append hprefix tailTrace_3856421
  have hstable : (prefixWord ++ tailWord_3856421).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3856421).length < 2 ^ (prefixWord ++ tailWord_3856421).sum := by decide
  have hdescent : baseEnd_3856421 < baseStart_3856421 := by decide
  rcases family_descends (prefixWord ++ tailWord_3856421) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3856434 : List Nat := [3, 2, 1, 1, 2, 4, 1, 2, 1, 4, 2]
def baseStart_3856434 : Nat := 118140960795 + 3856434 * 2 ^ 59
def prefixEnd_3856434 : Nat := 4983230072969 + 3 ^ 40 * 3856434 * 2
def baseEnd_3856434 : Nat := 1980204254341069917939589

theorem tailTrace_3856434 : CollatzResearch.WordTrace tailWord_3856434 prefixEnd_3856434 1980204254341069917939589 := by
  unfold tailWord_3856434
  simp only [CollatzResearch.WordTrace]
  refine ⟨35163925827701429834094089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 93770468873870479557584237 35163925827701429834094089)
  ·
    refine ⟨26372944370776072375570567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35163925827701429834094089 26372944370776072375570567)
    ·
      refine ⟨39559416556164108563355851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26372944370776072375570567 39559416556164108563355851)
      ·
        refine ⟨59339124834246162845033777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39559416556164108563355851 59339124834246162845033777)
        ·
          refine ⟨44504343625684622133775333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59339124834246162845033777 44504343625684622133775333)
          ·
            refine ⟨8344564429815866650082875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 44504343625684622133775333 8344564429815866650082875)
            ·
              refine ⟨12516846644723799975124313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8344564429815866650082875 12516846644723799975124313)
              ·
                refine ⟨9387634983542849981343235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12516846644723799975124313 9387634983542849981343235)
                ·
                  refine ⟨14081452475314274972014853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9387634983542849981343235 14081452475314274972014853)
                  ·
                    refine ⟨2640272339121426557252785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 14081452475314274972014853 2640272339121426557252785)
                    ·
                      refine ⟨1980204254341069917939589, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2640272339121426557252785 1980204254341069917939589)
                      ·
                        rfl

theorem cell23_3856434_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 4, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 4, 1, 2, 1, 4, 2].length) (baseStart_3856434 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3856434 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3856434 prefixEnd_3856434 := by exact prefixLift 3856434
  have htrace : WordTrace (prefixWord ++ tailWord_3856434) baseStart_3856434 baseEnd_3856434 := by
    simpa [prefixWord, tailWord_3856434, baseEnd_3856434] using wordTrace_append hprefix tailTrace_3856434
  have hstable : (prefixWord ++ tailWord_3856434).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3856434).length < 2 ^ (prefixWord ++ tailWord_3856434).sum := by decide
  have hdescent : baseEnd_3856434 < baseStart_3856434 := by decide
  rcases family_descends (prefixWord ++ tailWord_3856434) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3856438 : List Nat := [5, 1, 2, 1, 1, 1, 5, 1, 1, 3, 2]
def baseStart_3856438 : Nat := 118140960795 + 3856438 * 2 ^ 59
def prefixEnd_3856438 : Nat := 4983230072969 + 3 ^ 40 * 3856438 * 2
def baseEnd_3856438 : Nat := 1980206308263687902289571

theorem tailTrace_3856438 : CollatzResearch.WordTrace tailWord_3856438 prefixEnd_3856438 1980206308263687902289571 := by
  unfold tailWord_3856438
  simp only [CollatzResearch.WordTrace]
  refine ⟨8790990575174451751220123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 93770566135194152013014645 8790990575174451751220123)
  ·
    refine ⟨13186485862761677626830185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8790990575174451751220123 13186485862761677626830185)
    ·
      refine ⟨9889864397071258220122639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13186485862761677626830185 9889864397071258220122639)
      ·
        refine ⟨14834796595606887330183959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9889864397071258220122639 14834796595606887330183959)
        ·
          refine ⟨22252194893410330995275939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14834796595606887330183959 22252194893410330995275939)
          ·
            refine ⟨33378292340115496492913909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22252194893410330995275939 33378292340115496492913909)
            ·
              refine ⟨3129214906885827796210679, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 33378292340115496492913909 3129214906885827796210679)
              ·
                refine ⟨4693822360328741694316019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3129214906885827796210679 4693822360328741694316019)
                ·
                  refine ⟨7040733540493112541474029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4693822360328741694316019 7040733540493112541474029)
                  ·
                    refine ⟨2640275077684917203052761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7040733540493112541474029 2640275077684917203052761)
                    ·
                      refine ⟨1980206308263687902289571, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2640275077684917203052761 1980206308263687902289571)
                      ·
                        rfl

theorem cell23_3856438_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 5, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 5, 1, 1, 3, 2].length) (baseStart_3856438 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3856438 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3856438 prefixEnd_3856438 := by exact prefixLift 3856438
  have htrace : WordTrace (prefixWord ++ tailWord_3856438) baseStart_3856438 baseEnd_3856438 := by
    simpa [prefixWord, tailWord_3856438, baseEnd_3856438] using wordTrace_append hprefix tailTrace_3856438
  have hstable : (prefixWord ++ tailWord_3856438).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3856438).length < 2 ^ (prefixWord ++ tailWord_3856438).sum := by decide
  have hdescent : baseEnd_3856438 < baseStart_3856438 := by decide
  rcases family_descends (prefixWord ++ tailWord_3856438) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3856454 : List Nat := [6, 1, 1, 1, 1, 1, 1, 1, 1, 6, 3]
def baseStart_3856454 : Nat := 118140960795 + 3856454 * 2 ^ 59
def prefixEnd_3856454 : Nat := 4983230072969 + 3 ^ 40 * 3856454 * 2
def baseEnd_3856454 : Nat := 1980214523954159839689497

theorem tailTrace_3856454 : CollatzResearch.WordTrace tailWord_3856454 prefixEnd_3856454 1980214523954159839689497 := by
  unfold tailWord_3856454
  simp only [CollatzResearch.WordTrace]
  refine ⟨4395513524085414461003263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 93770955180488841834736277 4395513524085414461003263)
  ·
    refine ⟨6593270286128121691504895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4395513524085414461003263 6593270286128121691504895)
    ·
      refine ⟨9889905429192182537257343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6593270286128121691504895 9889905429192182537257343)
      ·
        refine ⟨14834858143788273805886015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9889905429192182537257343 14834858143788273805886015)
        ·
          refine ⟨22252287215682410708829023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14834858143788273805886015 22252287215682410708829023)
          ·
            refine ⟨33378430823523616063243535, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22252287215682410708829023 33378430823523616063243535)
            ·
              refine ⟨50067646235285424094865303, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33378430823523616063243535 50067646235285424094865303)
              ·
                refine ⟨75101469352928136142297955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50067646235285424094865303 75101469352928136142297955)
                ·
                  refine ⟨112652204029392204213446933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 75101469352928136142297955 112652204029392204213446933)
                  ·
                    refine ⟨5280572063877759572505325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 112652204029392204213446933 5280572063877759572505325)
                    ·
                      refine ⟨1980214523954159839689497, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5280572063877759572505325 1980214523954159839689497)
                      ·
                        rfl

theorem cell23_3856454_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 1, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 1, 1, 1, 6, 3].length) (baseStart_3856454 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3856454 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3856454 prefixEnd_3856454 := by exact prefixLift 3856454
  have htrace : WordTrace (prefixWord ++ tailWord_3856454) baseStart_3856454 baseEnd_3856454 := by
    simpa [prefixWord, tailWord_3856454, baseEnd_3856454] using wordTrace_append hprefix tailTrace_3856454
  have hstable : (prefixWord ++ tailWord_3856454).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3856454).length < 2 ^ (prefixWord ++ tailWord_3856454).sum := by decide
  have hdescent : baseEnd_3856454 < baseStart_3856454 := by decide
  rcases family_descends (prefixWord ++ tailWord_3856454) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3856457 : List Nat := [1, 2, 1, 1, 2, 2, 5, 4, 5]
def baseStart_3856457 : Nat := 118140960795 + 3856457 * 2 ^ 59
def prefixEnd_3856457 : Nat := 4983230072969 + 3 ^ 40 * 3856457 * 2
def baseEnd_3856457 : Nat := 220024007155124814216887

theorem tailTrace_3856457 : CollatzResearch.WordTrace tailWord_3856457 prefixEnd_3856457 220024007155124814216887 := by
  unfold tailWord_3856457
  simp only [CollatzResearch.WordTrace]
  refine ⟨140656542189722394264463625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93771028126481596176309083 140656542189722394264463625)
  ·
    refine ⟨105492406642291795698347719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 140656542189722394264463625 105492406642291795698347719)
    ·
      refine ⟨158238609963437693547521579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105492406642291795698347719 158238609963437693547521579)
      ·
        refine ⟨237357914945156540321282369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 158238609963437693547521579 237357914945156540321282369)
        ·
          refine ⟨178018436208867405240961777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 237357914945156540321282369 178018436208867405240961777)
          ·
            refine ⟨133513827156650553930721333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 178018436208867405240961777 133513827156650553930721333)
            ·
              refine ⟨12516921295935989431005125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 133513827156650553930721333 12516921295935989431005125)
              ·
                refine ⟨2346922742987998018313461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12516921295935989431005125 2346922742987998018313461)
                ·
                  refine ⟨220024007155124814216887, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2346922742987998018313461 220024007155124814216887)
                  ·
                    rfl

theorem cell23_3856457_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 5, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 5, 4, 5].length) (baseStart_3856457 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3856457 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3856457 prefixEnd_3856457 := by exact prefixLift 3856457
  have htrace : WordTrace (prefixWord ++ tailWord_3856457) baseStart_3856457 baseEnd_3856457 := by
    simpa [prefixWord, tailWord_3856457, baseEnd_3856457] using wordTrace_append hprefix tailTrace_3856457
  have hstable : (prefixWord ++ tailWord_3856457).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3856457).length < 2 ^ (prefixWord ++ tailWord_3856457).sum := by decide
  have hdescent : baseEnd_3856457 < baseStart_3856457 := by decide
  rcases family_descends (prefixWord ++ tailWord_3856457) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3856558 : List Nat := [4, 1, 4, 2, 1, 1, 1, 2, 2, 1, 4]
def baseStart_3856558 : Nat := 118140960795 + 3856558 * 2 ^ 59
def prefixEnd_3856558 : Nat := 4983230072969 + 3 ^ 40 * 3856558 * 2
def baseEnd_3856558 : Nat := 1980267925942227432789019

theorem tailTrace_3856558 : CollatzResearch.WordTrace tailWord_3856558 prefixEnd_3856558 1980267925942227432789019 := by
  unfold tailWord_3856558
  simp only [CollatzResearch.WordTrace]
  refine ⟨17582528245294561064236291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 93773483974904325675926885 17582528245294561064236291)
  ·
    refine ⟨26373792367941841596354437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17582528245294561064236291 26373792367941841596354437)
    ·
      refine ⟨4945086068989095299316457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 26373792367941841596354437 4945086068989095299316457)
      ·
        refine ⟨3708814551741821474487343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4945086068989095299316457 3708814551741821474487343)
        ·
          refine ⟨5563221827612732211731015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3708814551741821474487343 5563221827612732211731015)
          ·
            refine ⟨8344832741419098317596523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5563221827612732211731015 8344832741419098317596523)
            ·
              refine ⟨12517249112128647476394785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8344832741419098317596523 12517249112128647476394785)
              ·
                refine ⟨9387936834096485607296089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12517249112128647476394785 9387936834096485607296089)
                ·
                  refine ⟨7040952625572364205472067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9387936834096485607296089 7040952625572364205472067)
                  ·
                    refine ⟨10561428938358546308208101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7040952625572364205472067 10561428938358546308208101)
                    ·
                      refine ⟨1980267925942227432789019, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10561428938358546308208101 1980267925942227432789019)
                      ·
                        rfl

theorem cell23_3856558_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 2, 1, 1, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 2, 1, 1, 1, 2, 2, 1, 4].length) (baseStart_3856558 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3856558 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3856558 prefixEnd_3856558 := by exact prefixLift 3856558
  have htrace : WordTrace (prefixWord ++ tailWord_3856558) baseStart_3856558 baseEnd_3856558 := by
    simpa [prefixWord, tailWord_3856558, baseEnd_3856558] using wordTrace_append hprefix tailTrace_3856558
  have hstable : (prefixWord ++ tailWord_3856558).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3856558).length < 2 ^ (prefixWord ++ tailWord_3856558).sum := by decide
  have hdescent : baseEnd_3856558 < baseStart_3856558 := by decide
  rcases family_descends (prefixWord ++ tailWord_3856558) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3856561 : List Nat := [1, 2, 2, 5, 2, 1, 1, 2, 2, 2, 3]
def baseStart_3856561 : Nat := 118140960795 + 3856561 * 2 ^ 59
def prefixEnd_3856561 : Nat := 4983230072969 + 3 ^ 40 * 3856561 * 2
def baseEnd_3856561 : Nat := 1980269466384190921051505

theorem tailTrace_3856561 : CollatzResearch.WordTrace tailWord_3856561 prefixEnd_3856561 1980269466384190921051505 := by
  unfold tailWord_3856561
  simp only [CollatzResearch.WordTrace]
  refine ⟨140660335381345620026249537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93773556920897080017499691 140660335381345620026249537)
  ·
    refine ⟨105495251536009215019687153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 140660335381345620026249537 105495251536009215019687153)
    ·
      refine ⟨79121438652006911264765365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 105495251536009215019687153 79121438652006911264765365)
      ·
        refine ⟨7417634873625647931071753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 79121438652006911264765365 7417634873625647931071753)
        ·
          refine ⟨5563226155219235948303815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7417634873625647931071753 5563226155219235948303815)
          ·
            refine ⟨8344839232828853922455723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5563226155219235948303815 8344839232828853922455723)
            ·
              refine ⟨12517258849243280883683585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8344839232828853922455723 12517258849243280883683585)
              ·
                refine ⟨9387944136932460662762689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12517258849243280883683585 9387944136932460662762689)
                ·
                  refine ⟨7040958102699345497072017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9387944136932460662762689 7040958102699345497072017)
                  ·
                    refine ⟨5280718577024509122804013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7040958102699345497072017 5280718577024509122804013)
                    ·
                      refine ⟨1980269466384190921051505, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5280718577024509122804013 1980269466384190921051505)
                      ·
                        rfl

theorem cell23_3856561_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 2, 1, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 2, 1, 1, 2, 2, 2, 3].length) (baseStart_3856561 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3856561 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3856561 prefixEnd_3856561 := by exact prefixLift 3856561
  have htrace : WordTrace (prefixWord ++ tailWord_3856561) baseStart_3856561 baseEnd_3856561 := by
    simpa [prefixWord, tailWord_3856561, baseEnd_3856561] using wordTrace_append hprefix tailTrace_3856561
  have hstable : (prefixWord ++ tailWord_3856561).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3856561).length < 2 ^ (prefixWord ++ tailWord_3856561).sum := by decide
  have hdescent : baseEnd_3856561 < baseStart_3856561 := by decide
  rcases family_descends (prefixWord ++ tailWord_3856561) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3856584 : List Nat := [2, 1, 3, 1, 2, 1, 1, 1, 6, 3, 2]
def baseStart_3856584 : Nat := 118140960795 + 3856584 * 2 ^ 59
def prefixEnd_3856584 : Nat := 4983230072969 + 3 ^ 40 * 3856584 * 2
def baseEnd_3856584 : Nat := 1980281276439244331063899

theorem tailTrace_3856584 : CollatzResearch.WordTrace tailWord_3856584 prefixEnd_3856584 1980281276439244331063899 := by
  unfold tailWord_3856584
  simp only [CollatzResearch.WordTrace]
  refine ⟨70330587130131147477168403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93774116173508196636224537 70330587130131147477168403)
  ·
    refine ⟨105495880695196721215752605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70330587130131147477168403 105495880695196721215752605)
    ·
      refine ⟨39560955260698770455907227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 105495880695196721215752605 39560955260698770455907227)
      ·
        refine ⟨59341432891048155683860841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39560955260698770455907227 59341432891048155683860841)
        ·
          refine ⟨44506074668286116762895631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59341432891048155683860841 44506074668286116762895631)
          ·
            refine ⟨66759112002429175144343447, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44506074668286116762895631 66759112002429175144343447)
            ·
              refine ⟨100138668003643762716515171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 66759112002429175144343447 100138668003643762716515171)
              ·
                refine ⟨150208002005465644074772757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 100138668003643762716515171 150208002005465644074772757)
                ·
                  refine ⟨7041000094006202066004973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 150208002005465644074772757 7041000094006202066004973)
                  ·
                    refine ⟨2640375035252325774751865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7041000094006202066004973 2640375035252325774751865)
                    ·
                      refine ⟨1980281276439244331063899, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2640375035252325774751865 1980281276439244331063899)
                      ·
                        rfl

theorem cell23_3856584_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 1, 1, 6, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 1, 1, 6, 3, 2].length) (baseStart_3856584 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3856584 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3856584 prefixEnd_3856584 := by exact prefixLift 3856584
  have htrace : WordTrace (prefixWord ++ tailWord_3856584) baseStart_3856584 baseEnd_3856584 := by
    simpa [prefixWord, tailWord_3856584, baseEnd_3856584] using wordTrace_append hprefix tailTrace_3856584
  have hstable : (prefixWord ++ tailWord_3856584).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3856584).length < 2 ^ (prefixWord ++ tailWord_3856584).sum := by decide
  have hdescent : baseEnd_3856584 < baseStart_3856584 := by decide
  rcases family_descends (prefixWord ++ tailWord_3856584) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3856594 : List Nat := [3, 2, 2, 2, 1, 3, 1, 1, 3, 5]
def baseStart_3856594 : Nat := 118140960795 + 3856594 * 2 ^ 59
def prefixEnd_3856594 : Nat := 4983230072969 + 3 ^ 40 * 3856594 * 2
def baseEnd_3856594 : Nat := 660095470415263097312951

theorem tailTrace_3856594 : CollatzResearch.WordTrace tailWord_3856594 prefixEnd_3856594 660095470415263097312951 := by
  unfold tailWord_3856594
  simp only [CollatzResearch.WordTrace]
  refine ⟨35165384747556516665550209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 93774359326817377774800557 35165384747556516665550209)
  ·
    refine ⟨26374038560667387499162657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35165384747556516665550209 26374038560667387499162657)
    ·
      refine ⟨19780528920500540624371993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26374038560667387499162657 19780528920500540624371993)
      ·
        refine ⟨14835396690375405468278995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19780528920500540624371993 14835396690375405468278995)
        ·
          refine ⟨22253095035563108202418493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14835396690375405468278995 22253095035563108202418493)
          ·
            refine ⟨8344910638336165575906935, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22253095035563108202418493 8344910638336165575906935)
            ·
              refine ⟨12517365957504248363860403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8344910638336165575906935 12517365957504248363860403)
              ·
                refine ⟨18776048936256372545790605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12517365957504248363860403 18776048936256372545790605)
                ·
                  refine ⟨7041018351096139704671477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18776048936256372545790605 7041018351096139704671477)
                  ·
                    refine ⟨660095470415263097312951, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7041018351096139704671477 660095470415263097312951)
                    ·
                      rfl

theorem cell23_3856594_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 3, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 3, 1, 1, 3, 5].length) (baseStart_3856594 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3856594 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3856594 prefixEnd_3856594 := by exact prefixLift 3856594
  have htrace : WordTrace (prefixWord ++ tailWord_3856594) baseStart_3856594 baseEnd_3856594 := by
    simpa [prefixWord, tailWord_3856594, baseEnd_3856594] using wordTrace_append hprefix tailTrace_3856594
  have hstable : (prefixWord ++ tailWord_3856594).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3856594).length < 2 ^ (prefixWord ++ tailWord_3856594).sum := by decide
  have hdescent : baseEnd_3856594 < baseStart_3856594 := by decide
  rcases family_descends (prefixWord ++ tailWord_3856594) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3856627 : List Nat := [1, 1, 1, 2, 2, 4, 1, 2, 3, 2, 4]
def baseStart_3856627 : Nat := 118140960795 + 3856627 * 2 ^ 59
def prefixEnd_3856627 : Nat := 4983230072969 + 3 ^ 40 * 3856627 * 2
def baseEnd_3856627 : Nat := 1980303356107387662826201

theorem tailTrace_3856627 : CollatzResearch.WordTrace tailWord_3856627 prefixEnd_3856627 1980303356107387662826201 := by
  unfold tailWord_3856627
  simp only [CollatzResearch.WordTrace]
  refine ⟨140662742599106513298152135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93775161732737675532101423 140662742599106513298152135)
  ·
    refine ⟨210994113898659769947228203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140662742599106513298152135 210994113898659769947228203)
    ·
      refine ⟨316491170847989654920842305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 210994113898659769947228203 316491170847989654920842305)
      ·
        refine ⟨237368378135992241190631729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 316491170847989654920842305 237368378135992241190631729)
        ·
          refine ⟨178026283601994180892973797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 237368378135992241190631729 178026283601994180892973797)
          ·
            refine ⟨33379928175373908917432587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 178026283601994180892973797 33379928175373908917432587)
            ·
              refine ⟨50069892263060863376148881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33379928175373908917432587 50069892263060863376148881)
              ·
                refine ⟨37552419197295647532111661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 50069892263060863376148881 37552419197295647532111661)
                ·
                  refine ⟨14082157198985867824541873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 37552419197295647532111661 14082157198985867824541873)
                  ·
                    refine ⟨10561617899239400868406405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14082157198985867824541873 10561617899239400868406405)
                    ·
                      refine ⟨1980303356107387662826201, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10561617899239400868406405 1980303356107387662826201)
                      ·
                        rfl

theorem cell23_3856627_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 1, 2, 3, 2, 4].length) (baseStart_3856627 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3856627 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3856627 prefixEnd_3856627 := by exact prefixLift 3856627
  have htrace : WordTrace (prefixWord ++ tailWord_3856627) baseStart_3856627 baseEnd_3856627 := by
    simpa [prefixWord, tailWord_3856627, baseEnd_3856627] using wordTrace_append hprefix tailTrace_3856627
  have hstable : (prefixWord ++ tailWord_3856627).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3856627).length < 2 ^ (prefixWord ++ tailWord_3856627).sum := by decide
  have hdescent : baseEnd_3856627 < baseStart_3856627 := by decide
  rcases family_descends (prefixWord ++ tailWord_3856627) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3856634 : List Nat := [3, 1, 1, 1, 1, 5, 1, 2, 3, 2, 3]
def baseStart_3856634 : Nat := 118140960795 + 3856634 * 2 ^ 59
def prefixEnd_3856634 : Nat := 4983230072969 + 3 ^ 40 * 3856634 * 2
def baseEnd_3856634 : Nat := 1980306950471969135438669

theorem tailTrace_3856634 : CollatzResearch.WordTrace tailWord_3856634 prefixEnd_3856634 1980306950471969135438669 := by
  unfold tailWord_3856634
  simp only [CollatzResearch.WordTrace]
  refine ⟨35165749477520288373414239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 93775331940054102329104637 35165749477520288373414239)
  ·
    refine ⟨52748624216280432560121359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35165749477520288373414239 52748624216280432560121359)
    ·
      refine ⟨79122936324420648840182039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52748624216280432560121359 79122936324420648840182039)
      ·
        refine ⟨118684404486630973260273059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79122936324420648840182039 118684404486630973260273059)
        ·
          refine ⟨178026606729946459890409589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 118684404486630973260273059 178026606729946459890409589)
          ·
            refine ⟨16689994380932480614725899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 178026606729946459890409589 16689994380932480614725899)
            ·
              refine ⟨25034991571398720922088849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16689994380932480614725899 25034991571398720922088849)
              ·
                refine ⟨18776243678549040691566637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25034991571398720922088849 18776243678549040691566637)
                ·
                  refine ⟨7041091379455890259337489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18776243678549040691566637 7041091379455890259337489)
                  ·
                    refine ⟨5280818534591917694503117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7041091379455890259337489 5280818534591917694503117)
                    ·
                      refine ⟨1980306950471969135438669, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5280818534591917694503117 1980306950471969135438669)
                      ·
                        rfl

theorem cell23_3856634_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 5, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 5, 1, 2, 3, 2, 3].length) (baseStart_3856634 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3856634 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3856634 prefixEnd_3856634 := by exact prefixLift 3856634
  have htrace : WordTrace (prefixWord ++ tailWord_3856634) baseStart_3856634 baseEnd_3856634 := by
    simpa [prefixWord, tailWord_3856634, baseEnd_3856634] using wordTrace_append hprefix tailTrace_3856634
  have hstable : (prefixWord ++ tailWord_3856634).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3856634).length < 2 ^ (prefixWord ++ tailWord_3856634).sum := by decide
  have hdescent : baseEnd_3856634 < baseStart_3856634 := by decide
  rcases family_descends (prefixWord ++ tailWord_3856634) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3856648 : List Nat := [2, 1, 3, 2, 3, 2, 1, 2, 3, 2, 2]
def baseStart_3856648 : Nat := 118140960795 + 3856648 * 2 ^ 59
def prefixEnd_3856648 : Nat := 4983230072969 + 3 ^ 40 * 3856648 * 2
def baseEnd_3856648 : Nat := 1980314139201132080663605

theorem tailTrace_3856648 : CollatzResearch.WordTrace tailWord_3856648 prefixEnd_3856648 1980314139201132080663605 := by
  unfold tailWord_3856648
  simp only [CollatzResearch.WordTrace]
  refine ⟨70331754266015216942333299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93775672354686955923111065 70331754266015216942333299)
  ·
    refine ⟨105497631399022825413499949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70331754266015216942333299 105497631399022825413499949)
    ·
      refine ⟨39561611774633559530062481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 105497631399022825413499949 39561611774633559530062481)
      ·
        refine ⟨29671208830975169647546861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39561611774633559530062481 29671208830975169647546861)
        ·
          refine ⟨11126703311615688617830073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29671208830975169647546861 11126703311615688617830073)
          ·
            refine ⟨8345027483711766463372555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11126703311615688617830073 8345027483711766463372555)
            ·
              refine ⟨12517541225567649695058833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8345027483711766463372555 12517541225567649695058833)
              ·
                refine ⟨9388155919175737271294125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12517541225567649695058833 9388155919175737271294125)
                ·
                  refine ⟨3520558469690901476735297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9388155919175737271294125 3520558469690901476735297)
                  ·
                    refine ⟨2640418852268176107551473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3520558469690901476735297 2640418852268176107551473)
                    ·
                      refine ⟨1980314139201132080663605, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2640418852268176107551473 1980314139201132080663605)
                      ·
                        rfl

theorem cell23_3856648_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 2, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 2, 1, 2, 3, 2, 2].length) (baseStart_3856648 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3856648 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3856648 prefixEnd_3856648 := by exact prefixLift 3856648
  have htrace : WordTrace (prefixWord ++ tailWord_3856648) baseStart_3856648 baseEnd_3856648 := by
    simpa [prefixWord, tailWord_3856648, baseEnd_3856648] using wordTrace_append hprefix tailTrace_3856648
  have hstable : (prefixWord ++ tailWord_3856648).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3856648).length < 2 ^ (prefixWord ++ tailWord_3856648).sum := by decide
  have hdescent : baseEnd_3856648 < baseStart_3856648 := by decide
  rcases family_descends (prefixWord ++ tailWord_3856648) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3856654 : List Nat := [4, 1, 1, 2, 1, 2, 5, 7]
def baseStart_3856654 : Nat := 118140960795 + 3856654 * 2 ^ 59
def prefixEnd_3856654 : Nat := 4983230072969 + 3 ^ 40 * 3856654 * 2
def baseEnd_3856654 : Nat := 73345082225372557673651

theorem tailTrace_3856654 : CollatzResearch.WordTrace tailWord_3856654 prefixEnd_3856654 73345082225372557673651 := by
  unfold tailWord_3856654
  simp only [CollatzResearch.WordTrace]
  refine ⟨17582965921251087113673127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 93775818246672464606256677 17582965921251087113673127)
  ·
    refine ⟨26374448881876630670509691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17582965921251087113673127 26374448881876630670509691)
    ·
      refine ⟨39561673322814946005764537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26374448881876630670509691 39561673322814946005764537)
      ·
        refine ⟨29671254992111209504323403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39561673322814946005764537 29671254992111209504323403)
        ·
          refine ⟨44506882488166814256485105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29671254992111209504323403 44506882488166814256485105)
          ·
            refine ⟨33380161866125110692363829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44506882488166814256485105 33380161866125110692363829)
            ·
              refine ⟨3129390174949229127409109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 33380161866125110692363829 3129390174949229127409109)
              ·
                refine ⟨73345082225372557673651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3129390174949229127409109 73345082225372557673651)
                ·
                  rfl

theorem cell23_3856654_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 5, 7].length) (baseStart_3856654 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3856654 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3856654 prefixEnd_3856654 := by exact prefixLift 3856654
  have htrace : WordTrace (prefixWord ++ tailWord_3856654) baseStart_3856654 baseEnd_3856654 := by
    simpa [prefixWord, tailWord_3856654, baseEnd_3856654] using wordTrace_append hprefix tailTrace_3856654
  have hstable : (prefixWord ++ tailWord_3856654).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3856654).length < 2 ^ (prefixWord ++ tailWord_3856654).sum := by decide
  have hdescent : baseEnd_3856654 < baseStart_3856654 := by decide
  rcases family_descends (prefixWord ++ tailWord_3856654) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3856664 : List Nat := [2, 1, 2, 3, 1, 2, 1, 4, 1, 3, 3]
def baseStart_3856664 : Nat := 118140960795 + 3856664 * 2 ^ 59
def prefixEnd_3856664 : Nat := 4983230072969 + 3 ^ 40 * 3856664 * 2
def baseEnd_3856664 : Nat := 1980322354891604018063531

theorem tailTrace_3856664 : CollatzResearch.WordTrace tailWord_3856664 prefixEnd_3856664 1980322354891604018063531 := by
  unfold tailWord_3856664
  simp only [CollatzResearch.WordTrace]
  refine ⟨70332046049986234308624523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93776061399981645744832697 70332046049986234308624523)
  ·
    refine ⟨105498069074979351462936785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70332046049986234308624523 105498069074979351462936785)
    ·
      refine ⟨79123551806234513597202589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 105498069074979351462936785 79123551806234513597202589)
      ·
        refine ⟨29671331927337942598950971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 79123551806234513597202589 29671331927337942598950971)
        ·
          refine ⟨44506997891006913898426457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29671331927337942598950971 44506997891006913898426457)
          ·
            refine ⟨33380248418255185423819843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44506997891006913898426457 33380248418255185423819843)
            ·
              refine ⟨50070372627382778135729765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33380248418255185423819843 50070372627382778135729765)
              ·
                refine ⟨9388194867634270900449331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 50070372627382778135729765 9388194867634270900449331)
                ·
                  refine ⟨14082292301451406350673997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9388194867634270900449331 14082292301451406350673997)
                  ·
                    refine ⟨5280859613044277381502749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14082292301451406350673997 5280859613044277381502749)
                    ·
                      refine ⟨1980322354891604018063531, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5280859613044277381502749 1980322354891604018063531)
                      ·
                        rfl

theorem cell23_3856664_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 1, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 1, 4, 1, 3, 3].length) (baseStart_3856664 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3856664 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3856664 prefixEnd_3856664 := by exact prefixLift 3856664
  have htrace : WordTrace (prefixWord ++ tailWord_3856664) baseStart_3856664 baseEnd_3856664 := by
    simpa [prefixWord, tailWord_3856664, baseEnd_3856664] using wordTrace_append hprefix tailTrace_3856664
  have hstable : (prefixWord ++ tailWord_3856664).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3856664).length < 2 ^ (prefixWord ++ tailWord_3856664).sum := by decide
  have hdescent : baseEnd_3856664 < baseStart_3856664 := by decide
  rcases family_descends (prefixWord ++ tailWord_3856664) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3856687 : List Nat := [1, 1, 2, 1, 2, 1, 4, 1, 1, 5, 4]
def baseStart_3856687 : Nat := 118140960795 + 3856687 * 2 ^ 59
def prefixEnd_3856687 : Nat := 4983230072969 + 3 ^ 40 * 3856687 * 2
def baseEnd_3856687 : Nat := 1980334164946657428075925

theorem tailTrace_3856687 : CollatzResearch.WordTrace tailWord_3856687 prefixEnd_3856687 1980334164946657428075925 := by
  unfold tailWord_3856687
  simp only [CollatzResearch.WordTrace]
  refine ⟨140664930978889143545336315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93776620652592762363557543 140664930978889143545336315)
  ·
    refine ⟨210997396468333715318004473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140664930978889143545336315 210997396468333715318004473)
    ·
      refine ⟨158248047351250286488503355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 210997396468333715318004473 158248047351250286488503355)
      ·
        refine ⟨237372071026875429732755033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 158248047351250286488503355 237372071026875429732755033)
        ·
          refine ⟨178029053270156572299566275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 237372071026875429732755033 178029053270156572299566275)
          ·
            refine ⟨267043579905234858449349413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 178029053270156572299566275 267043579905234858449349413)
            ·
              refine ⟨50070671232231535959253015, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 267043579905234858449349413 50070671232231535959253015)
              ·
                refine ⟨75106006848347303938879523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50070671232231535959253015 75106006848347303938879523)
                ·
                  refine ⟨112659010272520955908319285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 75106006848347303938879523 112659010272520955908319285)
                  ·
                    refine ⟨10561782213048839616404933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 112659010272520955908319285 10561782213048839616404933)
                    ·
                      refine ⟨1980334164946657428075925, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10561782213048839616404933 1980334164946657428075925)
                      ·
                        rfl

theorem cell23_3856687_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 4, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 4, 1, 1, 5, 4].length) (baseStart_3856687 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3856687 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3856687 prefixEnd_3856687 := by exact prefixLift 3856687
  have htrace : WordTrace (prefixWord ++ tailWord_3856687) baseStart_3856687 baseEnd_3856687 := by
    simpa [prefixWord, tailWord_3856687, baseEnd_3856687] using wordTrace_append hprefix tailTrace_3856687
  have hstable : (prefixWord ++ tailWord_3856687).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3856687).length < 2 ^ (prefixWord ++ tailWord_3856687).sum := by decide
  have hdescent : baseEnd_3856687 < baseStart_3856687 := by decide
  rcases family_descends (prefixWord ++ tailWord_3856687) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3856724 : List Nat := [2, 4, 1, 1, 2, 2, 1, 1, 1, 3, 5]
def baseStart_3856724 : Nat := 118140960795 + 3856724 * 2 ^ 59
def prefixEnd_3856724 : Nat := 4983230072969 + 3 ^ 40 * 3856724 * 2
def baseEnd_3856724 : Nat := 1980353163730873783313255

theorem tailTrace_3856724 : CollatzResearch.WordTrace tailWord_3856724 prefixEnd_3856724 1980353163730873783313255 := by
  unfold tailWord_3856724
  simp only [CollatzResearch.WordTrace]
  refine ⟨70333140239877549432216613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93777520319836732576288817 70333140239877549432216613)
  ·
    refine ⟨13187463794977040518540615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 70333140239877549432216613 13187463794977040518540615)
    ·
      refine ⟨19781195692465560777810923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13187463794977040518540615 19781195692465560777810923)
      ·
        refine ⟨29671793538698341166716385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19781195692465560777810923 29671793538698341166716385)
        ·
          refine ⟨22253845154023755875037289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29671793538698341166716385 22253845154023755875037289)
          ·
            refine ⟨16690383865517816906277967, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22253845154023755875037289 16690383865517816906277967)
            ·
              refine ⟨25035575798276725359416951, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16690383865517816906277967 25035575798276725359416951)
              ·
                refine ⟨37553363697415088039125427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25035575798276725359416951 37553363697415088039125427)
                ·
                  refine ⟨56330045546122632058688141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37553363697415088039125427 56330045546122632058688141)
                  ·
                    refine ⟨21123767079795987022008053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 56330045546122632058688141 21123767079795987022008053)
                    ·
                      refine ⟨1980353163730873783313255, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 21123767079795987022008053 1980353163730873783313255)
                      ·
                        rfl

theorem cell23_3856724_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 2, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 2, 1, 1, 1, 3, 5].length) (baseStart_3856724 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3856724 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3856724 prefixEnd_3856724 := by exact prefixLift 3856724
  have htrace : WordTrace (prefixWord ++ tailWord_3856724) baseStart_3856724 baseEnd_3856724 := by
    simpa [prefixWord, tailWord_3856724, baseEnd_3856724] using wordTrace_append hprefix tailTrace_3856724
  have hstable : (prefixWord ++ tailWord_3856724).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3856724).length < 2 ^ (prefixWord ++ tailWord_3856724).sum := by decide
  have hdescent : baseEnd_3856724 < baseStart_3856724 := by decide
  rcases family_descends (prefixWord ++ tailWord_3856724) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3856828 : List Nat := [2, 2, 2, 4, 1, 1, 3, 1, 2, 1, 4]
def baseStart_3856828 : Nat := 118140960795 + 3856828 * 2 ^ 59
def prefixEnd_3856828 : Nat := 4983230072969 + 3 ^ 40 * 3856828 * 2
def baseEnd_3856828 : Nat := 1980406565718941376412777

theorem tailTrace_3856828 : CollatzResearch.WordTrace tailWord_3856828 prefixEnd_3856828 1980406565718941376412777 := by
  unfold tailWord_3856828
  simp only [CollatzResearch.WordTrace]
  refine ⟨70335036835689162313109569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93780049114252216417479425 70335036835689162313109569)
  ·
    refine ⟨52751277626766871734832177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70335036835689162313109569 52751277626766871734832177)
    ·
      refine ⟨39563458220075153801124133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52751277626766871734832177 39563458220075153801124133)
      ·
        refine ⟨7418148416264091337710775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 39563458220075153801124133 7418148416264091337710775)
        ·
          refine ⟨11127222624396137006566163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7418148416264091337710775 11127222624396137006566163)
          ·
            refine ⟨16690833936594205509849245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11127222624396137006566163 16690833936594205509849245)
            ·
              refine ⟨6259062726222827066193467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16690833936594205509849245 6259062726222827066193467)
              ·
                refine ⟨9388594089334240599290201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6259062726222827066193467 9388594089334240599290201)
                ·
                  refine ⟨7041445567000680449467651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9388594089334240599290201 7041445567000680449467651)
                  ·
                    refine ⟨10562168350501020674201477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7041445567000680449467651 10562168350501020674201477)
                    ·
                      refine ⟨1980406565718941376412777, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10562168350501020674201477 1980406565718941376412777)
                      ·
                        rfl

theorem cell23_3856828_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 1, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 1, 3, 1, 2, 1, 4].length) (baseStart_3856828 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3856828 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3856828 prefixEnd_3856828 := by exact prefixLift 3856828
  have htrace : WordTrace (prefixWord ++ tailWord_3856828) baseStart_3856828 baseEnd_3856828 := by
    simpa [prefixWord, tailWord_3856828, baseEnd_3856828] using wordTrace_append hprefix tailTrace_3856828
  have hstable : (prefixWord ++ tailWord_3856828).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3856828).length < 2 ^ (prefixWord ++ tailWord_3856828).sum := by decide
  have hdescent : baseEnd_3856828 < baseStart_3856828 := by decide
  rcases family_descends (prefixWord ++ tailWord_3856828) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3856888 : List Nat := [2, 1, 2, 1, 1, 4, 2, 3, 2, 3, 2]
def baseStart_3856888 : Nat := 118140960795 + 3856888 * 2 ^ 59
def prefixEnd_3856888 : Nat := 4983230072969 + 3 ^ 40 * 3856888 * 2
def baseEnd_3856888 : Nat := 1980437374558211141662501

theorem tailTrace_3856888 : CollatzResearch.WordTrace tailWord_3856888 prefixEnd_3856888 1980437374558211141662501 := by
  unfold tailWord_3856888
  simp only [CollatzResearch.WordTrace]
  refine ⟨70336131025580477436701659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93781508034107303248935545 70336131025580477436701659)
  ·
    refine ⟨105504196538370716155052489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70336131025580477436701659 105504196538370716155052489)
    ·
      refine ⟨79128147403778037116289367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 105504196538370716155052489 79128147403778037116289367)
      ·
        refine ⟨118692221105667055674434051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79128147403778037116289367 118692221105667055674434051)
        ·
          refine ⟨178038331658500583511651077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 118692221105667055674434051 178038331658500583511651077)
          ·
            refine ⟨33382187185968859408434577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 178038331658500583511651077 33382187185968859408434577)
            ·
              refine ⟨25036640389476644556325933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33382187185968859408434577 25036640389476644556325933)
              ·
                refine ⟨9388740146053741708622225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25036640389476644556325933 9388740146053741708622225)
                ·
                  refine ⟨7041555109540306281466669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9388740146053741708622225 7041555109540306281466669)
                  ·
                    refine ⟨2640583166077614855550001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7041555109540306281466669 2640583166077614855550001)
                    ·
                      refine ⟨1980437374558211141662501, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2640583166077614855550001 1980437374558211141662501)
                      ·
                        rfl

theorem cell23_3856888_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 2, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 2, 3, 2, 3, 2].length) (baseStart_3856888 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3856888 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3856888 prefixEnd_3856888 := by exact prefixLift 3856888
  have htrace : WordTrace (prefixWord ++ tailWord_3856888) baseStart_3856888 baseEnd_3856888 := by
    simpa [prefixWord, tailWord_3856888, baseEnd_3856888] using wordTrace_append hprefix tailTrace_3856888
  have hstable : (prefixWord ++ tailWord_3856888).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3856888).length < 2 ^ (prefixWord ++ tailWord_3856888).sum := by decide
  have hdescent : baseEnd_3856888 < baseStart_3856888 := by decide
  rcases family_descends (prefixWord ++ tailWord_3856888) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3856921 : List Nat := [1, 2, 1, 2, 1, 1, 2, 3, 5, 2, 3]
def baseStart_3856921 : Nat := 118140960795 + 3856921 * 2 ^ 59
def prefixEnd_3856921 : Nat := 4983230072969 + 3 ^ 40 * 3856921 * 2
def baseEnd_3856921 : Nat := 1980454319419809512549849

theorem tailTrace_3856921 : CollatzResearch.WordTrace tailWord_3856921 prefixEnd_3856921 1980454319419809512549849 := by
  unfold tailWord_3856921
  simp only [CollatzResearch.WordTrace]
  refine ⟨140673465660041401509354617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93782310440027601006236411 140673465660041401509354617)
  ·
    refine ⟨105505099245031051132015963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 140673465660041401509354617 105505099245031051132015963)
    ·
      refine ⟨158257648867546576698023945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105505099245031051132015963 158257648867546576698023945)
      ·
        refine ⟨118693236650659932523517959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 158257648867546576698023945 118693236650659932523517959)
        ·
          refine ⟨178039854975989898785276939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 118693236650659932523517959 178039854975989898785276939)
          ·
            refine ⟨267059782463984848177915409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 178039854975989898785276939 267059782463984848177915409)
            ·
              refine ⟨200294836847988636133436557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 267059782463984848177915409 200294836847988636133436557)
              ·
                refine ⟨75110563817995738550038709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 200294836847988636133436557 75110563817995738550038709)
                ·
                  refine ⟨7041615357937100489066129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 75110563817995738550038709 7041615357937100489066129)
                  ·
                    refine ⟨5281211518452825366799597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7041615357937100489066129 5281211518452825366799597)
                    ·
                      refine ⟨1980454319419809512549849, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5281211518452825366799597 1980454319419809512549849)
                      ·
                        rfl

theorem cell23_3856921_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 2, 3, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 2, 3, 5, 2, 3].length) (baseStart_3856921 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3856921 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3856921 prefixEnd_3856921 := by exact prefixLift 3856921
  have htrace : WordTrace (prefixWord ++ tailWord_3856921) baseStart_3856921 baseEnd_3856921 := by
    simpa [prefixWord, tailWord_3856921, baseEnd_3856921] using wordTrace_append hprefix tailTrace_3856921
  have hstable : (prefixWord ++ tailWord_3856921).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3856921).length < 2 ^ (prefixWord ++ tailWord_3856921).sum := by decide
  have hdescent : baseEnd_3856921 < baseStart_3856921 := by decide
  rcases family_descends (prefixWord ++ tailWord_3856921) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3856931 : List Nat := [1, 1, 1, 4, 4, 1, 2, 1, 1, 1, 6]
def baseStart_3856931 : Nat := 118140960795 + 3856931 * 2 ^ 59
def prefixEnd_3856931 : Nat := 4983230072969 + 3 ^ 40 * 3856931 * 2
def baseEnd_3856931 : Nat := 1980459454226354473424803

theorem tailTrace_3856931 : CollatzResearch.WordTrace tailWord_3856931 prefixEnd_3856931 1980459454226354473424803 := by
  unfold tailWord_3856931
  simp only [CollatzResearch.WordTrace]
  refine ⟨140673830390005173217218647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93782553593336782144812431 140673830390005173217218647)
  ·
    refine ⟨211010745585007759825827971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140673830390005173217218647 211010745585007759825827971)
    ·
      refine ⟨316516118377511639738741957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 211010745585007759825827971 316516118377511639738741957)
      ·
        refine ⟨59346772195783432451014117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 316516118377511639738741957 59346772195783432451014117)
        ·
          refine ⟨11127519786709393584565147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 59346772195783432451014117 11127519786709393584565147)
          ·
            refine ⟨16691279680064090376847721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11127519786709393584565147 16691279680064090376847721)
            ·
              refine ⟨12518459760048067782635791, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16691279680064090376847721 12518459760048067782635791)
              ·
                refine ⟨18777689640072101673953687, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12518459760048067782635791 18777689640072101673953687)
                ·
                  refine ⟨28166534460108152510930531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18777689640072101673953687 28166534460108152510930531)
                  ·
                    refine ⟨42249801690162228766395797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 28166534460108152510930531 42249801690162228766395797)
                    ·
                      refine ⟨1980459454226354473424803, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 42249801690162228766395797 1980459454226354473424803)
                      ·
                        rfl

theorem cell23_3856931_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 1, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 1, 2, 1, 1, 1, 6].length) (baseStart_3856931 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3856931 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3856931 prefixEnd_3856931 := by exact prefixLift 3856931
  have htrace : WordTrace (prefixWord ++ tailWord_3856931) baseStart_3856931 baseEnd_3856931 := by
    simpa [prefixWord, tailWord_3856931, baseEnd_3856931] using wordTrace_append hprefix tailTrace_3856931
  have hstable : (prefixWord ++ tailWord_3856931).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3856931).length < 2 ^ (prefixWord ++ tailWord_3856931).sum := by decide
  have hdescent : baseEnd_3856931 < baseStart_3856931 := by decide
  rcases family_descends (prefixWord ++ tailWord_3856931) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3856932 : List Nat := [2, 3, 1, 5, 1, 2, 1, 2, 1, 5]
def baseStart_3856932 : Nat := 118140960795 + 3856932 * 2 ^ 59
def prefixEnd_3856932 : Nat := 4983230072969 + 3 ^ 40 * 3856932 * 2
def baseEnd_3856932 : Nat := 660153322569002989837433

theorem tailTrace_3856932 : CollatzResearch.WordTrace tailWord_3856932 prefixEnd_3856932 660153322569002989837433 := by
  unfold tailWord_3856932
  simp only [CollatzResearch.WordTrace]
  refine ⟨70336933431500775194002525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93782577908667700258670033 70336933431500775194002525)
  ·
    refine ⟨26376350036812790697750947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 70336933431500775194002525 26376350036812790697750947)
    ·
      refine ⟨39564525055219186046626421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26376350036812790697750947 39564525055219186046626421)
      ·
        refine ⟨3709174223926798691871227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 39564525055219186046626421 3709174223926798691871227)
        ·
          refine ⟨5563761335890198037806841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3709174223926798691871227 5563761335890198037806841)
          ·
            refine ⟨4172821001917648528355131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5563761335890198037806841 4172821001917648528355131)
            ·
              refine ⟨6259231502876472792532697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4172821001917648528355131 6259231502876472792532697)
              ·
                refine ⟨4694423627157354594399523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6259231502876472792532697 4694423627157354594399523)
                ·
                  refine ⟨7041635440736031891599285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4694423627157354594399523 7041635440736031891599285)
                  ·
                    refine ⟨660153322569002989837433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7041635440736031891599285 660153322569002989837433)
                    ·
                      rfl

theorem cell23_3856932_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 5, 1, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 5, 1, 2, 1, 2, 1, 5].length) (baseStart_3856932 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3856932 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3856932 prefixEnd_3856932 := by exact prefixLift 3856932
  have htrace : WordTrace (prefixWord ++ tailWord_3856932) baseStart_3856932 baseEnd_3856932 := by
    simpa [prefixWord, tailWord_3856932, baseEnd_3856932] using wordTrace_append hprefix tailTrace_3856932
  have hstable : (prefixWord ++ tailWord_3856932).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3856932).length < 2 ^ (prefixWord ++ tailWord_3856932).sum := by decide
  have hdescent : baseEnd_3856932 < baseStart_3856932 := by decide
  rcases family_descends (prefixWord ++ tailWord_3856932) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3856952 : List Nat := [2, 1, 2, 1, 4, 1, 2, 5, 1, 2, 2]
def baseStart_3856952 : Nat := 118140960795 + 3856952 * 2 ^ 59
def prefixEnd_3856952 : Nat := 4983230072969 + 3 ^ 40 * 3856952 * 2
def baseEnd_3856952 : Nat := 1980470237320098891262207

theorem tailTrace_3856952 : CollatzResearch.WordTrace tailWord_3856952 prefixEnd_3856952 1980470237320098891262207 := by
  unfold tailWord_3856952
  simp only [CollatzResearch.WordTrace]
  refine ⟨70337298161464546901866555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93783064215286062535822073 70337298161464546901866555)
  ·
    refine ⟨105505947242196820352799833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70337298161464546901866555 105505947242196820352799833)
    ·
      refine ⟨79129460431647615264599875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 105505947242196820352799833 79129460431647615264599875)
      ·
        refine ⟨118694190647471422896899813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79129460431647615264599875 118694190647471422896899813)
        ·
          refine ⟨22255160746400891793168715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 118694190647471422896899813 22255160746400891793168715)
          ·
            refine ⟨33382741119601337689753073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22255160746400891793168715 33382741119601337689753073)
            ·
              refine ⟨25037055839701003267314805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33382741119601337689753073 25037055839701003267314805)
              ·
                refine ⟨2347223984971969056310763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 25037055839701003267314805 2347223984971969056310763)
                ·
                  refine ⟨3520835977457953584466145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2347223984971969056310763 3520835977457953584466145)
                  ·
                    refine ⟨2640626983093465188349609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3520835977457953584466145 2640626983093465188349609)
                    ·
                      refine ⟨1980470237320098891262207, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2640626983093465188349609 1980470237320098891262207)
                      ·
                        rfl

theorem cell23_3856952_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 2, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 2, 5, 1, 2, 2].length) (baseStart_3856952 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3856952 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3856952 prefixEnd_3856952 := by exact prefixLift 3856952
  have htrace : WordTrace (prefixWord ++ tailWord_3856952) baseStart_3856952 baseEnd_3856952 := by
    simpa [prefixWord, tailWord_3856952, baseEnd_3856952] using wordTrace_append hprefix tailTrace_3856952
  have hstable : (prefixWord ++ tailWord_3856952).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3856952).length < 2 ^ (prefixWord ++ tailWord_3856952).sum := by decide
  have hdescent : baseEnd_3856952 < baseStart_3856952 := by decide
  rcases family_descends (prefixWord ++ tailWord_3856952) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3856958 : List Nat := [4, 2, 1, 4, 1, 11]
def baseStart_3856958 : Nat := 118140960795 + 3856958 * 2 ^ 59
def prefixEnd_3856958 : Nat := 4983230072969 + 3 ^ 40 * 3856958 * 2
def baseEnd_3856958 : Nat := 8150095959687349250153

theorem tailTrace_3856958 : CollatzResearch.WordTrace tailWord_3856958 prefixEnd_3856958 8150095959687349250153 := by
  unfold tailWord_3856958
  simp only [CollatzResearch.WordTrace]
  refine ⟨17584351895113419603556441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 93783210107271571218967685 17584351895113419603556441)
  ·
    refine ⟨13188263921335064702667331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17584351895113419603556441 13188263921335064702667331)
    ·
      refine ⟨19782395882002597054000997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13188263921335064702667331 19782395882002597054000997)
      ·
        refine ⟨3709199227875486947625187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 19782395882002597054000997 3709199227875486947625187)
        ·
          refine ⟨5563798841813230421437781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3709199227875486947625187 5563798841813230421437781)
          ·
            refine ⟨8150095959687349250153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 5563798841813230421437781 8150095959687349250153)
            ·
              rfl

theorem cell23_3856958_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 4, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 4, 1, 11].length) (baseStart_3856958 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3856958 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3856958 prefixEnd_3856958 := by exact prefixLift 3856958
  have htrace : WordTrace (prefixWord ++ tailWord_3856958) baseStart_3856958 baseEnd_3856958 := by
    simpa [prefixWord, tailWord_3856958, baseEnd_3856958] using wordTrace_append hprefix tailTrace_3856958
  have hstable : (prefixWord ++ tailWord_3856958).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3856958).length < 2 ^ (prefixWord ++ tailWord_3856958).sum := by decide
  have hdescent : baseEnd_3856958 < baseStart_3856958 := by decide
  rcases family_descends (prefixWord ++ tailWord_3856958) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3856968 : List Nat := [2, 1, 3, 1, 1, 1, 1, 5, 4, 1, 3]
def baseStart_3856968 : Nat := 118140960795 + 3856968 * 2 ^ 59
def prefixEnd_3856968 : Nat := 4983230072969 + 3 ^ 40 * 3856968 * 2
def baseEnd_3856968 : Nat := 1980478453010570828662133

theorem tailTrace_3856968 : CollatzResearch.WordTrace tailWord_3856968 prefixEnd_3856968 1980478453010570828662133 := by
  unfold tailWord_3856968
  simp only [CollatzResearch.WordTrace]
  refine ⟨70337589945435564268157779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93783453260580752357543705 70337589945435564268157779)
  ·
    refine ⟨105506384918153346402236669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70337589945435564268157779 105506384918153346402236669)
    ·
      refine ⟨39564894344307504900838751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 105506384918153346402236669 39564894344307504900838751)
      ·
        refine ⟨59347341516461257351258127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39564894344307504900838751 59347341516461257351258127)
        ·
          refine ⟨89021012274691886026887191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59347341516461257351258127 89021012274691886026887191)
          ·
            refine ⟨133531518412037829040330787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 89021012274691886026887191 133531518412037829040330787)
            ·
              refine ⟨200297277618056743560496181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 133531518412037829040330787 200297277618056743560496181)
              ·
                refine ⟨18777869776692819708796517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 200297277618056743560496181 18777869776692819708796517)
                ·
                  refine ⟨3520850583129903695399347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 18777869776692819708796517 3520850583129903695399347)
                  ·
                    refine ⟨5281275874694855543099021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3520850583129903695399347 5281275874694855543099021)
                    ·
                      refine ⟨1980478453010570828662133, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5281275874694855543099021 1980478453010570828662133)
                      ·
                        rfl

theorem cell23_3856968_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 1, 5, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 1, 5, 4, 1, 3].length) (baseStart_3856968 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3856968 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3856968 prefixEnd_3856968 := by exact prefixLift 3856968
  have htrace : WordTrace (prefixWord ++ tailWord_3856968) baseStart_3856968 baseEnd_3856968 := by
    simpa [prefixWord, tailWord_3856968, baseEnd_3856968] using wordTrace_append hprefix tailTrace_3856968
  have hstable : (prefixWord ++ tailWord_3856968).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3856968).length < 2 ^ (prefixWord ++ tailWord_3856968).sum := by decide
  have hdescent : baseEnd_3856968 < baseStart_3856968 := by decide
  rcases family_descends (prefixWord ++ tailWord_3856968) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3856995 : List Nat := [1, 1, 1, 5, 1, 2, 2, 4, 1, 3, 2]
def baseStart_3856995 : Nat := 118140960795 + 3856995 * 2 ^ 59
def prefixEnd_3856995 : Nat := 4983230072969 + 3 ^ 40 * 3856995 * 2
def baseEnd_3856995 : Nat := 1980492316988242223024509

theorem tailTrace_3856995 : CollatzResearch.WordTrace tailWord_3856995 prefixEnd_3856995 1980492316988242223024509 := by
  unfold tailWord_3856995
  simp only [CollatzResearch.WordTrace]
  refine ⟨140676164661773312147548439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93784109774515541431698959 140676164661773312147548439)
  ·
    refine ⟨211014246992659968221322659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140676164661773312147548439 211014246992659968221322659)
    ·
      refine ⟨316521370488989952331983989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 211014246992659968221322659 316521370488989952331983989)
      ·
        refine ⟨29673878483342808031123499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 316521370488989952331983989 29673878483342808031123499)
        ·
          refine ⟨44510817725014212046685249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29673878483342808031123499 44510817725014212046685249)
          ·
            refine ⟨33383113293760659035013937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44510817725014212046685249 33383113293760659035013937)
            ·
              refine ⟨25037334970320494276260453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33383113293760659035013937 25037334970320494276260453)
              ·
                refine ⟨4694500306935092676798835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25037334970320494276260453 4694500306935092676798835)
                ·
                  refine ⟨7041750460402639015198253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4694500306935092676798835 7041750460402639015198253)
                  ·
                    refine ⟨2640656422650989630699345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7041750460402639015198253 2640656422650989630699345)
                    ·
                      refine ⟨1980492316988242223024509, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2640656422650989630699345 1980492316988242223024509)
                      ·
                        rfl

theorem cell23_3856995_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 2, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 2, 4, 1, 3, 2].length) (baseStart_3856995 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3856995 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3856995 prefixEnd_3856995 := by exact prefixLift 3856995
  have htrace : WordTrace (prefixWord ++ tailWord_3856995) baseStart_3856995 baseEnd_3856995 := by
    simpa [prefixWord, tailWord_3856995, baseEnd_3856995] using wordTrace_append hprefix tailTrace_3856995
  have hstable : (prefixWord ++ tailWord_3856995).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3856995).length < 2 ^ (prefixWord ++ tailWord_3856995).sum := by decide
  have hdescent : baseEnd_3856995 < baseStart_3856995 := by decide
  rcases family_descends (prefixWord ++ tailWord_3856995) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3857011 : List Nat := [1, 1, 1, 2, 2, 1, 1, 4, 1, 6, 3]
def baseStart_3857011 : Nat := 118140960795 + 3857011 * 2 ^ 59
def prefixEnd_3857011 : Nat := 4983230072969 + 3 ^ 40 * 3857011 * 2
def baseEnd_3857011 : Nat := 1980500532678714160424435

theorem tailTrace_3857011 : CollatzResearch.WordTrace tailWord_3857011 prefixEnd_3857011 1980500532678714160424435 := by
  unfold tailWord_3857011
  simp only [CollatzResearch.WordTrace]
  refine ⟨140676748229715346880130887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93784498819810231253420591 140676748229715346880130887)
  ·
    refine ⟨211015122344573020320196331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140676748229715346880130887 211015122344573020320196331)
    ·
      refine ⟨316522683516859530480294497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 211015122344573020320196331 316522683516859530480294497)
      ·
        refine ⟨237392012637644647860220873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 316522683516859530480294497 237392012637644647860220873)
        ·
          refine ⟨178044009478233485895165655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 237392012637644647860220873 178044009478233485895165655)
          ·
            refine ⟨267066014217350228842748483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 178044009478233485895165655 267066014217350228842748483)
            ·
              refine ⟨400599021326025343264122725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 267066014217350228842748483 400599021326025343264122725)
              ·
                refine ⟨75112316498629751862023011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 400599021326025343264122725 75112316498629751862023011)
                ·
                  refine ⟨112668474747944627793034517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 75112316498629751862023011 112668474747944627793034517)
                  ·
                    refine ⟨5281334753809904427798493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 112668474747944627793034517 5281334753809904427798493)
                    ·
                      refine ⟨1980500532678714160424435, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5281334753809904427798493 1980500532678714160424435)
                      ·
                        rfl

theorem cell23_3857011_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 4, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 4, 1, 6, 3].length) (baseStart_3857011 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3857011 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3857011 prefixEnd_3857011 := by exact prefixLift 3857011
  have htrace : WordTrace (prefixWord ++ tailWord_3857011) baseStart_3857011 baseEnd_3857011 := by
    simpa [prefixWord, tailWord_3857011, baseEnd_3857011] using wordTrace_append hprefix tailTrace_3857011
  have hstable : (prefixWord ++ tailWord_3857011).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3857011).length < 2 ^ (prefixWord ++ tailWord_3857011).sum := by decide
  have hdescent : baseEnd_3857011 < baseStart_3857011 := by decide
  rcases family_descends (prefixWord ++ tailWord_3857011) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3857038 : List Nat := [4, 1, 1, 3, 1, 1, 1, 3, 2, 2, 4]
def baseStart_3857038 : Nat := 118140960795 + 3857038 * 2 ^ 59
def prefixEnd_3857038 : Nat := 4983230072969 + 3 ^ 40 * 3857038 * 2
def baseEnd_3857038 : Nat := 1980514396656385554786811

theorem tailTrace_3857038 : CollatzResearch.WordTrace tailWord_3857038 prefixEnd_3857038 1980514396656385554786811 := by
  unfold tailWord_3857038
  simp only [CollatzResearch.WordTrace]
  refine ⟨17584716625077191311420471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 93785155333745020327575845 17584716625077191311420471)
  ·
    refine ⟨26377074937615786967130707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17584716625077191311420471 26377074937615786967130707)
    ·
      refine ⟨39565612406423680450696061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26377074937615786967130707 39565612406423680450696061)
      ·
        refine ⟨14837104652408880169011023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 39565612406423680450696061 14837104652408880169011023)
        ·
          refine ⟨22255656978613320253516535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14837104652408880169011023 22255656978613320253516535)
          ·
            refine ⟨33383485467919980380274803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22255656978613320253516535 33383485467919980380274803)
            ·
              refine ⟨50075228201879970570412205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33383485467919980380274803 50075228201879970570412205)
              ·
                refine ⟨18778210575704988963904577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 50075228201879970570412205 18778210575704988963904577)
                ·
                  refine ⟨14083657931778741722928433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18778210575704988963904577 14083657931778741722928433)
                  ·
                    refine ⟨10562743448834056292196325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14083657931778741722928433 10562743448834056292196325)
                    ·
                      refine ⟨1980514396656385554786811, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10562743448834056292196325 1980514396656385554786811)
                      ·
                        rfl

theorem cell23_3857038_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 1, 3, 2, 2, 4].length) (baseStart_3857038 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3857038 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3857038 prefixEnd_3857038 := by exact prefixLift 3857038
  have htrace : WordTrace (prefixWord ++ tailWord_3857038) baseStart_3857038 baseEnd_3857038 := by
    simpa [prefixWord, tailWord_3857038, baseEnd_3857038] using wordTrace_append hprefix tailTrace_3857038
  have hstable : (prefixWord ++ tailWord_3857038).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3857038).length < 2 ^ (prefixWord ++ tailWord_3857038).sum := by decide
  have hdescent : baseEnd_3857038 < baseStart_3857038 := by decide
  rcases family_descends (prefixWord ++ tailWord_3857038) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3857042 : List Nat := [3, 2, 3, 1, 2, 1, 3, 1, 1, 4, 2]
def baseStart_3857042 : Nat := 118140960795 + 3857042 * 2 ^ 59
def prefixEnd_3857042 : Nat := 4983230072969 + 3 ^ 40 * 3857042 * 2
def baseEnd_3857042 : Nat := 1980516450579003539136793

theorem tailTrace_3857042 : CollatzResearch.WordTrace tailWord_3857042 prefixEnd_3857042 1980516450579003539136793 := by
  unfold tailWord_3857042
  simp only [CollatzResearch.WordTrace]
  refine ⟨35169469723150759793627345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 93785252595068692783006253 35169469723150759793627345)
  ·
    refine ⟨26377102292363069845220509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35169469723150759793627345 26377102292363069845220509)
    ·
      refine ⟨9891413359636151191957691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26377102292363069845220509 9891413359636151191957691)
      ·
        refine ⟨14837120039454226787936537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9891413359636151191957691 14837120039454226787936537)
        ·
          refine ⟨11127840029590670090952403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14837120039454226787936537 11127840029590670090952403)
          ·
            refine ⟨16691760044386005136428605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11127840029590670090952403 16691760044386005136428605)
            ·
              refine ⟨6259410016644751926160727, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16691760044386005136428605 6259410016644751926160727)
              ·
                refine ⟨9389115024967127889241091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6259410016644751926160727 9389115024967127889241091)
                ·
                  refine ⟨14083672537450691833861637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9389115024967127889241091 14083672537450691833861637)
                  ·
                    refine ⟨2640688600772004718849057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 14083672537450691833861637 2640688600772004718849057)
                    ·
                      refine ⟨1980516450579003539136793, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2640688600772004718849057 1980516450579003539136793)
                      ·
                        rfl

theorem cell23_3857042_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 1, 3, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 1, 3, 1, 1, 4, 2].length) (baseStart_3857042 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3857042 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3857042 prefixEnd_3857042 := by exact prefixLift 3857042
  have htrace : WordTrace (prefixWord ++ tailWord_3857042) baseStart_3857042 baseEnd_3857042 := by
    simpa [prefixWord, tailWord_3857042, baseEnd_3857042] using wordTrace_append hprefix tailTrace_3857042
  have hstable : (prefixWord ++ tailWord_3857042).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3857042).length < 2 ^ (prefixWord ++ tailWord_3857042).sum := by decide
  have hdescent : baseEnd_3857042 < baseStart_3857042 := by decide
  rcases family_descends (prefixWord ++ tailWord_3857042) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3857088 : List Nat := [2, 1, 1, 2, 4, 3, 1, 1, 1, 2, 5]
def baseStart_3857088 : Nat := 118140960795 + 3857088 * 2 ^ 59
def prefixEnd_3857088 : Nat := 4983230072969 + 3 ^ 40 * 3857088 * 2
def baseEnd_3857088 : Nat := 1980540070689110359161581

theorem tailTrace_3857088 : CollatzResearch.WordTrace tailWord_3857088 prefixEnd_3857088 1980540070689110359161581 := by
  unfold tailWord_3857088
  simp only [CollatzResearch.WordTrace]
  refine ⟨70339778325218194515341959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93786371100290926020455945 70339778325218194515341959)
  ·
    refine ⟨105509667487827291773012939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70339778325218194515341959 105509667487827291773012939)
    ·
      refine ⟨158264501231740937659519409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105509667487827291773012939 158264501231740937659519409)
      ·
        refine ⟨118698375923805703244639557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 158264501231740937659519409 118698375923805703244639557)
        ·
          refine ⟨22255945485713569358369917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 118698375923805703244639557 22255945485713569358369917)
          ·
            refine ⟨8345979557142588509388719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22255945485713569358369917 8345979557142588509388719)
            ·
              refine ⟨12518969335713882764083079, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8345979557142588509388719 12518969335713882764083079)
              ·
                refine ⟨18778454003570824146124619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12518969335713882764083079 18778454003570824146124619)
                ·
                  refine ⟨28167681005356236219186929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18778454003570824146124619 28167681005356236219186929)
                  ·
                    refine ⟨21125760754017177164390197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 28167681005356236219186929 21125760754017177164390197)
                    ·
                      refine ⟨1980540070689110359161581, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 21125760754017177164390197 1980540070689110359161581)
                      ·
                        rfl

theorem cell23_3857088_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 3, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 3, 1, 1, 1, 2, 5].length) (baseStart_3857088 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3857088 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3857088 prefixEnd_3857088 := by exact prefixLift 3857088
  have htrace : WordTrace (prefixWord ++ tailWord_3857088) baseStart_3857088 baseEnd_3857088 := by
    simpa [prefixWord, tailWord_3857088, baseEnd_3857088] using wordTrace_append hprefix tailTrace_3857088
  have hstable : (prefixWord ++ tailWord_3857088).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3857088).length < 2 ^ (prefixWord ++ tailWord_3857088).sum := by decide
  have hdescent : baseEnd_3857088 < baseStart_3857088 := by decide
  rcases family_descends (prefixWord ++ tailWord_3857088) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3857135 : List Nat := [1, 1, 2, 1, 5, 2, 2, 2, 2, 2, 3]
def baseStart_3857135 : Nat := 118140960795 + 3857135 * 2 ^ 59
def prefixEnd_3857135 : Nat := 4983230072969 + 3 ^ 40 * 3857135 * 2
def baseEnd_3857135 : Nat := 1980564204279871675273865

theorem tailTrace_3857135 : CollatzResearch.WordTrace tailWord_3857135 prefixEnd_3857135 1980564204279871675273865 := by
  unfold tailWord_3857135
  simp only [CollatzResearch.WordTrace]
  refine ⟨140681270881266116057644859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93787513920844077371763239 140681270881266116057644859)
  ·
    refine ⟨211021906321899174086467289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140681270881266116057644859 211021906321899174086467289)
    ·
      refine ⟨158266429741424380564850467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 211021906321899174086467289 158266429741424380564850467)
      ·
        refine ⟨237399644612136570847275701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 158266429741424380564850467 237399644612136570847275701)
        ·
          refine ⟨22256216682387803516932097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 237399644612136570847275701 22256216682387803516932097)
          ·
            refine ⟨16692162511790852637699073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22256216682387803516932097 16692162511790852637699073)
            ·
              refine ⟨12519121883843139478274305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16692162511790852637699073 12519121883843139478274305)
              ·
                refine ⟨9389341412882354608705729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12519121883843139478274305 9389341412882354608705729)
                ·
                  refine ⟨7042006059661765956529297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9389341412882354608705729 7042006059661765956529297)
                  ·
                    refine ⟨5281504544746324467396973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7042006059661765956529297 5281504544746324467396973)
                    ·
                      refine ⟨1980564204279871675273865, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5281504544746324467396973 1980564204279871675273865)
                      ·
                        rfl

theorem cell23_3857135_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 2, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 2, 2, 2, 2, 2, 3].length) (baseStart_3857135 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3857135 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3857135 prefixEnd_3857135 := by exact prefixLift 3857135
  have htrace : WordTrace (prefixWord ++ tailWord_3857135) baseStart_3857135 baseEnd_3857135 := by
    simpa [prefixWord, tailWord_3857135, baseEnd_3857135] using wordTrace_append hprefix tailTrace_3857135
  have hstable : (prefixWord ++ tailWord_3857135).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3857135).length < 2 ^ (prefixWord ++ tailWord_3857135).sum := by decide
  have hdescent : baseEnd_3857135 < baseStart_3857135 := by decide
  rcases family_descends (prefixWord ++ tailWord_3857135) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3857185 : List Nat := [1, 2, 3, 2, 1, 2, 3, 3, 1, 5]
def baseStart_3857185 : Nat := 118140960795 + 3857185 * 2 ^ 59
def prefixEnd_3857185 : Nat := 4983230072969 + 3 ^ 40 * 3857185 * 2
def baseEnd_3857185 : Nat := 660196626104198826549545

theorem tailTrace_3857185 : CollatzResearch.WordTrace tailWord_3857185 prefixEnd_3857185 660196626104198826549545 := by
  unfold tailWord_3857185
  simp only [CollatzResearch.WordTrace]
  refine ⟨140683094531084974596965009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93788729687389983064643339 140683094531084974596965009)
  ·
    refine ⟨105512320898313730947723757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 140683094531084974596965009 105512320898313730947723757)
    ·
      refine ⟨39567120336867649105396409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 105512320898313730947723757 39567120336867649105396409)
      ·
        refine ⟨29675340252650736829047307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39567120336867649105396409 29675340252650736829047307)
        ·
          refine ⟨44513010378976105243570961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29675340252650736829047307 44513010378976105243570961)
          ·
            refine ⟨33384757784232078932678221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44513010378976105243570961 33384757784232078932678221)
            ·
              refine ⟨12519284169087029599754333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33384757784232078932678221 12519284169087029599754333)
              ·
                refine ⟨4694731563407636099907875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12519284169087029599754333 4694731563407636099907875)
                ·
                  refine ⟨7042097345111454149861813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4694731563407636099907875 7042097345111454149861813)
                  ·
                    refine ⟨660196626104198826549545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7042097345111454149861813 660196626104198826549545)
                    ·
                      rfl

theorem cell23_3857185_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 3, 3, 1, 5].length) (baseStart_3857185 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3857185 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3857185 prefixEnd_3857185 := by exact prefixLift 3857185
  have htrace : WordTrace (prefixWord ++ tailWord_3857185) baseStart_3857185 baseEnd_3857185 := by
    simpa [prefixWord, tailWord_3857185, baseEnd_3857185] using wordTrace_append hprefix tailTrace_3857185
  have hstable : (prefixWord ++ tailWord_3857185).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3857185).length < 2 ^ (prefixWord ++ tailWord_3857185).sum := by decide
  have hdescent : baseEnd_3857185 < baseStart_3857185 := by decide
  rcases family_descends (prefixWord ++ tailWord_3857185) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3857192 : List Nat := [2, 1, 5, 1, 1, 1, 2, 1, 4, 3, 2]
def baseStart_3857192 : Nat := 118140960795 + 3857192 * 2 ^ 59
def prefixEnd_3857192 : Nat := 4983230072969 + 3 ^ 40 * 3857192 * 2
def baseEnd_3857192 : Nat := 1980593472677177952261103

theorem tailTrace_3857192 : CollatzResearch.WordTrace tailWord_3857192 prefixEnd_3857192 1980593472677177952261103 := by
  unfold tailWord_3857192
  simp only [CollatzResearch.WordTrace]
  refine ⟨70341674921029807396234915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93788899894706409861646553 70341674921029807396234915)
  ·
    refine ⟨105512512381544711094352373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70341674921029807396234915 105512512381544711094352373)
    ·
      refine ⟨9891798035769816665095535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 105512512381544711094352373 9891798035769816665095535)
      ·
        refine ⟨14837697053654724997643303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9891798035769816665095535 14837697053654724997643303)
        ·
          refine ⟨22256545580482087496464955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14837697053654724997643303 22256545580482087496464955)
          ·
            refine ⟨33384818370723131244697433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22256545580482087496464955 33384818370723131244697433)
            ·
              refine ⟨25038613778042348433523075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33384818370723131244697433 25038613778042348433523075)
              ·
                refine ⟨37557920667063522650284613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25038613778042348433523075 37557920667063522650284613)
                ·
                  refine ⟨7042110125074410496928365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 37557920667063522650284613 7042110125074410496928365)
                  ·
                    refine ⟨2640791296902903936348137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7042110125074410496928365 2640791296902903936348137)
                    ·
                      refine ⟨1980593472677177952261103, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2640791296902903936348137 1980593472677177952261103)
                      ·
                        rfl

theorem cell23_3857192_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 2, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 2, 1, 4, 3, 2].length) (baseStart_3857192 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3857192 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3857192 prefixEnd_3857192 := by exact prefixLift 3857192
  have htrace : WordTrace (prefixWord ++ tailWord_3857192) baseStart_3857192 baseEnd_3857192 := by
    simpa [prefixWord, tailWord_3857192, baseEnd_3857192] using wordTrace_append hprefix tailTrace_3857192
  have hstable : (prefixWord ++ tailWord_3857192).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3857192).length < 2 ^ (prefixWord ++ tailWord_3857192).sum := by decide
  have hdescent : baseEnd_3857192 < baseStart_3857192 := by decide
  rcases family_descends (prefixWord ++ tailWord_3857192) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3857215 : List Nat := [1, 1, 2, 2, 5, 1, 3, 1, 1, 6]
def baseStart_3857215 : Nat := 118140960795 + 3857215 * 2 ^ 59
def prefixEnd_3857215 : Nat := 4983230072969 + 3 ^ 40 * 3857215 * 2
def baseEnd_3857215 : Nat := 660201760910743787424499

theorem tailTrace_3857215 : CollatzResearch.WordTrace tailWord_3857215 prefixEnd_3857215 660201760910743787424499 := by
  unfold tailWord_3857215
  simp only [CollatzResearch.WordTrace]
  refine ⟨140684188720976289720557099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93789459147317526480371399 140684188720976289720557099)
  ·
    refine ⟨211026283081464434580835649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140684188720976289720557099 211026283081464434580835649)
    ·
      refine ⟨158269712311098325935626737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 211026283081464434580835649 158269712311098325935626737)
      ·
        refine ⟨118702284233323744451720053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 158269712311098325935626737 118702284233323744451720053)
        ·
          refine ⟨11128339146874101042348755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 118702284233323744451720053 11128339146874101042348755)
          ·
            refine ⟨16692508720311151563523133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11128339146874101042348755 16692508720311151563523133)
            ·
              refine ⟨6259690770116681836321175, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16692508720311151563523133 6259690770116681836321175)
              ·
                refine ⟨9389536155175022754481763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6259690770116681836321175 9389536155175022754481763)
                ·
                  refine ⟨14084304232762534131722645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9389536155175022754481763 14084304232762534131722645)
                  ·
                    refine ⟨660201760910743787424499, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 14084304232762534131722645 660201760910743787424499)
                    ·
                      rfl

theorem cell23_3857215_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 1, 3, 1, 1, 6].length) (baseStart_3857215 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3857215 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3857215 prefixEnd_3857215 := by exact prefixLift 3857215
  have htrace : WordTrace (prefixWord ++ tailWord_3857215) baseStart_3857215 baseEnd_3857215 := by
    simpa [prefixWord, tailWord_3857215, baseEnd_3857215] using wordTrace_append hprefix tailTrace_3857215
  have hstable : (prefixWord ++ tailWord_3857215).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3857215).length < 2 ^ (prefixWord ++ tailWord_3857215).sum := by decide
  have hdescent : baseEnd_3857215 < baseStart_3857215 := by decide
  rcases family_descends (prefixWord ++ tailWord_3857215) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3857233 : List Nat := [1, 2, 2, 1, 7, 1, 1, 3, 1, 1, 3]
def baseStart_3857233 : Nat := 118140960795 + 3857233 * 2 ^ 59
def prefixEnd_3857233 : Nat := 4983230072969 + 3 ^ 40 * 3857233 * 2
def baseEnd_3857233 : Nat := 1980614525384012291848415

theorem tailTrace_3857233 : CollatzResearch.WordTrace tailWord_3857233 prefixEnd_3857233 1980614525384012291848415 := by
  unfold tailWord_3857233
  simp only [CollatzResearch.WordTrace]
  refine ⟨140684845234911078794712353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93789896823274052529808235 140684845234911078794712353)
  ·
    refine ⟨105513633926183309096034265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 140684845234911078794712353 105513633926183309096034265)
    ·
      refine ⟨79135225444637481822025699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 105513633926183309096034265 79135225444637481822025699)
      ·
        refine ⟨118702838166956222733038549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79135225444637481822025699 118702838166956222733038549)
        ·
          refine ⟨2782097769538036470305591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 118702838166956222733038549 2782097769538036470305591)
          ·
            refine ⟨4173146654307054705458387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2782097769538036470305591 4173146654307054705458387)
            ·
              refine ⟨6259719981460582058187581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4173146654307054705458387 6259719981460582058187581)
              ·
                refine ⟨2347394993047718271820343, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6259719981460582058187581 2347394993047718271820343)
                ·
                  refine ⟨3521092489571577407730515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2347394993047718271820343 3521092489571577407730515)
                  ·
                    refine ⟨5281638734357366111595773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3521092489571577407730515 5281638734357366111595773)
                    ·
                      refine ⟨1980614525384012291848415, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5281638734357366111595773 1980614525384012291848415)
                      ·
                        rfl

theorem cell23_3857233_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 7, 1, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 7, 1, 1, 3, 1, 1, 3].length) (baseStart_3857233 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3857233 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3857233 prefixEnd_3857233 := by exact prefixLift 3857233
  have htrace : WordTrace (prefixWord ++ tailWord_3857233) baseStart_3857233 baseEnd_3857233 := by
    simpa [prefixWord, tailWord_3857233, baseEnd_3857233] using wordTrace_append hprefix tailTrace_3857233
  have hstable : (prefixWord ++ tailWord_3857233).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3857233).length < 2 ^ (prefixWord ++ tailWord_3857233).sum := by decide
  have hdescent : baseEnd_3857233 < baseStart_3857233 := by decide
  rcases family_descends (prefixWord ++ tailWord_3857233) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3857242 : List Nat := [3, 1, 1, 2, 1, 4, 2, 3, 1, 2, 3]
def baseStart_3857242 : Nat := 118140960795 + 3857242 * 2 ^ 59
def prefixEnd_3857242 : Nat := 4983230072969 + 3 ^ 40 * 3857242 * 2
def baseEnd_3857242 : Nat := 1980619146709902756635873

theorem tailTrace_3857242 : CollatzResearch.WordTrace tailWord_3857242 prefixEnd_3857242 1980619146709902756635873 := by
  unfold tailWord_3857242
  simp only [CollatzResearch.WordTrace]
  refine ⟨35171293372969618332947495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 93790115661252315554526653 35171293372969618332947495)
  ·
    refine ⟨52756940059454427499421243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35171293372969618332947495 52756940059454427499421243)
    ·
      refine ⟨79135410089181641249131865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52756940059454427499421243 79135410089181641249131865)
      ·
        refine ⟨59351557566886230936848899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 79135410089181641249131865 59351557566886230936848899)
        ·
          refine ⟨89027336350329346405273349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59351557566886230936848899 89027336350329346405273349)
          ·
            refine ⟨16692625565686752450988753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 89027336350329346405273349 16692625565686752450988753)
            ·
              refine ⟨12519469174265064338241565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16692625565686752450988753 12519469174265064338241565)
              ·
                refine ⟨4694800940349399126840587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12519469174265064338241565 4694800940349399126840587)
                ·
                  refine ⟨7042201410524098690260881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4694800940349399126840587 7042201410524098690260881)
                  ·
                    refine ⟨5281651057893074017695661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7042201410524098690260881 5281651057893074017695661)
                    ·
                      refine ⟨1980619146709902756635873, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5281651057893074017695661 1980619146709902756635873)
                      ·
                        rfl

theorem cell23_3857242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 4, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 4, 2, 3, 1, 2, 3].length) (baseStart_3857242 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3857242 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3857242 prefixEnd_3857242 := by exact prefixLift 3857242
  have htrace : WordTrace (prefixWord ++ tailWord_3857242) baseStart_3857242 baseEnd_3857242 := by
    simpa [prefixWord, tailWord_3857242, baseEnd_3857242] using wordTrace_append hprefix tailTrace_3857242
  have hstable : (prefixWord ++ tailWord_3857242).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3857242).length < 2 ^ (prefixWord ++ tailWord_3857242).sum := by decide
  have hdescent : baseEnd_3857242 < baseStart_3857242 := by decide
  rcases family_descends (prefixWord ++ tailWord_3857242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3857256 : List Nat := [2, 1, 4, 2, 1, 4, 1, 1, 3, 2, 2]
def baseStart_3857256 : Nat := 118140960795 + 3857256 * 2 ^ 59
def prefixEnd_3857256 : Nat := 4983230072969 + 3 ^ 40 * 3857256 * 2
def baseEnd_3857256 : Nat := 1980626335439065701860809

theorem tailTrace_3857256 : CollatzResearch.WordTrace tailWord_3857256 prefixEnd_3857256 1980626335439065701860809 := by
  unfold tailWord_3857256
  simp only [CollatzResearch.WordTrace]
  refine ⟨70342842056913876861399811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93790456075885169148533081 70342842056913876861399811)
  ·
    refine ⟨105514263085370815292099717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70342842056913876861399811 105514263085370815292099717)
    ·
      refine ⟨19783924328507027867268697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 105514263085370815292099717 19783924328507027867268697)
      ·
        refine ⟨14837943246380270900451523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19783924328507027867268697 14837943246380270900451523)
        ·
          refine ⟨22256914869570406350677285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14837943246380270900451523 22256914869570406350677285)
          ·
            refine ⟨4173171538044451190751991, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 22256914869570406350677285 4173171538044451190751991)
            ·
              refine ⟨6259757307066676786127987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4173171538044451190751991 6259757307066676786127987)
              ·
                refine ⟨9389635960600015179191981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6259757307066676786127987 9389635960600015179191981)
                ·
                  refine ⟨3521113485225005692196993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9389635960600015179191981 3521113485225005692196993)
                  ·
                    refine ⟨2640835113918754269147745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3521113485225005692196993 2640835113918754269147745)
                    ·
                      refine ⟨1980626335439065701860809, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2640835113918754269147745 1980626335439065701860809)
                      ·
                        rfl

theorem cell23_3857256_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 4, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 4, 1, 1, 3, 2, 2].length) (baseStart_3857256 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3857256 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3857256 prefixEnd_3857256 := by exact prefixLift 3857256
  have htrace : WordTrace (prefixWord ++ tailWord_3857256) baseStart_3857256 baseEnd_3857256 := by
    simpa [prefixWord, tailWord_3857256, baseEnd_3857256] using wordTrace_append hprefix tailTrace_3857256
  have hstable : (prefixWord ++ tailWord_3857256).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3857256).length < 2 ^ (prefixWord ++ tailWord_3857256).sum := by decide
  have hdescent : baseEnd_3857256 < baseStart_3857256 := by decide
  rcases family_descends (prefixWord ++ tailWord_3857256) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3857262 : List Nat := [4, 1, 2, 3, 2, 1, 2, 8]
def baseStart_3857262 : Nat := 118140960795 + 3857262 * 2 ^ 59
def prefixEnd_3857262 : Nat := 4983230072969 + 3 ^ 40 * 3857262 * 2
def baseEnd_3857262 : Nat := 73356645048999728829103

theorem tailTrace_3857262 : CollatzResearch.WordTrace tailWord_3857262 prefixEnd_3857262 73356645048999728829103 := by
  unfold tailWord_3857262
  simp only [CollatzResearch.WordTrace]
  refine ⟨17585737868975752093439755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 93790601967870677831678693 17585737868975752093439755)
  ·
    refine ⟨26378606803463628140159633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17585737868975752093439755 26378606803463628140159633)
    ·
      refine ⟨19783955102597721105119725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26378606803463628140159633 19783955102597721105119725)
      ·
        refine ⟨7418983163474145414419897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19783955102597721105119725 7418983163474145414419897)
        ·
          refine ⟨5564237372605609060814923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7418983163474145414419897 5564237372605609060814923)
          ·
            refine ⟨8346356058908413591222385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5564237372605609060814923 8346356058908413591222385)
            ·
              refine ⟨6259767044181310193416789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8346356058908413591222385 6259767044181310193416789)
              ·
                refine ⟨73356645048999728829103, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 6259767044181310193416789 73356645048999728829103)
                ·
                  rfl

theorem cell23_3857262_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 2, 1, 2, 8].length) (baseStart_3857262 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3857262 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3857262 prefixEnd_3857262 := by exact prefixLift 3857262
  have htrace : WordTrace (prefixWord ++ tailWord_3857262) baseStart_3857262 baseEnd_3857262 := by
    simpa [prefixWord, tailWord_3857262, baseEnd_3857262] using wordTrace_append hprefix tailTrace_3857262
  have hstable : (prefixWord ++ tailWord_3857262).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3857262).length < 2 ^ (prefixWord ++ tailWord_3857262).sum := by decide
  have hdescent : baseEnd_3857262 < baseStart_3857262 := by decide
  rcases family_descends (prefixWord ++ tailWord_3857262) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3857306 : List Nat := [3, 1, 1, 4, 3, 1, 2, 2, 2, 1, 3]
def baseStart_3857306 : Nat := 118140960795 + 3857306 * 2 ^ 59
def prefixEnd_3857306 : Nat := 4983230072969 + 3 ^ 40 * 3857306 * 2
def baseEnd_3857306 : Nat := 1980652009471790506235579

theorem tailTrace_3857306 : CollatzResearch.WordTrace tailWord_3857306 prefixEnd_3857306 1980652009471790506235579 := by
  unfold tailWord_3857306
  simp only [CollatzResearch.WordTrace]
  refine ⟨35171876940911653065529943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 93791671842431074841413181 35171876940911653065529943)
  ·
    refine ⟨52757815411367479598294915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35171876940911653065529943 52757815411367479598294915)
    ·
      refine ⟨79136723117051219397442373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52757815411367479598294915 79136723117051219397442373)
      ·
        refine ⟨14838135584447103637020445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 79136723117051219397442373 14838135584447103637020445)
        ·
          refine ⟨5564300844167663863882667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14838135584447103637020445 5564300844167663863882667)
          ·
            refine ⟨8346451266251495795824001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5564300844167663863882667 8346451266251495795824001)
            ·
              refine ⟨6259838449688621846868001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8346451266251495795824001 6259838449688621846868001)
              ·
                refine ⟨4694878837266466385151001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6259838449688621846868001 4694878837266466385151001)
                ·
                  refine ⟨3521159127949849788863251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4694878837266466385151001 3521159127949849788863251)
                  ·
                    refine ⟨5281738691924774683294877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3521159127949849788863251 5281738691924774683294877)
                    ·
                      refine ⟨1980652009471790506235579, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5281738691924774683294877 1980652009471790506235579)
                      ·
                        rfl

theorem cell23_3857306_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 3, 1, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 3, 1, 2, 2, 2, 1, 3].length) (baseStart_3857306 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3857306 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3857306 prefixEnd_3857306 := by exact prefixLift 3857306
  have htrace : WordTrace (prefixWord ++ tailWord_3857306) baseStart_3857306 baseEnd_3857306 := by
    simpa [prefixWord, tailWord_3857306, baseEnd_3857306] using wordTrace_append hprefix tailTrace_3857306
  have hstable : (prefixWord ++ tailWord_3857306).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3857306).length < 2 ^ (prefixWord ++ tailWord_3857306).sum := by decide
  have hdescent : baseEnd_3857306 < baseStart_3857306 := by decide
  rcases family_descends (prefixWord ++ tailWord_3857306) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3857315 : List Nat := [1, 1, 1, 4, 1, 2, 3, 1, 2, 4, 3]
def baseStart_3857315 : Nat := 118140960795 + 3857315 * 2 ^ 59
def prefixEnd_3857315 : Nat := 4983230072969 + 3 ^ 40 * 3857315 * 2
def baseEnd_3857315 : Nat := 1980656630797680971023037

theorem tailTrace_3857315 : CollatzResearch.WordTrace tailWord_3857315 prefixEnd_3857315 1980656630797680971023037 := by
  unfold tailWord_3857315
  simp only [CollatzResearch.WordTrace]
  refine ⟨140687836020614006799197399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93791890680409337866131599 140687836020614006799197399)
  ·
    refine ⟨211031754030921010198796099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140687836020614006799197399 211031754030921010198796099)
    ·
      refine ⟨316547631046381515298194149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 211031754030921010198796099 316547631046381515298194149)
      ·
        refine ⟨59352680821196534118411403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 316547631046381515298194149 59352680821196534118411403)
        ·
          refine ⟨89029021231794801177617105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59352680821196534118411403 89029021231794801177617105)
          ·
            refine ⟨66771765923846100883212829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 89029021231794801177617105 66771765923846100883212829)
            ·
              refine ⟨25039412221442287831204811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 66771765923846100883212829 25039412221442287831204811)
              ·
                refine ⟨37559118332163431746807217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25039412221442287831204811 37559118332163431746807217)
                ·
                  refine ⟨28169338749122573810105413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 37559118332163431746807217 28169338749122573810105413)
                  ·
                    refine ⟨5281751015460482589394765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 28169338749122573810105413 5281751015460482589394765)
                    ·
                      refine ⟨1980656630797680971023037, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5281751015460482589394765 1980656630797680971023037)
                      ·
                        rfl

theorem cell23_3857315_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 3, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 3, 1, 2, 4, 3].length) (baseStart_3857315 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3857315 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3857315 prefixEnd_3857315 := by exact prefixLift 3857315
  have htrace : WordTrace (prefixWord ++ tailWord_3857315) baseStart_3857315 baseEnd_3857315 := by
    simpa [prefixWord, tailWord_3857315, baseEnd_3857315] using wordTrace_append hprefix tailTrace_3857315
  have hstable : (prefixWord ++ tailWord_3857315).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3857315).length < 2 ^ (prefixWord ++ tailWord_3857315).sum := by decide
  have hdescent : baseEnd_3857315 < baseStart_3857315 := by decide
  rcases family_descends (prefixWord ++ tailWord_3857315) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3857357 : List Nat := [1, 6, 3, 1, 1, 2, 1, 2, 2, 1, 3]
def baseStart_3857357 : Nat := 118140960795 + 3857357 * 2 ^ 59
def prefixEnd_3857357 : Nat := 4983230072969 + 3 ^ 40 * 3857357 * 2
def baseEnd_3857357 : Nat := 1980678196985169806697845

theorem tailTrace_3857357 : CollatzResearch.WordTrace tailWord_3857357 prefixEnd_3857357 1980678196985169806697845 := by
  unfold tailWord_3857357
  simp only [CollatzResearch.WordTrace]
  refine ⟨140689367886461847972226325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93792911924307898648150883 140689367886461847972226325)
  ·
    refine ⟨6594814119677899123698109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 140689367886461847972226325 6594814119677899123698109)
    ·
      refine ⟨2473055294879212171386791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6594814119677899123698109 2473055294879212171386791)
      ·
        refine ⟨3709582942318818257080187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2473055294879212171386791 3709582942318818257080187)
        ·
          refine ⟨5564374413478227385620281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3709582942318818257080187 5564374413478227385620281)
          ·
            refine ⟨4173280810108670539215211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5564374413478227385620281 4173280810108670539215211)
            ·
              refine ⟨6259921215163005808822817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4173280810108670539215211 6259921215163005808822817)
              ·
                refine ⟨4694940911372254356617113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6259921215163005808822817 4694940911372254356617113)
                ·
                  refine ⟨3521205683529190767462835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4694940911372254356617113 3521205683529190767462835)
                  ·
                    refine ⟨5281808525293786151194253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3521205683529190767462835 5281808525293786151194253)
                    ·
                      refine ⟨1980678196985169806697845, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5281808525293786151194253 1980678196985169806697845)
                      ·
                        rfl

theorem cell23_3857357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 3, 1, 1, 2, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 3, 1, 1, 2, 1, 2, 2, 1, 3].length) (baseStart_3857357 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3857357 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3857357 prefixEnd_3857357 := by exact prefixLift 3857357
  have htrace : WordTrace (prefixWord ++ tailWord_3857357) baseStart_3857357 baseEnd_3857357 := by
    simpa [prefixWord, tailWord_3857357, baseEnd_3857357] using wordTrace_append hprefix tailTrace_3857357
  have hstable : (prefixWord ++ tailWord_3857357).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3857357).length < 2 ^ (prefixWord ++ tailWord_3857357).sum := by decide
  have hdescent : baseEnd_3857357 < baseStart_3857357 := by decide
  rcases family_descends (prefixWord ++ tailWord_3857357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3857402 : List Nat := [3, 1, 1, 1, 1, 2, 1, 4, 1, 6, 2]
def baseStart_3857402 : Nat := 118140960795 + 3857402 * 2 ^ 59
def prefixEnd_3857402 : Nat := 4983230072969 + 3 ^ 40 * 3857402 * 2
def baseEnd_3857402 : Nat := 1980701303614622130635137

theorem tailTrace_3857402 : CollatzResearch.WordTrace tailWord_3857402 prefixEnd_3857402 1980701303614622130635137 := by
  unfold tailWord_3857402
  simp only [CollatzResearch.WordTrace]
  refine ⟨35172752292824705164403615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 93794006114199213771742973 35172752292824705164403615)
  ·
    refine ⟨52759128439237057746605423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35172752292824705164403615 52759128439237057746605423)
    ·
      refine ⟨79138692658855586619908135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52759128439237057746605423 79138692658855586619908135)
      ·
        refine ⟨118708038988283379929862203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79138692658855586619908135 118708038988283379929862203)
        ·
          refine ⟨178062058482425069894793305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 118708038988283379929862203 178062058482425069894793305)
          ·
            refine ⟨133546543861818802421094979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 178062058482425069894793305 133546543861818802421094979)
            ·
              refine ⟨200319815792728203631642469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 133546543861818802421094979 200319815792728203631642469)
              ·
                refine ⟨37559965461136538180932963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 200319815792728203631642469 37559965461136538180932963)
                ·
                  refine ⟨56339948191704807271399445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37559965461136538180932963 56339948191704807271399445)
                  ·
                    refine ⟨2640935071486162840846849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 56339948191704807271399445 2640935071486162840846849)
                    ·
                      refine ⟨1980701303614622130635137, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2640935071486162840846849 1980701303614622130635137)
                      ·
                        rfl

theorem cell23_3857402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 1, 4, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 1, 4, 1, 6, 2].length) (baseStart_3857402 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3857402 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3857402 prefixEnd_3857402 := by exact prefixLift 3857402
  have htrace : WordTrace (prefixWord ++ tailWord_3857402) baseStart_3857402 baseEnd_3857402 := by
    simpa [prefixWord, tailWord_3857402, baseEnd_3857402] using wordTrace_append hprefix tailTrace_3857402
  have hstable : (prefixWord ++ tailWord_3857402).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3857402).length < 2 ^ (prefixWord ++ tailWord_3857402).sum := by decide
  have hdescent : baseEnd_3857402 < baseStart_3857402 := by decide
  rcases family_descends (prefixWord ++ tailWord_3857402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3857405 : List Nat := [1, 4, 1, 1, 1, 2, 1, 2, 2, 3, 5]
def baseStart_3857405 : Nat := 118140960795 + 3857405 * 2 ^ 59
def prefixEnd_3857405 : Nat := 4983230072969 + 3 ^ 40 * 3857405 * 2
def baseEnd_3857405 : Nat := 1980702844056585618897623

theorem tailTrace_3857405 : CollatzResearch.WordTrace tailWord_3857405 prefixEnd_3857405 1980702844056585618897623 := by
  unfold tailWord_3857405
  simp only [CollatzResearch.WordTrace]
  refine ⟨140691118590287952169973669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93794079060191968113315779 140691118590287952169973669)
  ·
    refine ⟨26379584735678991031870063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 140691118590287952169973669 26379584735678991031870063)
    ·
      refine ⟨39569377103518486547805095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26379584735678991031870063 39569377103518486547805095)
      ·
        refine ⟨59354065655277729821707643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39569377103518486547805095 59354065655277729821707643)
        ·
          refine ⟨89031098482916594732561465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59354065655277729821707643 89031098482916594732561465)
          ·
            refine ⟨66773323862187446049421099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 89031098482916594732561465 66773323862187446049421099)
            ·
              refine ⟨100159985793281169074131649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 66773323862187446049421099 100159985793281169074131649)
              ·
                refine ⟨75119989344960876805598737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 100159985793281169074131649 75119989344960876805598737)
                ·
                  refine ⟨56339992008720657604199053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 75119989344960876805598737 56339992008720657604199053)
                  ·
                    refine ⟨21127497003270246601574645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 56339992008720657604199053 21127497003270246601574645)
                    ·
                      refine ⟨1980702844056585618897623, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 21127497003270246601574645 1980702844056585618897623)
                      ·
                        rfl

theorem cell23_3857405_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 1, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 1, 2, 2, 3, 5].length) (baseStart_3857405 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3857405 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3857405 prefixEnd_3857405 := by exact prefixLift 3857405
  have htrace : WordTrace (prefixWord ++ tailWord_3857405) baseStart_3857405 baseEnd_3857405 := by
    simpa [prefixWord, tailWord_3857405, baseEnd_3857405] using wordTrace_append hprefix tailTrace_3857405
  have hstable : (prefixWord ++ tailWord_3857405).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3857405).length < 2 ^ (prefixWord ++ tailWord_3857405).sum := by decide
  have hdescent : baseEnd_3857405 < baseStart_3857405 := by decide
  rcases family_descends (prefixWord ++ tailWord_3857405) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3857429 : List Nat := [1, 3, 2, 1, 4, 1, 3, 1, 3, 4]
def baseStart_3857429 : Nat := 118140960795 + 3857429 * 2 ^ 59
def prefixEnd_3857429 : Nat := 4983230072969 + 3 ^ 40 * 3857429 * 2
def baseEnd_3857429 : Nat := 660238389197431174999171

theorem tailTrace_3857429 : CollatzResearch.WordTrace tailWord_3857429 prefixEnd_3857429 660238389197431174999171 := by
  unfold tailWord_3857429
  simp only [CollatzResearch.WordTrace]
  refine ⟨140691993942201004268847341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93794662628134002845898227 140691993942201004268847341)
  ·
    refine ⟨52759497728325376600817753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 140691993942201004268847341 52759497728325376600817753)
    ·
      refine ⟨39569623296244032450613315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52759497728325376600817753 39569623296244032450613315)
      ·
        refine ⟨59354434944366048675919973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39569623296244032450613315 59354434944366048675919973)
        ·
          refine ⟨11128956552068634126734995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 59354434944366048675919973 11128956552068634126734995)
          ·
            refine ⟨16693434828102951190102493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11128956552068634126734995 16693434828102951190102493)
            ·
              refine ⟨6260038060538606696288435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16693434828102951190102493 6260038060538606696288435)
              ·
                refine ⟨9390057090807910044432653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6260038060538606696288435 9390057090807910044432653)
                ·
                  refine ⟨3521271409052966266662245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9390057090807910044432653 3521271409052966266662245)
                  ·
                    refine ⟨660238389197431174999171, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3521271409052966266662245 660238389197431174999171)
                    ·
                      rfl

theorem cell23_3857429_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 1, 3, 1, 3, 4].length) (baseStart_3857429 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3857429 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3857429 prefixEnd_3857429 := by exact prefixLift 3857429
  have htrace : WordTrace (prefixWord ++ tailWord_3857429) baseStart_3857429 baseEnd_3857429 := by
    simpa [prefixWord, tailWord_3857429, baseEnd_3857429] using wordTrace_append hprefix tailTrace_3857429
  have hstable : (prefixWord ++ tailWord_3857429).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3857429).length < 2 ^ (prefixWord ++ tailWord_3857429).sum := by decide
  have hdescent : baseEnd_3857429 < baseStart_3857429 := by decide
  rcases family_descends (prefixWord ++ tailWord_3857429) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3857509 : List Nat := [1, 3, 1, 3, 2, 1, 2, 4, 1, 1, 4]
def baseStart_3857509 : Nat := 118140960795 + 3857509 * 2 ^ 59
def prefixEnd_3857509 : Nat := 4983230072969 + 3 ^ 40 * 3857509 * 2
def baseEnd_3857509 : Nat := 1980756246044653211997145

theorem tailTrace_3857509 : CollatzResearch.WordTrace tailWord_3857509 prefixEnd_3857509 1980756246044653211997145 := by
  unfold tailWord_3857509
  simp only [CollatzResearch.WordTrace]
  refine ⟨140694911781911177931759581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93796607854607451954506387 140694911781911177931759581)
  ·
    refine ⟨52760591918216691724409843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 140694911781911177931759581 52760591918216691724409843)
    ·
      refine ⟨79140887877325037586614765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52760591918216691724409843 79140887877325037586614765)
      ·
        refine ⟨29677832953996889094980537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 79140887877325037586614765 29677832953996889094980537)
        ·
          refine ⟨22258374715497666821235403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29677832953996889094980537 22258374715497666821235403)
          ·
            refine ⟨33387562073246500231853105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22258374715497666821235403 33387562073246500231853105)
            ·
              refine ⟨25040671554934875173889829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33387562073246500231853105 25040671554934875173889829)
              ·
                refine ⟨4695125916550289095104343, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25040671554934875173889829 4695125916550289095104343)
                ·
                  refine ⟨7042688874825433642656515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4695125916550289095104343 7042688874825433642656515)
                  ·
                    refine ⟨10564033312238150463984773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7042688874825433642656515 10564033312238150463984773)
                    ·
                      refine ⟨1980756246044653211997145, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10564033312238150463984773 1980756246044653211997145)
                      ·
                        rfl

theorem cell23_3857509_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 2, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 2, 4, 1, 1, 4].length) (baseStart_3857509 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3857509 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3857509 prefixEnd_3857509 := by exact prefixLift 3857509
  have htrace : WordTrace (prefixWord ++ tailWord_3857509) baseStart_3857509 baseEnd_3857509 := by
    simpa [prefixWord, tailWord_3857509, baseEnd_3857509] using wordTrace_append hprefix tailTrace_3857509
  have hstable : (prefixWord ++ tailWord_3857509).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3857509).length < 2 ^ (prefixWord ++ tailWord_3857509).sum := by decide
  have hdescent : baseEnd_3857509 < baseStart_3857509 := by decide
  rcases family_descends (prefixWord ++ tailWord_3857509) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3857526 : List Nat := [5, 1, 1, 2, 1, 1, 3, 3, 1, 1, 4]
def baseStart_3857526 : Nat := 118140960795 + 3857526 * 2 ^ 59
def prefixEnd_3857526 : Nat := 4983230072969 + 3 ^ 40 * 3857526 * 2
def baseEnd_3857526 : Nat := 1980764975215779645484567

theorem tailTrace_3857526 : CollatzResearch.WordTrace tailWord_3857526 prefixEnd_3857526 1980764975215779645484567 := by
  unfold tailWord_3857526
  simp only [CollatzResearch.WordTrace]
  refine ⟨8793470738928099364695527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 93797021215233059890085621 8793470738928099364695527)
  ·
    refine ⟨13190206108392149047043291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8793470738928099364695527 13190206108392149047043291)
    ·
      refine ⟨19785309162588223570564937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13190206108392149047043291 19785309162588223570564937)
      ·
        refine ⟨14838981871941167677923703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19785309162588223570564937 14838981871941167677923703)
        ·
          refine ⟨22258472807911751516885555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14838981871941167677923703 22258472807911751516885555)
          ·
            refine ⟨33387709211867627275328333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22258472807911751516885555 33387709211867627275328333)
            ·
              refine ⟨12520390954450360228248125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33387709211867627275328333 12520390954450360228248125)
              ·
                refine ⟨4695146607918885085593047, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12520390954450360228248125 4695146607918885085593047)
                ·
                  refine ⟨7042719911878327628389571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4695146607918885085593047 7042719911878327628389571)
                  ·
                    refine ⟨10564079867817491442584357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7042719911878327628389571 10564079867817491442584357)
                    ·
                      refine ⟨1980764975215779645484567, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10564079867817491442584357 1980764975215779645484567)
                      ·
                        rfl

theorem cell23_3857526_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 3, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 3, 3, 1, 1, 4].length) (baseStart_3857526 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3857526 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3857526 prefixEnd_3857526 := by exact prefixLift 3857526
  have htrace : WordTrace (prefixWord ++ tailWord_3857526) baseStart_3857526 baseEnd_3857526 := by
    simpa [prefixWord, tailWord_3857526, baseEnd_3857526] using wordTrace_append hprefix tailTrace_3857526
  have hstable : (prefixWord ++ tailWord_3857526).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3857526).length < 2 ^ (prefixWord ++ tailWord_3857526).sum := by decide
  have hdescent : baseEnd_3857526 < baseStart_3857526 := by decide
  rcases family_descends (prefixWord ++ tailWord_3857526) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3857566 : List Nat := [4, 3, 1, 1, 2, 1, 4, 7]
def baseStart_3857566 : Nat := 118140960795 + 3857566 * 2 ^ 59
def prefixEnd_3857566 : Nat := 4983230072969 + 3 ^ 40 * 3857566 * 2
def baseEnd_3857566 : Nat := 73362426460813314406829

theorem tailTrace_3857566 : CollatzResearch.WordTrace tailWord_3857566 prefixEnd_3857566 73362426460813314406829 := by
  unfold tailWord_3857566
  simp only [CollatzResearch.WordTrace]
  refine ⟨17587123842838084583323069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 93797993828469784444389701 17587123842838084583323069)
  ·
    refine ⟨6595171441064281718746151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17587123842838084583323069 6595171441064281718746151)
    ·
      refine ⟨9892757161596422578119227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6595171441064281718746151 9892757161596422578119227)
      ·
        refine ⟨14839135742394633867178841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9892757161596422578119227 14839135742394633867178841)
        ·
          refine ⟨11129351806795975400384131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14839135742394633867178841 11129351806795975400384131)
          ·
            refine ⟨16694027710193963100576197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11129351806795975400384131 16694027710193963100576197)
            ·
              refine ⟨3130130195661368081358037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16694027710193963100576197 3130130195661368081358037)
              ·
                refine ⟨73362426460813314406829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3130130195661368081358037 73362426460813314406829)
                ·
                  rfl

theorem cell23_3857566_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 1, 4, 7].length) (baseStart_3857566 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3857566 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3857566 prefixEnd_3857566 := by exact prefixLift 3857566
  have htrace : WordTrace (prefixWord ++ tailWord_3857566) baseStart_3857566 baseEnd_3857566 := by
    simpa [prefixWord, tailWord_3857566, baseEnd_3857566] using wordTrace_append hprefix tailTrace_3857566
  have hstable : (prefixWord ++ tailWord_3857566).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3857566).length < 2 ^ (prefixWord ++ tailWord_3857566).sum := by decide
  have hdescent : baseEnd_3857566 < baseStart_3857566 := by decide
  rcases family_descends (prefixWord ++ tailWord_3857566) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3857592 : List Nat := [2, 1, 2, 1, 2, 1, 2, 4, 2, 6]
def baseStart_3857592 : Nat := 118140960795 + 3857592 * 2 ^ 59
def prefixEnd_3857592 : Nat := 4983230072969 + 3 ^ 40 * 3857592 * 2
def baseEnd_3857592 : Nat := 660266288312992129086421

theorem tailTrace_3857592 : CollatzResearch.WordTrace tailWord_3857592 prefixEnd_3857592 660266288312992129086421 := by
  unfold tailWord_3857592
  simp only [CollatzResearch.WordTrace]
  refine ⟨70348969520305241553515515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93798626027073655404687353 70348969520305241553515515)
  ·
    refine ⟨105523454280457862330273273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70348969520305241553515515 105523454280457862330273273)
    ·
      refine ⟨79142590710343396747704955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 105523454280457862330273273 79142590710343396747704955)
      ·
        refine ⟨118713886065515095121557433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79142590710343396747704955 118713886065515095121557433)
        ·
          refine ⟨89035414549136321341168075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 118713886065515095121557433 89035414549136321341168075)
          ·
            refine ⟨133553121823704482011752113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 89035414549136321341168075 133553121823704482011752113)
            ·
              refine ⟨100164841367778361508814085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 133553121823704482011752113 100164841367778361508814085)
              ·
                refine ⟨18780907756458442782902641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 100164841367778361508814085 18780907756458442782902641)
                ·
                  refine ⟨14085680817343832087176981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18780907756458442782902641 14085680817343832087176981)
                  ·
                    refine ⟨660266288312992129086421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 14085680817343832087176981 660266288312992129086421)
                    ·
                      rfl

theorem cell23_3857592_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 2, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 2, 4, 2, 6].length) (baseStart_3857592 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3857592 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3857592 prefixEnd_3857592 := by exact prefixLift 3857592
  have htrace : WordTrace (prefixWord ++ tailWord_3857592) baseStart_3857592 baseEnd_3857592 := by
    simpa [prefixWord, tailWord_3857592, baseEnd_3857592] using wordTrace_append hprefix tailTrace_3857592
  have hstable : (prefixWord ++ tailWord_3857592).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3857592).length < 2 ^ (prefixWord ++ tailWord_3857592).sum := by decide
  have hdescent : baseEnd_3857592 < baseStart_3857592 := by decide
  rcases family_descends (prefixWord ++ tailWord_3857592) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3857610 : List Nat := [3, 1, 2, 1, 3, 4, 2, 1, 2, 1, 3]
def baseStart_3857610 : Nat := 118140960795 + 3857610 * 2 ^ 59
def prefixEnd_3857610 : Nat := 4983230072969 + 3 ^ 40 * 3857610 * 2
def baseEnd_3857610 : Nat := 1980808107590757316834181

theorem tailTrace_3857610 : CollatzResearch.WordTrace tailWord_3857610 prefixEnd_3857610 1980808107590757316834181 := by
  unfold tailWord_3857610
  simp only [CollatzResearch.WordTrace]
  refine ⟨35174648888636318045296571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 93799063703030181454124189 35174648888636318045296571)
  ·
    refine ⟨52761973332954477067944857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35174648888636318045296571 52761973332954477067944857)
    ·
      refine ⟨39571479999715857800958643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52761973332954477067944857 39571479999715857800958643)
      ·
        refine ⟨59357219999573786701437965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39571479999715857800958643 59357219999573786701437965)
        ·
          refine ⟨22258957499840170013039237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 59357219999573786701437965 22258957499840170013039237)
          ·
            refine ⟨4173554531220031877444857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 22258957499840170013039237 4173554531220031877444857)
            ·
              refine ⟨3130165898415023908083643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4173554531220031877444857 3130165898415023908083643)
              ·
                refine ⟨4695248847622535862125465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3130165898415023908083643 4695248847622535862125465)
                ·
                  refine ⟨3521436635716901896594099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4695248847622535862125465 3521436635716901896594099)
                  ·
                    refine ⟨5282154953575352844891149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3521436635716901896594099 5282154953575352844891149)
                    ·
                      refine ⟨1980808107590757316834181, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5282154953575352844891149 1980808107590757316834181)
                      ·
                        rfl

theorem cell23_3857610_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 4, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 4, 2, 1, 2, 1, 3].length) (baseStart_3857610 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3857610 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3857610 prefixEnd_3857610 := by exact prefixLift 3857610
  have htrace : WordTrace (prefixWord ++ tailWord_3857610) baseStart_3857610 baseEnd_3857610 := by
    simpa [prefixWord, tailWord_3857610, baseEnd_3857610] using wordTrace_append hprefix tailTrace_3857610
  have hstable : (prefixWord ++ tailWord_3857610).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3857610).length < 2 ^ (prefixWord ++ tailWord_3857610).sum := by decide
  have hdescent : baseEnd_3857610 < baseStart_3857610 := by decide
  rcases family_descends (prefixWord ++ tailWord_3857610) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3857620 : List Nat := [2, 4, 1, 4, 1, 1, 1, 1, 3, 3, 2]
def baseStart_3857620 : Nat := 118140960795 + 3857620 * 2 ^ 59
def prefixEnd_3857620 : Nat := 4983230072969 + 3 ^ 40 * 3857620 * 2
def baseEnd_3857620 : Nat := 1980813242397302277709135

theorem tailTrace_3857620 : CollatzResearch.WordTrace tailWord_3857620 prefixEnd_3857620 1980813242397302277709135 := by
  unfold tailWord_3857620
  simp only [CollatzResearch.WordTrace]
  refine ⟨70349480142254521944525157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93799306856339362592700209 70349480142254521944525157)
  ·
    refine ⟨13190527526672722864598467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 70349480142254521944525157 13190527526672722864598467)
    ·
      refine ⟨19785791290009084296897701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13190527526672722864598467 19785791290009084296897701)
      ·
        refine ⟨3709835866876703305668319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 19785791290009084296897701 3709835866876703305668319)
        ·
          refine ⟨5564753800315054958502479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3709835866876703305668319 5564753800315054958502479)
          ·
            refine ⟨8347130700472582437753719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5564753800315054958502479 8347130700472582437753719)
            ·
              refine ⟨12520696050708873656630579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8347130700472582437753719 12520696050708873656630579)
              ·
                refine ⟨18781044076063310484945869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12520696050708873656630579 18781044076063310484945869)
                ·
                  refine ⟨7042891528523741431854701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18781044076063310484945869 7042891528523741431854701)
                  ·
                    refine ⟨2641084323196403036945513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7042891528523741431854701 2641084323196403036945513)
                    ·
                      refine ⟨1980813242397302277709135, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2641084323196403036945513 1980813242397302277709135)
                      ·
                        rfl

theorem cell23_3857620_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 4, 1, 1, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 4, 1, 1, 1, 1, 3, 3, 2].length) (baseStart_3857620 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3857620 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3857620 prefixEnd_3857620 := by exact prefixLift 3857620
  have htrace : WordTrace (prefixWord ++ tailWord_3857620) baseStart_3857620 baseEnd_3857620 := by
    simpa [prefixWord, tailWord_3857620, baseEnd_3857620] using wordTrace_append hprefix tailTrace_3857620
  have hstable : (prefixWord ++ tailWord_3857620).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3857620).length < 2 ^ (prefixWord ++ tailWord_3857620).sum := by decide
  have hdescent : baseEnd_3857620 < baseStart_3857620 := by decide
  rcases family_descends (prefixWord ++ tailWord_3857620) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3857649 : List Nat := [1, 2, 2, 2, 2, 1, 1, 4, 2, 3, 3]
def baseStart_3857649 : Nat := 118140960795 + 3857649 * 2 ^ 59
def prefixEnd_3857649 : Nat := 4983230072969 + 3 ^ 40 * 3857649 * 2
def baseEnd_3857649 : Nat := 1980828133336282664246501

theorem tailTrace_3857649 : CollatzResearch.WordTrace tailWord_3857649 prefixEnd_3857649 1980828133336282664246501 := by
  unfold tailWord_3857649
  simp only [CollatzResearch.WordTrace]
  refine ⟨140700018001403981841856001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93800012000935987894570667 140700018001403981841856001)
  ·
    refine ⟨105525013501052986381392001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 140700018001403981841856001 105525013501052986381392001)
    ·
      refine ⟨79143760125789739786044001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 105525013501052986381392001 79143760125789739786044001)
      ·
        refine ⟨59357820094342304839533001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 79143760125789739786044001 59357820094342304839533001)
        ·
          refine ⟨44518365070756728629649751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59357820094342304839533001 44518365070756728629649751)
          ·
            refine ⟨66777547606135092944474627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44518365070756728629649751 66777547606135092944474627)
            ·
              refine ⟨100166321409202639416711941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 66777547606135092944474627 100166321409202639416711941)
              ·
                refine ⟨18781185264225494890633489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 100166321409202639416711941 18781185264225494890633489)
                ·
                  refine ⟨14085888948169121167975117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18781185264225494890633489 14085888948169121167975117)
                  ·
                    refine ⟨5282208355563420437990669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14085888948169121167975117 5282208355563420437990669)
                    ·
                      refine ⟨1980828133336282664246501, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5282208355563420437990669 1980828133336282664246501)
                      ·
                        rfl

theorem cell23_3857649_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 1, 4, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 1, 4, 2, 3, 3].length) (baseStart_3857649 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3857649 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3857649 prefixEnd_3857649 := by exact prefixLift 3857649
  have htrace : WordTrace (prefixWord ++ tailWord_3857649) baseStart_3857649 baseEnd_3857649 := by
    simpa [prefixWord, tailWord_3857649, baseEnd_3857649] using wordTrace_append hprefix tailTrace_3857649
  have hstable : (prefixWord ++ tailWord_3857649).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3857649).length < 2 ^ (prefixWord ++ tailWord_3857649).sum := by decide
  have hdescent : baseEnd_3857649 < baseStart_3857649 := by decide
  rcases family_descends (prefixWord ++ tailWord_3857649) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3857726 : List Nat := [4, 2, 1, 2, 1, 1, 1, 1, 3, 4, 3]
def baseStart_3857726 : Nat := 118140960795 + 3857726 * 2 ^ 59
def prefixEnd_3857726 : Nat := 4983230072969 + 3 ^ 40 * 3857726 * 2
def baseEnd_3857726 : Nat := 1980867671346678862983647

theorem tailTrace_3857726 : CollatzResearch.WordTrace tailWord_3857726 prefixEnd_3857726 1980867671346678862983647 := by
  unfold tailWord_3857726
  simp only [CollatzResearch.WordTrace]
  refine ⟨17587853302765627999051129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 93801884281416682661606021 17587853302765627999051129)
  ·
    refine ⟨13190889977074220999288347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17587853302765627999051129 13190889977074220999288347)
    ·
      refine ⟨19786334965611331498932521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13190889977074220999288347 19786334965611331498932521)
      ·
        refine ⟨14839751224208498624199391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19786334965611331498932521 14839751224208498624199391)
        ·
          refine ⟨22259626836312747936299087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14839751224208498624199391 22259626836312747936299087)
          ·
            refine ⟨33389440254469121904448631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22259626836312747936299087 33389440254469121904448631)
            ·
              refine ⟨50084160381703682856672947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33389440254469121904448631 50084160381703682856672947)
              ·
                refine ⟨75126240572555524285009421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50084160381703682856672947 75126240572555524285009421)
                ·
                  refine ⟨28172340214708321606878533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 75126240572555524285009421 28172340214708321606878533)
                  ·
                    refine ⟨5282313790257810301289725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 28172340214708321606878533 5282313790257810301289725)
                    ·
                      refine ⟨1980867671346678862983647, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5282313790257810301289725 1980867671346678862983647)
                      ·
                        rfl

theorem cell23_3857726_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 1, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 1, 1, 3, 4, 3].length) (baseStart_3857726 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3857726 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3857726 prefixEnd_3857726 := by exact prefixLift 3857726
  have htrace : WordTrace (prefixWord ++ tailWord_3857726) baseStart_3857726 baseEnd_3857726 := by
    simpa [prefixWord, tailWord_3857726, baseEnd_3857726] using wordTrace_append hprefix tailTrace_3857726
  have hstable : (prefixWord ++ tailWord_3857726).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3857726).length < 2 ^ (prefixWord ++ tailWord_3857726).sum := by decide
  have hdescent : baseEnd_3857726 < baseStart_3857726 := by decide
  rcases family_descends (prefixWord ++ tailWord_3857726) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3857757 : List Nat := [1, 4, 5, 1, 1, 1, 1, 2, 2, 1, 4]
def baseStart_3857757 : Nat := 118140960795 + 3857757 * 2 ^ 59
def prefixEnd_3857757 : Nat := 4983230072969 + 3 ^ 40 * 3857757 * 2
def baseEnd_3857757 : Nat := 1980883589246968241696005

theorem tailTrace_3857757 : CollatzResearch.WordTrace tailWord_3857757 prefixEnd_3857757 1980883589246968241696005 := by
  unfold tailWord_3857757
  simp only [CollatzResearch.WordTrace]
  refine ⟨140703957085012716286787525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93802638056675144191191683 140703957085012716286787525)
  ·
    refine ⟨26381991953439884303772661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 140703957085012716286787525 26381991953439884303772661)
    ·
      refine ⟨2473311745634989153478687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 26381991953439884303772661 2473311745634989153478687)
      ·
        refine ⟨3709967618452483730218031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2473311745634989153478687 3709967618452483730218031)
        ·
          refine ⟨5564951427678725595327047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3709967618452483730218031 5564951427678725595327047)
          ·
            refine ⟨8347427141518088392990571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5564951427678725595327047 8347427141518088392990571)
            ·
              refine ⟨12521140712277132589485857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8347427141518088392990571 12521140712277132589485857)
              ·
                refine ⟨9390855534207849442114393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12521140712277132589485857 9390855534207849442114393)
                ·
                  refine ⟨7043141650655887081585795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9390855534207849442114393 7043141650655887081585795)
                  ·
                    refine ⟨10564712475983830622378693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7043141650655887081585795 10564712475983830622378693)
                    ·
                      refine ⟨1980883589246968241696005, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10564712475983830622378693 1980883589246968241696005)
                      ·
                        rfl

theorem cell23_3857757_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 5, 1, 1, 1, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 5, 1, 1, 1, 1, 2, 2, 1, 4].length) (baseStart_3857757 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3857757 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3857757 prefixEnd_3857757 := by exact prefixLift 3857757
  have htrace : WordTrace (prefixWord ++ tailWord_3857757) baseStart_3857757 baseEnd_3857757 := by
    simpa [prefixWord, tailWord_3857757, baseEnd_3857757] using wordTrace_append hprefix tailTrace_3857757
  have hstable : (prefixWord ++ tailWord_3857757).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3857757).length < 2 ^ (prefixWord ++ tailWord_3857757).sum := by decide
  have hdescent : baseEnd_3857757 < baseStart_3857757 := by decide
  rcases family_descends (prefixWord ++ tailWord_3857757) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3857759 : List Nat := [1, 1, 2, 3, 1, 2, 1, 2, 5, 5]
def baseStart_3857759 : Nat := 118140960795 + 3857759 * 2 ^ 59
def prefixEnd_3857759 : Nat := 4983230072969 + 3 ^ 40 * 3857759 * 2
def baseEnd_3857759 : Nat := 660294872069425744623665

theorem tailTrace_3857759 : CollatzResearch.WordTrace tailWord_3857759 prefixEnd_3857759 660294872069425744623665 := by
  unfold tailWord_3857759
  simp only [CollatzResearch.WordTrace]
  refine ⟨140704030031005470628360331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93802686687336980418906887 140704030031005470628360331)
  ·
    refine ⟨211056045046508205942540497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140704030031005470628360331 211056045046508205942540497)
    ·
      refine ⟨158292033784881154456905373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 211056045046508205942540497 158292033784881154456905373)
      ·
        refine ⟨59359512669330432921339515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 158292033784881154456905373 59359512669330432921339515)
        ·
          refine ⟨89039269003995649382009273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59359512669330432921339515 89039269003995649382009273)
          ·
            refine ⟨66779451752996737036506955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 89039269003995649382009273 66779451752996737036506955)
            ·
              refine ⟨100169177629495105554760433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 66779451752996737036506955 100169177629495105554760433)
              ·
                refine ⟨75126883222121329166070325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 100169177629495105554760433 75126883222121329166070325)
                ·
                  refine ⟨7043145302073874609319093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 75126883222121329166070325 7043145302073874609319093)
                  ·
                    refine ⟨660294872069425744623665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7043145302073874609319093 660294872069425744623665)
                    ·
                      rfl

theorem cell23_3857759_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 1, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 1, 2, 5, 5].length) (baseStart_3857759 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3857759 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3857759 prefixEnd_3857759 := by exact prefixLift 3857759
  have htrace : WordTrace (prefixWord ++ tailWord_3857759) baseStart_3857759 baseEnd_3857759 := by
    simpa [prefixWord, tailWord_3857759, baseEnd_3857759] using wordTrace_append hprefix tailTrace_3857759
  have hstable : (prefixWord ++ tailWord_3857759).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3857759).length < 2 ^ (prefixWord ++ tailWord_3857759).sum := by decide
  have hdescent : baseEnd_3857759 < baseStart_3857759 := by decide
  rcases family_descends (prefixWord ++ tailWord_3857759) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3857767 : List Nat := [1, 1, 5, 1, 4, 1, 3, 2, 1, 4]
def baseStart_3857767 : Nat := 118140960795 + 3857767 * 2 ^ 59
def prefixEnd_3857767 : Nat := 4983230072969 + 3 ^ 40 * 3857767 * 2
def baseEnd_3857767 : Nat := 660296241351171067523653

theorem tailTrace_3857767 : CollatzResearch.WordTrace tailWord_3857767 prefixEnd_3857767 660296241351171067523653 := by
  unfold tailWord_3857767
  simp only [CollatzResearch.WordTrace]
  refine ⟨140704321814976487994651555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93802881209984325329767703 140704321814976487994651555)
  ·
    refine ⟨211056482722464731991977333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140704321814976487994651555 211056482722464731991977333)
    ·
      refine ⟨19786545255231068624247875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 211056482722464731991977333 19786545255231068624247875)
      ·
        refine ⟨29679817882846602936371813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19786545255231068624247875 29679817882846602936371813)
        ·
          refine ⟨5564965853033738050569715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 29679817882846602936371813 5564965853033738050569715)
          ·
            refine ⟨8347448779550607075854573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5564965853033738050569715 8347448779550607075854573)
            ·
              refine ⟨3130293292331477653445465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8347448779550607075854573 3130293292331477653445465)
              ·
                refine ⟨2347719969248608240084099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3130293292331477653445465 2347719969248608240084099)
                ·
                  refine ⟨3521579953872912360126149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2347719969248608240084099 3521579953872912360126149)
                  ·
                    refine ⟨660296241351171067523653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3521579953872912360126149 660296241351171067523653)
                    ·
                      rfl

theorem cell23_3857767_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 4, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 4, 1, 3, 2, 1, 4].length) (baseStart_3857767 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3857767 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3857767 prefixEnd_3857767 := by exact prefixLift 3857767
  have htrace : WordTrace (prefixWord ++ tailWord_3857767) baseStart_3857767 baseEnd_3857767 := by
    simpa [prefixWord, tailWord_3857767, baseEnd_3857767] using wordTrace_append hprefix tailTrace_3857767
  have hstable : (prefixWord ++ tailWord_3857767).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3857767).length < 2 ^ (prefixWord ++ tailWord_3857767).sum := by decide
  have hdescent : baseEnd_3857767 < baseStart_3857767 := by decide
  rcases family_descends (prefixWord ++ tailWord_3857767) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3857793 : List Nat := [1, 2, 4, 3, 2, 1, 1, 1, 3, 5]
def baseStart_3857793 : Nat := 118140960795 + 3857793 * 2 ^ 59
def prefixEnd_3857793 : Nat := 4983230072969 + 3 ^ 40 * 3857793 * 2
def baseEnd_3857793 : Nat := 660300691516843366948613

theorem tailTrace_3857793 : CollatzResearch.WordTrace tailWord_3857793 prefixEnd_3857793 660300691516843366948613 := by
  unfold tailWord_3857793
  simp only [CollatzResearch.WordTrace]
  refine ⟨140705270112882294435098033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93803513408588196290065355 140705270112882294435098033)
  ·
    refine ⟨105528952584661720826323525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 140705270112882294435098033 105528952584661720826323525)
    ·
      refine ⟨19786678609624072654935661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 105528952584661720826323525 19786678609624072654935661)
      ·
        refine ⟨7420004478609027245600873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19786678609624072654935661 7420004478609027245600873)
        ·
          refine ⟨5565003358956770434200655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7420004478609027245600873 5565003358956770434200655)
          ·
            refine ⟨8347505038435155651300983, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5565003358956770434200655 8347505038435155651300983)
            ·
              refine ⟨12521257557652733476951475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8347505038435155651300983 12521257557652733476951475)
              ·
                refine ⟨18781886336479100215427213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12521257557652733476951475 18781886336479100215427213)
                ·
                  refine ⟨7043207376179662580785205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18781886336479100215427213 7043207376179662580785205)
                  ·
                    refine ⟨660300691516843366948613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7043207376179662580785205 660300691516843366948613)
                    ·
                      rfl

theorem cell23_3857793_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 2, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 2, 1, 1, 1, 3, 5].length) (baseStart_3857793 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3857793 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3857793 prefixEnd_3857793 := by exact prefixLift 3857793
  have htrace : WordTrace (prefixWord ++ tailWord_3857793) baseStart_3857793 baseEnd_3857793 := by
    simpa [prefixWord, tailWord_3857793, baseEnd_3857793] using wordTrace_append hprefix tailTrace_3857793
  have hstable : (prefixWord ++ tailWord_3857793).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3857793).length < 2 ^ (prefixWord ++ tailWord_3857793).sum := by decide
  have hdescent : baseEnd_3857793 < baseStart_3857793 := by decide
  rcases family_descends (prefixWord ++ tailWord_3857793) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3857800 : List Nat := [2, 1, 3, 3, 1, 3, 2, 1, 2, 3, 2]
def baseStart_3857800 : Nat := 118140960795 + 3857800 * 2 ^ 59
def prefixEnd_3857800 : Nat := 4983230072969 + 3 ^ 40 * 3857800 * 2
def baseEnd_3857800 : Nat := 1980905668915111573458307

theorem tailTrace_3857800 : CollatzResearch.WordTrace tailWord_3857800 prefixEnd_3857800 1980905668915111573458307 := by
  unfold tailWord_3857800
  simp only [CollatzResearch.WordTrace]
  refine ⟨70352762711928467315301427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93803683615904623087068569 70352762711928467315301427)
  ·
    refine ⟨105529144067892700972952141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70352762711928467315301427 105529144067892700972952141)
    ·
      refine ⟨39573429025459762864857053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 105529144067892700972952141 39573429025459762864857053)
      ·
        refine ⟨14840035884547411074321395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 39573429025459762864857053 14840035884547411074321395)
        ·
          refine ⟨22260053826821116611482093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14840035884547411074321395 22260053826821116611482093)
          ·
            refine ⟨8347520185057918729305785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22260053826821116611482093 8347520185057918729305785)
            ·
              refine ⟨6260640138793439046979339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8347520185057918729305785 6260640138793439046979339)
              ·
                refine ⟨9390960208190158570469009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6260640138793439046979339 9390960208190158570469009)
                ·
                  refine ⟨7043220156142618927851757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9390960208190158570469009 7043220156142618927851757)
                  ·
                    refine ⟨2641207558553482097944409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7043220156142618927851757 2641207558553482097944409)
                    ·
                      refine ⟨1980905668915111573458307, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2641207558553482097944409 1980905668915111573458307)
                      ·
                        rfl

theorem cell23_3857800_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 3, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 3, 2, 1, 2, 3, 2].length) (baseStart_3857800 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3857800 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3857800 prefixEnd_3857800 := by exact prefixLift 3857800
  have htrace : WordTrace (prefixWord ++ tailWord_3857800) baseStart_3857800 baseEnd_3857800 := by
    simpa [prefixWord, tailWord_3857800, baseEnd_3857800] using wordTrace_append hprefix tailTrace_3857800
  have hstable : (prefixWord ++ tailWord_3857800).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3857800).length < 2 ^ (prefixWord ++ tailWord_3857800).sum := by decide
  have hdescent : baseEnd_3857800 < baseStart_3857800 := by decide
  rcases family_descends (prefixWord ++ tailWord_3857800) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3857823 : List Nat := [1, 1, 2, 5, 1, 2, 1, 4, 2, 4]
def baseStart_3857823 : Nat := 118140960795 + 3857823 * 2 ^ 59
def prefixEnd_3857823 : Nat := 4983230072969 + 3 ^ 40 * 3857823 * 2
def baseEnd_3857823 : Nat := 660305826323388327823567

theorem tailTrace_3857823 : CollatzResearch.WordTrace tailWord_3857823 prefixEnd_3857823 660305826323388327823567 := by
  unfold tailWord_3857823
  simp only [CollatzResearch.WordTrace]
  refine ⟨140706364302773609558690123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93804242868515739705793415 140706364302773609558690123)
  ·
    refine ⟨211059546454160414338035185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140706364302773609558690123 211059546454160414338035185)
    ·
      refine ⟨158294659840620310753526389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 211059546454160414338035185 158294659840620310753526389)
      ·
        refine ⟨14840124360058154133143099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 158294659840620310753526389 14840124360058154133143099)
        ·
          refine ⟨22260186540087231199714649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14840124360058154133143099 22260186540087231199714649)
          ·
            refine ⟨16695139905065423399785987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22260186540087231199714649 16695139905065423399785987)
            ·
              refine ⟨25042709857598135099678981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16695139905065423399785987 25042709857598135099678981)
              ·
                refine ⟨4695508098299650331189809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25042709857598135099678981 4695508098299650331189809)
                ·
                  refine ⟨3521631073724737748392357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4695508098299650331189809 3521631073724737748392357)
                  ·
                    refine ⟨660305826323388327823567, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3521631073724737748392357 660305826323388327823567)
                    ·
                      rfl

theorem cell23_3857823_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 2, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 2, 1, 4, 2, 4].length) (baseStart_3857823 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3857823 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3857823 prefixEnd_3857823 := by exact prefixLift 3857823
  have htrace : WordTrace (prefixWord ++ tailWord_3857823) baseStart_3857823 baseEnd_3857823 := by
    simpa [prefixWord, tailWord_3857823, baseEnd_3857823] using wordTrace_append hprefix tailTrace_3857823
  have hstable : (prefixWord ++ tailWord_3857823).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3857823).length < 2 ^ (prefixWord ++ tailWord_3857823).sum := by decide
  have hdescent : baseEnd_3857823 < baseStart_3857823 := by decide
  rcases family_descends (prefixWord ++ tailWord_3857823) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3857829 : List Nat := [1, 3, 1, 2, 1, 1, 2, 1, 2, 2, 7]
def baseStart_3857829 : Nat := 118140960795 + 3857829 * 2 ^ 59
def prefixEnd_3857829 : Nat := 4983230072969 + 3 ^ 40 * 3857829 * 2
def baseEnd_3857829 : Nat := 1980920559854091959995673

theorem tailTrace_3857829 : CollatzResearch.WordTrace tailWord_3857829 prefixEnd_3857829 1980920559854091959995673 := by
  unfold tailWord_3857829
  simp only [CollatzResearch.WordTrace]
  refine ⟨140706583140751872583408541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93804388760501248388939027 140706583140751872583408541)
  ·
    refine ⟨52764968677781952218778203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 140706583140751872583408541 52764968677781952218778203)
    ·
      refine ⟨79147453016672928328167305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52764968677781952218778203 79147453016672928328167305)
      ·
        refine ⟨59360589762504696246125479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 79147453016672928328167305 59360589762504696246125479)
        ·
          refine ⟨89040884643757044369188219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59360589762504696246125479 89040884643757044369188219)
          ·
            refine ⟨133561326965635566553782329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 89040884643757044369188219 133561326965635566553782329)
            ·
              refine ⟨100170995224226674915336747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 133561326965635566553782329 100170995224226674915336747)
              ·
                refine ⟨150256492836340012373005121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 100170995224226674915336747 150256492836340012373005121)
                ·
                  refine ⟨112692369627255009279753841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 150256492836340012373005121 112692369627255009279753841)
                  ·
                    refine ⟨84519277220441256959815381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 112692369627255009279753841 84519277220441256959815381)
                    ·
                      refine ⟨1980920559854091959995673, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 84519277220441256959815381 1980920559854091959995673)
                      ·
                        rfl

theorem cell23_3857829_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 2, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 2, 1, 2, 2, 7].length) (baseStart_3857829 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3857829 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3857829 prefixEnd_3857829 := by exact prefixLift 3857829
  have htrace : WordTrace (prefixWord ++ tailWord_3857829) baseStart_3857829 baseEnd_3857829 := by
    simpa [prefixWord, tailWord_3857829, baseEnd_3857829] using wordTrace_append hprefix tailTrace_3857829
  have hstable : (prefixWord ++ tailWord_3857829).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3857829).length < 2 ^ (prefixWord ++ tailWord_3857829).sum := by decide
  have hdescent : baseEnd_3857829 < baseStart_3857829 := by decide
  rcases family_descends (prefixWord ++ tailWord_3857829) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3857839 : List Nat := [1, 1, 2, 1, 2, 2, 1, 3, 2, 2, 6]
def baseStart_3857839 : Nat := 118140960795 + 3857839 * 2 ^ 59
def prefixEnd_3857839 : Nat := 4983230072969 + 3 ^ 40 * 3857839 * 2
def baseEnd_3857839 : Nat := 1980925694660636920870627

theorem tailTrace_3857839 : CollatzResearch.WordTrace tailWord_3857839 prefixEnd_3857839 1980925694660636920870627 := by
  unfold tailWord_3857839
  simp only [CollatzResearch.WordTrace]
  refine ⟨140706947870715644291272571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93804631913810429527515047 140706947870715644291272571)
  ·
    refine ⟨211060421806073466436908857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140706947870715644291272571 211060421806073466436908857)
    ·
      refine ⟨158295316354555099827681643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 211060421806073466436908857 158295316354555099827681643)
      ·
        refine ⟨237442974531832649741522465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 158295316354555099827681643 237442974531832649741522465)
        ·
          refine ⟨178082230898874487306141849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 237442974531832649741522465 178082230898874487306141849)
          ·
            refine ⟨133561673174155865479606387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 178082230898874487306141849 133561673174155865479606387)
            ·
              refine ⟨200342509761233798219409581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 133561673174155865479606387 200342509761233798219409581)
              ·
                refine ⟨75128441160462674332278593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 200342509761233798219409581 75128441160462674332278593)
                ·
                  refine ⟨56346330870347005749208945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 75128441160462674332278593 56346330870347005749208945)
                  ·
                    refine ⟨42259748152760254311906709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 56346330870347005749208945 42259748152760254311906709)
                    ·
                      refine ⟨1980925694660636920870627, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 42259748152760254311906709 1980925694660636920870627)
                      ·
                        rfl

theorem cell23_3857839_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 1, 3, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 1, 3, 2, 2, 6].length) (baseStart_3857839 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3857839 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3857839 prefixEnd_3857839 := by exact prefixLift 3857839
  have htrace : WordTrace (prefixWord ++ tailWord_3857839) baseStart_3857839 baseEnd_3857839 := by
    simpa [prefixWord, tailWord_3857839, baseEnd_3857839] using wordTrace_append hprefix tailTrace_3857839
  have hstable : (prefixWord ++ tailWord_3857839).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3857839).length < 2 ^ (prefixWord ++ tailWord_3857839).sum := by decide
  have hdescent : baseEnd_3857839 < baseStart_3857839 := by decide
  rcases family_descends (prefixWord ++ tailWord_3857839) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3857863 : List Nat := [1, 1, 4, 1, 1, 3, 2, 2, 4, 1, 3]
def baseStart_3857863 : Nat := 118140960795 + 3857863 * 2 ^ 59
def prefixEnd_3857863 : Nat := 4983230072969 + 3 ^ 40 * 3857863 * 2
def baseEnd_3857863 : Nat := 1980938018196344826970517

theorem tailTrace_3857863 : CollatzResearch.WordTrace tailWord_3857863 prefixEnd_3857863 1980938018196344826970517 := by
  unfold tailWord_3857863
  simp only [CollatzResearch.WordTrace]
  refine ⟨140707823222628696390146243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93805215481752464260097495 140707823222628696390146243)
  ·
    refine ⟨211061734833943044585219365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140707823222628696390146243 211061734833943044585219365)
    ·
      refine ⟨39574075281364320859728631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 211061734833943044585219365 39574075281364320859728631)
      ·
        refine ⟨59361112922046481289592947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39574075281364320859728631 59361112922046481289592947)
        ·
          refine ⟨89041669383069721934389421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59361112922046481289592947 89041669383069721934389421)
          ·
            refine ⟨33390626018651145725396033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 89041669383069721934389421 33390626018651145725396033)
            ·
              refine ⟨25042969513988359294047025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33390626018651145725396033 25042969513988359294047025)
              ·
                refine ⟨18782227135491269470535269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25042969513988359294047025 18782227135491269470535269)
                ·
                  refine ⟨3521667587904613025725363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 18782227135491269470535269 3521667587904613025725363)
                  ·
                    refine ⟨5282501381856919538588045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3521667587904613025725363 5282501381856919538588045)
                    ·
                      refine ⟨1980938018196344826970517, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5282501381856919538588045 1980938018196344826970517)
                      ·
                        rfl

theorem cell23_3857863_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 2, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 2, 2, 4, 1, 3].length) (baseStart_3857863 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3857863 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3857863 prefixEnd_3857863 := by exact prefixLift 3857863
  have htrace : WordTrace (prefixWord ++ tailWord_3857863) baseStart_3857863 baseEnd_3857863 := by
    simpa [prefixWord, tailWord_3857863, baseEnd_3857863] using wordTrace_append hprefix tailTrace_3857863
  have hstable : (prefixWord ++ tailWord_3857863).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3857863).length < 2 ^ (prefixWord ++ tailWord_3857863).sum := by decide
  have hdescent : baseEnd_3857863 < baseStart_3857863 := by decide
  rcases family_descends (prefixWord ++ tailWord_3857863) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3857880 : List Nat := [2, 1, 2, 2, 2, 1, 5, 2, 2, 1, 3]
def baseStart_3857880 : Nat := 118140960795 + 3857880 * 2 ^ 59
def prefixEnd_3857880 : Nat := 4983230072969 + 3 ^ 40 * 3857880 * 2
def baseEnd_3857880 : Nat := 1980946747367471260457939

theorem tailTrace_3857880 : CollatzResearch.WordTrace tailWord_3857880 prefixEnd_3857880 1980946747367471260457939 := by
  unfold tailWord_3857880
  simp only [CollatzResearch.WordTrace]
  refine ⟨70354221631783554146757547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93805628842378072195676729 70354221631783554146757547)
  ·
    refine ⟨105531332447675331220136321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70354221631783554146757547 105531332447675331220136321)
    ·
      refine ⟨79148499335756498415102241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 105531332447675331220136321 79148499335756498415102241)
      ·
        refine ⟨59361374501817373811326681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 79148499335756498415102241 59361374501817373811326681)
        ·
          refine ⟨44521030876363030358495011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59361374501817373811326681 44521030876363030358495011)
          ·
            refine ⟨66781546314544545537742517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44521030876363030358495011 66781546314544545537742517)
            ·
              refine ⟨6260769966988551144163361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 66781546314544545537742517 6260769966988551144163361)
              ·
                refine ⟨4695577475241413358122521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6260769966988551144163361 4695577475241413358122521)
                ·
                  refine ⟨3521683106431060018591891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4695577475241413358122521 3521683106431060018591891)
                  ·
                    refine ⟨5282524659646590027887837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3521683106431060018591891 5282524659646590027887837)
                    ·
                      refine ⟨1980946747367471260457939, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5282524659646590027887837 1980946747367471260457939)
                      ·
                        rfl

theorem cell23_3857880_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 5, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 5, 2, 2, 1, 3].length) (baseStart_3857880 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3857880 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3857880 prefixEnd_3857880 := by exact prefixLift 3857880
  have htrace : WordTrace (prefixWord ++ tailWord_3857880) baseStart_3857880 baseEnd_3857880 := by
    simpa [prefixWord, tailWord_3857880, baseEnd_3857880] using wordTrace_append hprefix tailTrace_3857880
  have hstable : (prefixWord ++ tailWord_3857880).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3857880).length < 2 ^ (prefixWord ++ tailWord_3857880).sum := by decide
  have hdescent : baseEnd_3857880 < baseStart_3857880 := by decide
  rcases family_descends (prefixWord ++ tailWord_3857880) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3857896 : List Nat := [2, 1, 4, 1, 1, 2, 1, 3, 2, 6]
def baseStart_3857896 : Nat := 118140960795 + 3857896 * 2 ^ 59
def prefixEnd_3857896 : Nat := 4983230072969 + 3 ^ 40 * 3857896 * 2
def baseEnd_3857896 : Nat := 660318321019314399285955

theorem tailTrace_3857896 : CollatzResearch.WordTrace tailWord_3857896 prefixEnd_3857896 660318321019314399285955 := by
  unfold tailWord_3857896
  simp only [CollatzResearch.WordTrace]
  refine ⟨70354513415754571513048771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93806017887672762017398361 70354513415754571513048771)
  ·
    refine ⟨105531770123631857269573157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70354513415754571513048771 105531770123631857269573157)
    ·
      refine ⟨19787206898180973238044967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 105531770123631857269573157 19787206898180973238044967)
      ·
        refine ⟨29680810347271459857067451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19787206898180973238044967 29680810347271459857067451)
        ·
          refine ⟨44521215520907189785601177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29680810347271459857067451 44521215520907189785601177)
          ·
            refine ⟨33390911640680392339200883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44521215520907189785601177 33390911640680392339200883)
            ·
              refine ⟨50086367461020588508801325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33390911640680392339200883 50086367461020588508801325)
              ·
                refine ⟨18782387797882720690800497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 50086367461020588508801325 18782387797882720690800497)
                ·
                  refine ⟨14086790848412040518100373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18782387797882720690800497 14086790848412040518100373)
                  ·
                    refine ⟨660318321019314399285955, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 14086790848412040518100373 660318321019314399285955)
                    ·
                      rfl

theorem cell23_3857896_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 1, 3, 2, 6].length) (baseStart_3857896 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3857896 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3857896 prefixEnd_3857896 := by exact prefixLift 3857896
  have htrace : WordTrace (prefixWord ++ tailWord_3857896) baseStart_3857896 baseEnd_3857896 := by
    simpa [prefixWord, tailWord_3857896, baseEnd_3857896] using wordTrace_append hprefix tailTrace_3857896
  have hstable : (prefixWord ++ tailWord_3857896).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3857896).length < 2 ^ (prefixWord ++ tailWord_3857896).sum := by decide
  have hdescent : baseEnd_3857896 < baseStart_3857896 := by decide
  rcases family_descends (prefixWord ++ tailWord_3857896) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3857916 : List Nat := [2, 2, 2, 1, 2, 1, 2, 2, 1, 4, 4]
def baseStart_3857916 : Nat := 118140960795 + 3857916 * 2 ^ 59
def prefixEnd_3857916 : Nat := 4983230072969 + 3 ^ 40 * 3857916 * 2
def baseEnd_3857916 : Nat := 1980965232671033119607773

theorem tailTrace_3857916 : CollatzResearch.WordTrace tailWord_3857916 prefixEnd_3857916 1980965232671033119607773 := by
  unfold tailWord_3857916
  simp only [CollatzResearch.WordTrace]
  refine ⟨70354878145718343220912801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93806504194291124294550401 70354878145718343220912801)
  ·
    refine ⟨52766158609288757415684601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70354878145718343220912801 52766158609288757415684601)
    ·
      refine ⟨39574618956966568061763451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52766158609288757415684601 39574618956966568061763451)
      ·
        refine ⟨59361928435449852092645177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39574618956966568061763451 59361928435449852092645177)
        ·
          refine ⟨44521446326587389069483883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59361928435449852092645177 44521446326587389069483883)
          ·
            refine ⟨66782169489881083604225825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44521446326587389069483883 66782169489881083604225825)
            ·
              refine ⟨50086627117410812703169369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 66782169489881083604225825 50086627117410812703169369)
              ·
                refine ⟨37564970338058109527377027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 50086627117410812703169369 37564970338058109527377027)
                ·
                  refine ⟨56347455507087164291065541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37564970338058109527377027 56347455507087164291065541)
                  ·
                    refine ⟨10565147907578843304574789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 56347455507087164291065541 10565147907578843304574789)
                    ·
                      refine ⟨1980965232671033119607773, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10565147907578843304574789 1980965232671033119607773)
                      ·
                        rfl

theorem cell23_3857916_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 2, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 2, 2, 1, 4, 4].length) (baseStart_3857916 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3857916 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3857916 prefixEnd_3857916 := by exact prefixLift 3857916
  have htrace : WordTrace (prefixWord ++ tailWord_3857916) baseStart_3857916 baseEnd_3857916 := by
    simpa [prefixWord, tailWord_3857916, baseEnd_3857916] using wordTrace_append hprefix tailTrace_3857916
  have hstable : (prefixWord ++ tailWord_3857916).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3857916).length < 2 ^ (prefixWord ++ tailWord_3857916).sum := by decide
  have hdescent : baseEnd_3857916 < baseStart_3857916 := by decide
  rcases family_descends (prefixWord ++ tailWord_3857916) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3857954 : List Nat := [3, 3, 1, 1, 1, 1, 6, 1, 2, 2, 2]
def baseStart_3857954 : Nat := 118140960795 + 3857954 * 2 ^ 59
def prefixEnd_3857954 : Nat := 4983230072969 + 3 ^ 40 * 3857954 * 2
def baseEnd_3857954 : Nat := 1980984744935903970932599

theorem tailTrace_3857954 : CollatzResearch.WordTrace tailWord_3857954 prefixEnd_3857954 1980984744935903970932599 := by
  unfold tailWord_3857954
  simp only [CollatzResearch.WordTrace]
  refine ⟨35177785566324754732927229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 93807428176866012621139277 35177785566324754732927229)
  ·
    refine ⟨13191669587371783024847711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 35177785566324754732927229 13191669587371783024847711)
    ·
      refine ⟨19787504381057674537271567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13191669587371783024847711 19787504381057674537271567)
      ·
        refine ⟨29681256571586511805907351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19787504381057674537271567 29681256571586511805907351)
        ·
          refine ⟨44521884857379767708861027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29681256571586511805907351 44521884857379767708861027)
          ·
            refine ⟨66782827286069651563291541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44521884857379767708861027 66782827286069651563291541)
            ·
              refine ⟨3130445029034514917029291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 66782827286069651563291541 3130445029034514917029291)
              ·
                refine ⟨4695667543551772375543937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3130445029034514917029291 4695667543551772375543937)
                ·
                  refine ⟨3521750657663829281657953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4695667543551772375543937 3521750657663829281657953)
                  ·
                    refine ⟨2641312993247871961243465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3521750657663829281657953 2641312993247871961243465)
                    ·
                      refine ⟨1980984744935903970932599, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2641312993247871961243465 1980984744935903970932599)
                      ·
                        rfl

theorem cell23_3857954_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 6, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 6, 1, 2, 2, 2].length) (baseStart_3857954 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3857954 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3857954 prefixEnd_3857954 := by exact prefixLift 3857954
  have htrace : WordTrace (prefixWord ++ tailWord_3857954) baseStart_3857954 baseEnd_3857954 := by
    simpa [prefixWord, tailWord_3857954, baseEnd_3857954] using wordTrace_append hprefix tailTrace_3857954
  have hstable : (prefixWord ++ tailWord_3857954).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3857954).length < 2 ^ (prefixWord ++ tailWord_3857954).sum := by decide
  have hdescent : baseEnd_3857954 < baseStart_3857954 := by decide
  rcases family_descends (prefixWord ++ tailWord_3857954) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3857973 : List Nat := [1, 3, 3, 1, 1, 3, 1, 3, 2, 5]
def baseStart_3857973 : Nat := 118140960795 + 3857973 * 2 ^ 59
def prefixEnd_3857973 : Nat := 4983230072969 + 3 ^ 40 * 3857973 * 2
def baseEnd_3857973 : Nat := 660331500356113132198337

theorem tailTrace_3857973 : CollatzResearch.WordTrace tailWord_3857973 prefixEnd_3857973 660331500356113132198337 := by
  unfold tailWord_3857973
  simp only [CollatzResearch.WordTrace]
  refine ⟨140711835252230185176650573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93807890168153456784433715 140711835252230185176650573)
  ·
    refine ⟨52766938219586319441243965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 140711835252230185176650573 52766938219586319441243965)
    ·
      refine ⟨19787601832344869790466487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 52766938219586319441243965 19787601832344869790466487)
      ·
        refine ⟨29681402748517304685699731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19787601832344869790466487 29681402748517304685699731)
        ·
          refine ⟨44522104122775957028549597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29681402748517304685699731 44522104122775957028549597)
          ·
            refine ⟨16695789046040983885706099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 44522104122775957028549597 16695789046040983885706099)
            ·
              refine ⟨25043683569061475828559149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16695789046040983885706099 25043683569061475828559149)
              ·
                refine ⟨9391381338398053435709681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25043683569061475828559149 9391381338398053435709681)
                ·
                  refine ⟨7043536003798540076782261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9391381338398053435709681 7043536003798540076782261)
                  ·
                    refine ⟨660331500356113132198337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7043536003798540076782261 660331500356113132198337)
                    ·
                      rfl

theorem cell23_3857973_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 3, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 3, 1, 3, 2, 5].length) (baseStart_3857973 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3857973 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3857973 prefixEnd_3857973 := by exact prefixLift 3857973
  have htrace : WordTrace (prefixWord ++ tailWord_3857973) baseStart_3857973 baseEnd_3857973 := by
    simpa [prefixWord, tailWord_3857973, baseEnd_3857973] using wordTrace_append hprefix tailTrace_3857973
  have hstable : (prefixWord ++ tailWord_3857973).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3857973).length < 2 ^ (prefixWord ++ tailWord_3857973).sum := by decide
  have hdescent : baseEnd_3857973 < baseStart_3857973 := by decide
  rcases family_descends (prefixWord ++ tailWord_3857973) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3857993 : List Nat := [1, 2, 1, 1, 2, 2, 1, 2, 3, 6, 2]
def baseStart_3857993 : Nat := 118140960795 + 3857993 * 2 ^ 59
def prefixEnd_3857993 : Nat := 4983230072969 + 3 ^ 40 * 3857993 * 2
def baseEnd_3857993 : Nat := 1981004770681429318344919

theorem tailTrace_3857993 : CollatzResearch.WordTrace tailWord_3857993 prefixEnd_3857993 1981004770681429318344919 := by
  unfold tailWord_3857993
  simp only [CollatzResearch.WordTrace]
  refine ⟨140712564712157728592378633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93808376474771819061585755 140712564712157728592378633)
  ·
    refine ⟨105534423534118296444283975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 140712564712157728592378633 105534423534118296444283975)
    ·
      refine ⟨158301635301177444666425963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105534423534118296444283975 158301635301177444666425963)
      ·
        refine ⟨237452452951766166999638945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 158301635301177444666425963 237452452951766166999638945)
        ·
          refine ⟨178089339713824625249729209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 237452452951766166999638945 178089339713824625249729209)
          ·
            refine ⟨133567004785368468937296907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 178089339713824625249729209 133567004785368468937296907)
            ·
              refine ⟨200350507178052703405945361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 133567004785368468937296907 200350507178052703405945361)
              ·
                refine ⟨150262880383539527554459021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 200350507178052703405945361 150262880383539527554459021)
                ·
                  refine ⟨56348580143827322832922133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 150262880383539527554459021 56348580143827322832922133)
                  ·
                    refine ⟨2641339694241905757793225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 56348580143827322832922133 2641339694241905757793225)
                    ·
                      refine ⟨1981004770681429318344919, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2641339694241905757793225 1981004770681429318344919)
                      ·
                        rfl

theorem cell23_3857993_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 1, 2, 3, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 1, 2, 3, 6, 2].length) (baseStart_3857993 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3857993 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3857993 prefixEnd_3857993 := by exact prefixLift 3857993
  have htrace : WordTrace (prefixWord ++ tailWord_3857993) baseStart_3857993 baseEnd_3857993 := by
    simpa [prefixWord, tailWord_3857993, baseEnd_3857993] using wordTrace_append hprefix tailTrace_3857993
  have hstable : (prefixWord ++ tailWord_3857993).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3857993).length < 2 ^ (prefixWord ++ tailWord_3857993).sum := by decide
  have hdescent : baseEnd_3857993 < baseStart_3857993 := by decide
  rcases family_descends (prefixWord ++ tailWord_3857993) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3858016 : List Nat := [2, 1, 1, 3, 2, 1, 1, 2, 10]
def baseStart_3858016 : Nat := 118140960795 + 3858016 * 2 ^ 59
def prefixEnd_3858016 : Nat := 4983230072969 + 3 ^ 40 * 3858016 * 2
def baseEnd_3858016 : Nat := 220112953415164747595257

theorem tailTrace_3858016 : CollatzResearch.WordTrace tailWord_3858016 prefixEnd_3858016 220112953415164747595257 := by
  unfold tailWord_3858016
  simp only [CollatzResearch.WordTrace]
  refine ⟨70356701795537201760232951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93808935727382935680310601 70356701795537201760232951)
  ·
    refine ⟨105535052693305802640349427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70356701795537201760232951 105535052693305802640349427)
    ·
      refine ⟨158302579039958703960524141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105535052693305802640349427 158302579039958703960524141)
      ·
        refine ⟨59363467139984513985196553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 158302579039958703960524141 59363467139984513985196553)
        ·
          refine ⟨44522600354988385488897415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59363467139984513985196553 44522600354988385488897415)
          ·
            refine ⟨66783900532482578233346123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44522600354988385488897415 66783900532482578233346123)
            ·
              refine ⟨100175850798723867350019185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 66783900532482578233346123 100175850798723867350019185)
              ·
                refine ⟨75131888099042900512514389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 100175850798723867350019185 75131888099042900512514389)
                ·
                  refine ⟨220112953415164747595257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 75131888099042900512514389 220112953415164747595257)
                  ·
                    rfl

theorem cell23_3858016_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 1, 2, 10].length) (baseStart_3858016 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3858016 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3858016 prefixEnd_3858016 := by exact prefixLift 3858016
  have htrace : WordTrace (prefixWord ++ tailWord_3858016) baseStart_3858016 baseEnd_3858016 := by
    simpa [prefixWord, tailWord_3858016, baseEnd_3858016] using wordTrace_append hprefix tailTrace_3858016
  have hstable : (prefixWord ++ tailWord_3858016).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3858016).length < 2 ^ (prefixWord ++ tailWord_3858016).sum := by decide
  have hdescent : baseEnd_3858016 < baseStart_3858016 := by decide
  rcases family_descends (prefixWord ++ tailWord_3858016) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3858020 : List Nat := [2, 3, 1, 1, 2, 4, 1, 2, 3, 4]
def baseStart_3858020 : Nat := 118140960795 + 3858020 * 2 ^ 59
def prefixEnd_3858020 : Nat := 4983230072969 + 3 ^ 40 * 3858020 * 2
def baseEnd_3858020 : Nat := 660339544886366904235765

theorem tailTrace_3858020 : CollatzResearch.WordTrace tailWord_3858020 prefixEnd_3858020 660339544886366904235765 := by
  unfold tailWord_3858020
  simp only [CollatzResearch.WordTrace]
  refine ⟨70356774741529956101805757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93809032988706608135741009 70356774741529956101805757)
  ·
    refine ⟨26383790528073733538177159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 70356774741529956101805757 26383790528073733538177159)
    ·
      refine ⟨39575685792110600307265739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26383790528073733538177159 39575685792110600307265739)
      ·
        refine ⟨59363528688165900460898609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39575685792110600307265739 59363528688165900460898609)
        ·
          refine ⟨44522646516124425345673957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59363528688165900460898609 44522646516124425345673957)
          ·
            refine ⟨8347996221773329752313867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 44522646516124425345673957 8347996221773329752313867)
            ·
              refine ⟨12521994332659994628470801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8347996221773329752313867 12521994332659994628470801)
              ·
                refine ⟨9391495749494995971353101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12521994332659994628470801 9391495749494995971353101)
                ·
                  refine ⟨3521810906060623489257413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9391495749494995971353101 3521810906060623489257413)
                  ·
                    refine ⟨660339544886366904235765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3521810906060623489257413 660339544886366904235765)
                    ·
                      rfl

theorem cell23_3858020_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 4, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 4, 1, 2, 3, 4].length) (baseStart_3858020 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3858020 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3858020 prefixEnd_3858020 := by exact prefixLift 3858020
  have htrace : WordTrace (prefixWord ++ tailWord_3858020) baseStart_3858020 baseEnd_3858020 := by
    simpa [prefixWord, tailWord_3858020, baseEnd_3858020] using wordTrace_append hprefix tailTrace_3858020
  have hstable : (prefixWord ++ tailWord_3858020).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3858020).length < 2 ^ (prefixWord ++ tailWord_3858020).sum := by decide
  have hdescent : baseEnd_3858020 < baseStart_3858020 := by decide
  rcases family_descends (prefixWord ++ tailWord_3858020) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3858080 : List Nat := [2, 1, 1, 4, 3, 1, 1, 4, 1, 5]
def baseStart_3858080 : Nat := 118140960795 + 3858080 * 2 ^ 59
def prefixEnd_3858080 : Nat := 4983230072969 + 3 ^ 40 * 3858080 * 2
def baseEnd_3858080 : Nat := 660349814499456825985673

theorem tailTrace_3858080 : CollatzResearch.WordTrace tailWord_3858080 prefixEnd_3858080 660349814499456825985673 := by
  unfold tailWord_3858080
  simp only [CollatzResearch.WordTrace]
  refine ⟨70357868931421271225397847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93810491908561694967197129 70357868931421271225397847)
  ·
    refine ⟨105536803397131906838096771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70357868931421271225397847 105536803397131906838096771)
    ·
      refine ⟨158305205095697860257145157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105536803397131906838096771 158305205095697860257145157)
      ·
        refine ⟨29682225955443348798214717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 158305205095697860257145157 29682225955443348798214717)
        ·
          refine ⟨11130834733291255799330519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29682225955443348798214717 11130834733291255799330519)
          ·
            refine ⟨16696252099936883698995779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11130834733291255799330519 16696252099936883698995779)
            ·
              refine ⟨25044378149905325548493669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16696252099936883698995779 25044378149905325548493669)
              ·
                refine ⟨4695820903107248540342563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25044378149905325548493669 4695820903107248540342563)
                ·
                  refine ⟨7043731354660872810513845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4695820903107248540342563 7043731354660872810513845)
                  ·
                    refine ⟨660349814499456825985673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7043731354660872810513845 660349814499456825985673)
                    ·
                      rfl

theorem cell23_3858080_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 1, 1, 4, 1, 5].length) (baseStart_3858080 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3858080 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3858080 prefixEnd_3858080 := by exact prefixLift 3858080
  have htrace : WordTrace (prefixWord ++ tailWord_3858080) baseStart_3858080 baseEnd_3858080 := by
    simpa [prefixWord, tailWord_3858080, baseEnd_3858080] using wordTrace_append hprefix tailTrace_3858080
  have hstable : (prefixWord ++ tailWord_3858080).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3858080).length < 2 ^ (prefixWord ++ tailWord_3858080).sum := by decide
  have hdescent : baseEnd_3858080 < baseStart_3858080 := by decide
  rcases family_descends (prefixWord ++ tailWord_3858080) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3858120 : List Nat := [2, 1, 3, 1, 2, 2, 2, 2, 3, 2, 3]
def baseStart_3858120 : Nat := 118140960795 + 3858120 * 2 ^ 59
def prefixEnd_3858120 : Nat := 4983230072969 + 3 ^ 40 * 3858120 * 2
def baseEnd_3858120 : Nat := 1981069982724550321456835

theorem tailTrace_3858120 : CollatzResearch.WordTrace tailWord_3858120 prefixEnd_3858120 1981069982724550321456835 := by
  unfold tailWord_3858120
  simp only [CollatzResearch.WordTrace]
  refine ⟨70358598391348814641125907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93811464521798419521501209 70358598391348814641125907)
  ·
    refine ⟨105537897587023221961688861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70358598391348814641125907 105537897587023221961688861)
    ·
      refine ⟨39576711595133708235633323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 105537897587023221961688861 39576711595133708235633323)
      ·
        refine ⟨59365067392700562353449985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39576711595133708235633323 59365067392700562353449985)
        ·
          refine ⟨44523800544525421765087489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59365067392700562353449985 44523800544525421765087489)
          ·
            refine ⟨33392850408394066323815617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44523800544525421765087489 33392850408394066323815617)
            ·
              refine ⟨25044637806295549742861713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33392850408394066323815617 25044637806295549742861713)
              ·
                refine ⟨18783478354721662307146285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25044637806295549742861713 18783478354721662307146285)
                ·
                  refine ⟨7043804383020623365179857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18783478354721662307146285 7043804383020623365179857)
                  ·
                    refine ⟨5282853287265467523884893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7043804383020623365179857 5282853287265467523884893)
                    ·
                      refine ⟨1981069982724550321456835, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5282853287265467523884893 1981069982724550321456835)
                      ·
                        rfl

theorem cell23_3858120_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 2, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 2, 2, 3, 2, 3].length) (baseStart_3858120 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3858120 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3858120 prefixEnd_3858120 := by exact prefixLift 3858120
  have htrace : WordTrace (prefixWord ++ tailWord_3858120) baseStart_3858120 baseEnd_3858120 := by
    simpa [prefixWord, tailWord_3858120, baseEnd_3858120] using wordTrace_append hprefix tailTrace_3858120
  have hstable : (prefixWord ++ tailWord_3858120).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3858120).length < 2 ^ (prefixWord ++ tailWord_3858120).sum := by decide
  have hdescent : baseEnd_3858120 < baseStart_3858120 := by decide
  rcases family_descends (prefixWord ++ tailWord_3858120) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3858130 : List Nat := [3, 2, 2, 2, 2, 1, 2, 1, 1, 1, 6]
def baseStart_3858130 : Nat := 118140960795 + 3858130 * 2 ^ 59
def prefixEnd_3858130 : Nat := 4983230072969 + 3 ^ 40 * 3858130 * 2
def baseEnd_3858130 : Nat := 1981075117531095282331789

theorem tailTrace_3858130 : CollatzResearch.WordTrace tailWord_3858130 prefixEnd_3858130 1981075117531095282331789 := by
  unfold tailWord_3858130
  simp only [CollatzResearch.WordTrace]
  refine ⟨35179390378165350247528961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 93811707675107600660077229 35179390378165350247528961)
  ·
    refine ⟨26384542783624012685646721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35179390378165350247528961 26384542783624012685646721)
    ·
      refine ⟨19788407087718009514235041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26384542783624012685646721 19788407087718009514235041)
      ·
        refine ⟨14841305315788507135676281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19788407087718009514235041 14841305315788507135676281)
        ·
          refine ⟨11130978986841380351757211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14841305315788507135676281 11130978986841380351757211)
          ·
            refine ⟨16696468480262070527635817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11130978986841380351757211 16696468480262070527635817)
            ·
              refine ⟨12522351360196552895726863, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16696468480262070527635817 12522351360196552895726863)
              ·
                refine ⟨18783527040294829343590295, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12522351360196552895726863 18783527040294829343590295)
                ·
                  refine ⟨28175290560442244015385443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18783527040294829343590295 28175290560442244015385443)
                  ·
                    refine ⟨42262935840663366023078165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 28175290560442244015385443 42262935840663366023078165)
                    ·
                      refine ⟨1981075117531095282331789, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 42262935840663366023078165 1981075117531095282331789)
                      ·
                        rfl

theorem cell23_3858130_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 1, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 1, 2, 1, 1, 1, 6].length) (baseStart_3858130 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3858130 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3858130 prefixEnd_3858130 := by exact prefixLift 3858130
  have htrace : WordTrace (prefixWord ++ tailWord_3858130) baseStart_3858130 baseEnd_3858130 := by
    simpa [prefixWord, tailWord_3858130, baseEnd_3858130] using wordTrace_append hprefix tailTrace_3858130
  have hstable : (prefixWord ++ tailWord_3858130).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3858130).length < 2 ^ (prefixWord ++ tailWord_3858130).sum := by decide
  have hdescent : baseEnd_3858130 < baseStart_3858130 := by decide
  rcases family_descends (prefixWord ++ tailWord_3858130) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3858137 : List Nat := [1, 2, 1, 2, 3, 3, 3, 2, 1, 2, 3]
def baseStart_3858137 : Nat := 118140960795 + 3858137 * 2 ^ 59
def prefixEnd_3858137 : Nat := 4983230072969 + 3 ^ 40 * 3858137 * 2
def baseEnd_3858137 : Nat := 1981078711895676754944257

theorem tailTrace_3858137 : CollatzResearch.WordTrace tailWord_3858137 prefixEnd_3858137 1981078711895676754944257 := by
  unfold tailWord_3858137
  simp only [CollatzResearch.WordTrace]
  refine ⟨140717816823636041185620665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93811877882424027457080443 140717816823636041185620665)
  ·
    refine ⟨105538362617727030889215499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 140717816823636041185620665 105538362617727030889215499)
    ·
      refine ⟨158307543926590546333823249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105538362617727030889215499 158307543926590546333823249)
      ·
        refine ⟨118730657944942909750367437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 158307543926590546333823249 118730657944942909750367437)
        ·
          refine ⟨44523996729353591156387789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 118730657944942909750367437 44523996729353591156387789)
          ·
            refine ⟨16696498773507596683645421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 44523996729353591156387789 16696498773507596683645421)
            ·
              refine ⟨6261187040065348756367033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16696498773507596683645421 6261187040065348756367033)
              ·
                refine ⟨4695890280049011567275275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6261187040065348756367033 4695890280049011567275275)
                ·
                  refine ⟨7043835420073517350912913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4695890280049011567275275 7043835420073517350912913)
                  ·
                    refine ⟨5282876565055138013184685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7043835420073517350912913 5282876565055138013184685)
                    ·
                      refine ⟨1981078711895676754944257, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5282876565055138013184685 1981078711895676754944257)
                      ·
                        rfl

theorem cell23_3858137_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 3, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 3, 3, 2, 1, 2, 3].length) (baseStart_3858137 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3858137 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3858137 prefixEnd_3858137 := by exact prefixLift 3858137
  have htrace : WordTrace (prefixWord ++ tailWord_3858137) baseStart_3858137 baseEnd_3858137 := by
    simpa [prefixWord, tailWord_3858137, baseEnd_3858137] using wordTrace_append hprefix tailTrace_3858137
  have hstable : (prefixWord ++ tailWord_3858137).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3858137).length < 2 ^ (prefixWord ++ tailWord_3858137).sum := by decide
  have hdescent : baseEnd_3858137 < baseStart_3858137 := by decide
  rcases family_descends (prefixWord ++ tailWord_3858137) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3858147 : List Nat := [1, 1, 1, 7, 2, 1, 1, 2, 1, 2, 4]
def baseStart_3858147 : Nat := 118140960795 + 3858147 * 2 ^ 59
def prefixEnd_3858147 : Nat := 4983230072969 + 3 ^ 40 * 3858147 * 2
def baseEnd_3858147 : Nat := 1981083846702221715819211

theorem tailTrace_3858147 : CollatzResearch.WordTrace tailWord_3858147 prefixEnd_3858147 1981083846702221715819211 := by
  unfold tailWord_3858147
  simp only [CollatzResearch.WordTrace]
  refine ⟨140718181553599812893484695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93812121035733208595656463 140718181553599812893484695)
  ·
    refine ⟨211077272330399719340227043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140718181553599812893484695 211077272330399719340227043)
    ·
      refine ⟨316615908495599579010340565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 211077272330399719340227043 316615908495599579010340565)
      ·
        refine ⟨7420685355365615133054857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 316615908495599579010340565 7420685355365615133054857)
        ·
          refine ⟨5565514016524211349791143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7420685355365615133054857 5565514016524211349791143)
          ·
            refine ⟨8348271024786317024686715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5565514016524211349791143 8348271024786317024686715)
            ·
              refine ⟨12522406537179475537030073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8348271024786317024686715 12522406537179475537030073)
              ·
                refine ⟨9391804902884606652772555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12522406537179475537030073 9391804902884606652772555)
                ·
                  refine ⟨14087707354326909979158833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9391804902884606652772555 14087707354326909979158833)
                  ·
                    refine ⟨10565780515745182484369125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14087707354326909979158833 10565780515745182484369125)
                    ·
                      refine ⟨1981083846702221715819211, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10565780515745182484369125 1981083846702221715819211)
                      ·
                        rfl

theorem cell23_3858147_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 2, 1, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 2, 1, 1, 2, 1, 2, 4].length) (baseStart_3858147 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3858147 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3858147 prefixEnd_3858147 := by exact prefixLift 3858147
  have htrace : WordTrace (prefixWord ++ tailWord_3858147) baseStart_3858147 baseEnd_3858147 := by
    simpa [prefixWord, tailWord_3858147, baseEnd_3858147] using wordTrace_append hprefix tailTrace_3858147
  have hstable : (prefixWord ++ tailWord_3858147).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3858147).length < 2 ^ (prefixWord ++ tailWord_3858147).sum := by decide
  have hdescent : baseEnd_3858147 < baseStart_3858147 := by decide
  rcases family_descends (prefixWord ++ tailWord_3858147) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3858151 : List Nat := [1, 1, 5, 4, 1, 1, 3, 1, 1, 1, 4]
def baseStart_3858151 : Nat := 118140960795 + 3858151 * 2 ^ 59
def prefixEnd_3858151 : Nat := 4983230072969 + 3 ^ 40 * 3858151 * 2
def baseEnd_3858151 : Nat := 1981085900624839700169193

theorem tailTrace_3858151 : CollatzResearch.WordTrace tailWord_3858151 prefixEnd_3858151 1981085900624839700169193 := by
  unfold tailWord_3858151
  simp only [CollatzResearch.WordTrace]
  refine ⟨140718327445585321576630307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93812218297056881051086871 140718327445585321576630307)
  ·
    refine ⟨211077491168377982364945461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140718327445585321576630307 211077491168377982364945461)
    ·
      refine ⟨19788514797035435846713637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 211077491168377982364945461 19788514797035435846713637)
      ·
        refine ⟨3710346524444144221258807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 19788514797035435846713637 3710346524444144221258807)
        ·
          refine ⟨5565519786666216331888211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3710346524444144221258807 5565519786666216331888211)
          ·
            refine ⟨8348279679999324497832317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5565519786666216331888211 8348279679999324497832317)
            ·
              refine ⟨3130604879999746686687119, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8348279679999324497832317 3130604879999746686687119)
              ·
                refine ⟨4695907319999620030030679, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3130604879999746686687119 4695907319999620030030679)
                ·
                  refine ⟨7043860979999430045046019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4695907319999620030030679 7043860979999430045046019)
                  ·
                    refine ⟨10565791469999145067569029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7043860979999430045046019 10565791469999145067569029)
                    ·
                      refine ⟨1981085900624839700169193, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10565791469999145067569029 1981085900624839700169193)
                      ·
                        rfl

theorem cell23_3858151_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 4, 1, 1, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 4, 1, 1, 3, 1, 1, 1, 4].length) (baseStart_3858151 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3858151 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3858151 prefixEnd_3858151 := by exact prefixLift 3858151
  have htrace : WordTrace (prefixWord ++ tailWord_3858151) baseStart_3858151 baseEnd_3858151 := by
    simpa [prefixWord, tailWord_3858151, baseEnd_3858151] using wordTrace_append hprefix tailTrace_3858151
  have hstable : (prefixWord ++ tailWord_3858151).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3858151).length < 2 ^ (prefixWord ++ tailWord_3858151).sum := by decide
  have hdescent : baseEnd_3858151 < baseStart_3858151 := by decide
  rcases family_descends (prefixWord ++ tailWord_3858151) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3858163 : List Nat := [1, 1, 1, 2, 2, 3, 2, 2, 2, 2, 5]
def baseStart_3858163 : Nat := 118140960795 + 3858163 * 2 ^ 59
def prefixEnd_3858163 : Nat := 4983230072969 + 3 ^ 40 * 3858163 * 2
def baseEnd_3858163 : Nat := 1981092062392693653219137

theorem tailTrace_3858163 : CollatzResearch.WordTrace tailWord_3858163 prefixEnd_3858163 1981092062392693653219137 := by
  unfold tailWord_3858163
  simp only [CollatzResearch.WordTrace]
  refine ⟨140718765121541847626067143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93812510081027898417378095 140718765121541847626067143)
  ·
    refine ⟨211078147682312771439100715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140718765121541847626067143 211078147682312771439100715)
    ·
      refine ⟨316617221523469157158651073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 211078147682312771439100715 316617221523469157158651073)
      ·
        refine ⟨237462916142601867868988305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 316617221523469157158651073 237462916142601867868988305)
        ·
          refine ⟨178097187106951400901741229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 237462916142601867868988305 178097187106951400901741229)
          ·
            refine ⟨66786445165106775338152961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 178097187106951400901741229 66786445165106775338152961)
            ·
              refine ⟨50089833873830081503614721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 66786445165106775338152961 50089833873830081503614721)
              ·
                refine ⟨37567375405372561127711041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 50089833873830081503614721 37567375405372561127711041)
                ·
                  refine ⟨28175531554029420845783281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 37567375405372561127711041 28175531554029420845783281)
                  ·
                    refine ⟨21131648665522065634337461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 28175531554029420845783281 21131648665522065634337461)
                    ·
                      refine ⟨1981092062392693653219137, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 21131648665522065634337461 1981092062392693653219137)
                      ·
                        rfl

theorem cell23_3858163_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 2, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 2, 2, 2, 2, 5].length) (baseStart_3858163 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3858163 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3858163 prefixEnd_3858163 := by exact prefixLift 3858163
  have htrace : WordTrace (prefixWord ++ tailWord_3858163) baseStart_3858163 baseEnd_3858163 := by
    simpa [prefixWord, tailWord_3858163, baseEnd_3858163] using wordTrace_append hprefix tailTrace_3858163
  have hstable : (prefixWord ++ tailWord_3858163).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3858163).length < 2 ^ (prefixWord ++ tailWord_3858163).sum := by decide
  have hdescent : baseEnd_3858163 < baseStart_3858163 := by decide
  rcases family_descends (prefixWord ++ tailWord_3858163) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3858167 : List Nat := [1, 1, 3, 1, 1, 1, 5, 4, 2, 1, 3]
def baseStart_3858167 : Nat := 118140960795 + 3858167 * 2 ^ 59
def prefixEnd_3858167 : Nat := 4983230072969 + 3 ^ 40 * 3858167 * 2
def baseEnd_3858167 : Nat := 1981094116315311637569119

theorem tailTrace_3858167 : CollatzResearch.WordTrace tailWord_3858167 prefixEnd_3858167 1981094116315311637569119 := by
  unfold tailWord_3858167
  simp only [CollatzResearch.WordTrace]
  refine ⟨140718911013527356309212755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93812607342351570872808503 140718911013527356309212755)
  ·
    refine ⟨211078366520291034463819133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140718911013527356309212755 211078366520291034463819133)
    ·
      refine ⟨79154387445109137923932175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 211078366520291034463819133 79154387445109137923932175)
      ·
        refine ⟨118731581167663706885898263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79154387445109137923932175 118731581167663706885898263)
        ·
          refine ⟨178097371751495560328847395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 118731581167663706885898263 178097371751495560328847395)
          ·
            refine ⟨267146057627243340493271093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 178097371751495560328847395 267146057627243340493271093)
            ·
              refine ⟨25044942902554063171244165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 267146057627243340493271093 25044942902554063171244165)
              ·
                refine ⟨4695926794228886844608281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25044942902554063171244165 4695926794228886844608281)
                ·
                  refine ⟨3521945095671665133456211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4695926794228886844608281 3521945095671665133456211)
                  ·
                    refine ⟨5282917643507497700184317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3521945095671665133456211 5282917643507497700184317)
                    ·
                      refine ⟨1981094116315311637569119, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5282917643507497700184317 1981094116315311637569119)
                      ·
                        rfl

theorem cell23_3858167_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 5, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 5, 4, 2, 1, 3].length) (baseStart_3858167 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3858167 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3858167 prefixEnd_3858167 := by exact prefixLift 3858167
  have htrace : WordTrace (prefixWord ++ tailWord_3858167) baseStart_3858167 baseEnd_3858167 := by
    simpa [prefixWord, tailWord_3858167, baseEnd_3858167] using wordTrace_append hprefix tailTrace_3858167
  have hstable : (prefixWord ++ tailWord_3858167).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3858167).length < 2 ^ (prefixWord ++ tailWord_3858167).sum := by decide
  have hdescent : baseEnd_3858167 < baseStart_3858167 := by decide
  rcases family_descends (prefixWord ++ tailWord_3858167) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3858174 : List Nat := [4, 2, 2, 1, 4, 1, 1, 8]
def baseStart_3858174 : Nat := 118140960795 + 3858174 * 2 ^ 59
def prefixEnd_3858174 : Nat := 4983230072969 + 3 ^ 40 * 3858174 * 2
def baseEnd_3858174 : Nat := 73373989284440485562281

theorem tailTrace_3858174 : CollatzResearch.WordTrace tailWord_3858174 prefixEnd_3858174 73373989284440485562281 := by
  unfold tailWord_3858174
  simp only [CollatzResearch.WordTrace]
  refine ⟨17589895790562749563089697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 93812777549667997669811717 17589895790562749563089697)
  ·
    refine ⟨13192421842922062172317273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17589895790562749563089697 13192421842922062172317273)
    ·
      refine ⟨9894316382191546629237955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13192421842922062172317273 9894316382191546629237955)
      ·
        refine ⟨14841474573287319943856933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9894316382191546629237955 14841474573287319943856933)
        ·
          refine ⟨2782776482491372489473175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 14841474573287319943856933 2782776482491372489473175)
          ·
            refine ⟨4174164723737058734209763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2782776482491372489473175 4174164723737058734209763)
            ·
              refine ⟨6261247085605588101314645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4174164723737058734209763 6261247085605588101314645)
              ·
                refine ⟨73373989284440485562281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 6261247085605588101314645 73373989284440485562281)
                ·
                  rfl

theorem cell23_3858174_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 4, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 4, 1, 1, 8].length) (baseStart_3858174 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3858174 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3858174 prefixEnd_3858174 := by exact prefixLift 3858174
  have htrace : WordTrace (prefixWord ++ tailWord_3858174) baseStart_3858174 baseEnd_3858174 := by
    simpa [prefixWord, tailWord_3858174, baseEnd_3858174] using wordTrace_append hprefix tailTrace_3858174
  have hstable : (prefixWord ++ tailWord_3858174).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3858174).length < 2 ^ (prefixWord ++ tailWord_3858174).sum := by decide
  have hdescent : baseEnd_3858174 < baseStart_3858174 := by decide
  rcases family_descends (prefixWord ++ tailWord_3858174) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3858177 : List Nat := [1, 2, 4, 1, 1, 1, 3, 2, 3, 3, 2]
def baseStart_3858177 : Nat := 118140960795 + 3858177 * 2 ^ 59
def prefixEnd_3858177 : Nat := 4983230072969 + 3 ^ 40 * 3858177 * 2
def baseEnd_3858177 : Nat := 1981099251121856598444073

theorem tailTrace_3858177 : CollatzResearch.WordTrace tailWord_3858177 prefixEnd_3858177 1981099251121856598444073 := by
  unfold tailWord_3858177
  simp only [CollatzResearch.WordTrace]
  refine ⟨140719275743491128017076785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93812850495660752011384523 140719275743491128017076785)
  ·
    refine ⟨105539456807618346012807589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 140719275743491128017076785 105539456807618346012807589)
    ·
      refine ⟨19788648151428439877401423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 105539456807618346012807589 19788648151428439877401423)
      ·
        refine ⟨29682972227142659816102135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19788648151428439877401423 29682972227142659816102135)
        ·
          refine ⟨44524458340713989724153203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29682972227142659816102135 44524458340713989724153203)
          ·
            refine ⟨66786687511070984586229805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44524458340713989724153203 66786687511070984586229805)
            ·
              refine ⟨25045007816651619219836177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 66786687511070984586229805 25045007816651619219836177)
              ·
                refine ⟨18783755862488714414877133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25045007816651619219836177 18783755862488714414877133)
                ·
                  refine ⟨7043908448433267905578925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18783755862488714414877133 7043908448433267905578925)
                  ·
                    refine ⟨2641465668162475464592097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7043908448433267905578925 2641465668162475464592097)
                    ·
                      refine ⟨1981099251121856598444073, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2641465668162475464592097 1981099251121856598444073)
                      ·
                        rfl

theorem cell23_3858177_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 3, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 3, 2, 3, 3, 2].length) (baseStart_3858177 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3858177 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3858177 prefixEnd_3858177 := by exact prefixLift 3858177
  have htrace : WordTrace (prefixWord ++ tailWord_3858177) baseStart_3858177 baseEnd_3858177 := by
    simpa [prefixWord, tailWord_3858177, baseEnd_3858177] using wordTrace_append hprefix tailTrace_3858177
  have hstable : (prefixWord ++ tailWord_3858177).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3858177).length < 2 ^ (prefixWord ++ tailWord_3858177).sum := by decide
  have hdescent : baseEnd_3858177 < baseStart_3858177 := by decide
  rcases family_descends (prefixWord ++ tailWord_3858177) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3858207 : List Nat := [1, 1, 2, 4, 2, 1, 1, 4, 1, 4, 2]
def baseStart_3858207 : Nat := 118140960795 + 3858207 * 2 ^ 59
def prefixEnd_3858207 : Nat := 4983230072969 + 3 ^ 40 * 3858207 * 2
def baseEnd_3858207 : Nat := 1981114655541491481068935

theorem tailTrace_3858207 : CollatzResearch.WordTrace tailWord_3858207 prefixEnd_3858207 1981114655541491481068935 := by
  unfold tailWord_3858207
  simp only [CollatzResearch.WordTrace]
  refine ⟨140720369933382443140668875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93813579955588295427112583 140720369933382443140668875)
  ·
    refine ⟨211080554900073664711003313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140720369933382443140668875 211080554900073664711003313)
    ·
      refine ⟨158310416175055248533252485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 211080554900073664711003313 158310416175055248533252485)
      ·
        refine ⟨29683203032822859099984841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 158310416175055248533252485 29683203032822859099984841)
        ·
          refine ⟨22262402274617144324988631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29683203032822859099984841 22262402274617144324988631)
          ·
            refine ⟨33393603411925716487482947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22262402274617144324988631 33393603411925716487482947)
            ·
              refine ⟨50090405117888574731224421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33393603411925716487482947 50090405117888574731224421)
              ·
                refine ⟨9391950959604107762104579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 50090405117888574731224421 9391950959604107762104579)
                ·
                  refine ⟨14087926439406161643156869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9391950959604107762104579 14087926439406161643156869)
                  ·
                    refine ⟨2641486207388655308091913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 14087926439406161643156869 2641486207388655308091913)
                    ·
                      refine ⟨1981114655541491481068935, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2641486207388655308091913 1981114655541491481068935)
                      ·
                        rfl

theorem cell23_3858207_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 1, 4, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 1, 4, 1, 4, 2].length) (baseStart_3858207 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3858207 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3858207 prefixEnd_3858207 := by exact prefixLift 3858207
  have htrace : WordTrace (prefixWord ++ tailWord_3858207) baseStart_3858207 baseEnd_3858207 := by
    simpa [prefixWord, tailWord_3858207, baseEnd_3858207] using wordTrace_append hprefix tailTrace_3858207
  have hstable : (prefixWord ++ tailWord_3858207).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3858207).length < 2 ^ (prefixWord ++ tailWord_3858207).sum := by decide
  have hdescent : baseEnd_3858207 < baseStart_3858207 := by decide
  rcases family_descends (prefixWord ++ tailWord_3858207) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3858210 : List Nat := [3, 3, 1, 1, 2, 1, 2, 1, 1, 3, 5]
def baseStart_3858210 : Nat := 118140960795 + 3858210 * 2 ^ 59
def prefixEnd_3858210 : Nat := 4983230072969 + 3 ^ 40 * 3858210 * 2
def baseEnd_3858210 : Nat := 1981116195983454969331421

theorem tailTrace_3858210 : CollatzResearch.WordTrace tailWord_3858210 prefixEnd_3858210 1981116195983454969331421 := by
  unfold tailWord_3858210
  simp only [CollatzResearch.WordTrace]
  refine ⟨35180119838092893663257021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 93813652901581049768685389 35180119838092893663257021)
  ·
    refine ⟨13192544939284835123721383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 35180119838092893663257021 13192544939284835123721383)
    ·
      refine ⟨19788817408927252685582075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13192544939284835123721383 19788817408927252685582075)
      ·
        refine ⟨29683226113390879028373113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19788817408927252685582075 29683226113390879028373113)
        ·
          refine ⟨22262419585043159271279835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29683226113390879028373113 22262419585043159271279835)
          ·
            refine ⟨33393629377564738906919753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22262419585043159271279835 33393629377564738906919753)
            ·
              refine ⟨25045222033173554180189815, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33393629377564738906919753 25045222033173554180189815)
              ·
                refine ⟨37567833049760331270284723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25045222033173554180189815 37567833049760331270284723)
                ·
                  refine ⟨56351749574640496905427085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37567833049760331270284723 56351749574640496905427085)
                  ·
                    refine ⟨21131906090490186339535157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 56351749574640496905427085 21131906090490186339535157)
                    ·
                      refine ⟨1981116195983454969331421, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 21131906090490186339535157 1981116195983454969331421)
                      ·
                        rfl

theorem cell23_3858210_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 2, 1, 1, 3, 5].length) (baseStart_3858210 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3858210 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3858210 prefixEnd_3858210 := by exact prefixLift 3858210
  have htrace : WordTrace (prefixWord ++ tailWord_3858210) baseStart_3858210 baseEnd_3858210 := by
    simpa [prefixWord, tailWord_3858210, baseEnd_3858210] using wordTrace_append hprefix tailTrace_3858210
  have hstable : (prefixWord ++ tailWord_3858210).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3858210).length < 2 ^ (prefixWord ++ tailWord_3858210).sum := by decide
  have hdescent : baseEnd_3858210 < baseStart_3858210 := by decide
  rcases family_descends (prefixWord ++ tailWord_3858210) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3858220 : List Nat := [2, 2, 1, 1, 1, 5, 1, 2, 2, 2, 4]
def baseStart_3858220 : Nat := 118140960795 + 3858220 * 2 ^ 59
def prefixEnd_3858220 : Nat := 4983230072969 + 3 ^ 40 * 3858220 * 2
def baseEnd_3858220 : Nat := 1981121330789999930206375

theorem tailTrace_3858220 : CollatzResearch.WordTrace tailWord_3858220 prefixEnd_3858220 1981121330789999930206375 := by
  unfold tailWord_3858220
  simp only [CollatzResearch.WordTrace]
  refine ⟨70360422041167673180446057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93813896054890230907261409 70360422041167673180446057)
  ·
    refine ⟨52770316530875754885334543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70360422041167673180446057 52770316530875754885334543)
    ·
      refine ⟨79155474796313632328001815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52770316530875754885334543 79155474796313632328001815)
      ·
        refine ⟨118733212194470448492002723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79155474796313632328001815 118733212194470448492002723)
        ·
          refine ⟨178099818291705672738004085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 118733212194470448492002723 178099818291705672738004085)
          ·
            refine ⟨16696857964847406819187883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 178099818291705672738004085 16696857964847406819187883)
            ·
              refine ⟨25045286947271110228781825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16696857964847406819187883 25045286947271110228781825)
              ·
                refine ⟨18783965210453332671586369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25045286947271110228781825 18783965210453332671586369)
                ·
                  refine ⟨14087973907839999503689777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18783965210453332671586369 14087973907839999503689777)
                  ·
                    refine ⟨10565980430879999627767333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14087973907839999503689777 10565980430879999627767333)
                    ·
                      refine ⟨1981121330789999930206375, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10565980430879999627767333 1981121330789999930206375)
                      ·
                        rfl

theorem cell23_3858220_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 2, 4].length) (baseStart_3858220 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3858220 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3858220 prefixEnd_3858220 := by exact prefixLift 3858220
  have htrace : WordTrace (prefixWord ++ tailWord_3858220) baseStart_3858220 baseEnd_3858220 := by
    simpa [prefixWord, tailWord_3858220, baseEnd_3858220] using wordTrace_append hprefix tailTrace_3858220
  have hstable : (prefixWord ++ tailWord_3858220).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3858220).length < 2 ^ (prefixWord ++ tailWord_3858220).sum := by decide
  have hdescent : baseEnd_3858220 < baseStart_3858220 := by decide
  rcases family_descends (prefixWord ++ tailWord_3858220) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3858223 : List Nat := [1, 1, 2, 1, 2, 1, 2, 3, 1, 2, 7]
def baseStart_3858223 : Nat := 118140960795 + 3858223 * 2 ^ 59
def prefixEnd_3858223 : Nat := 4983230072969 + 3 ^ 40 * 3858223 * 2
def baseEnd_3858223 : Nat := 1981122871231963418468861

theorem tailTrace_3858223 : CollatzResearch.WordTrace tailWord_3858223 prefixEnd_3858223 1981122871231963418468861 := by
  unfold tailWord_3858223
  simp only [CollatzResearch.WordTrace]
  refine ⟨140720953501324477873251323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93813969000882985248834215 140720953501324477873251323)
  ·
    refine ⟨211081430251986716809876985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140720953501324477873251323 211081430251986716809876985)
    ·
      refine ⟨158311072688990037607407739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 211081430251986716809876985 158311072688990037607407739)
      ·
        refine ⟨237466609033485056411111609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 158311072688990037607407739 237466609033485056411111609)
        ·
          refine ⟨178099956775113792308333707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 237466609033485056411111609 178099956775113792308333707)
          ·
            refine ⟨267149935162670688462500561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 178099956775113792308333707 267149935162670688462500561)
            ·
              refine ⟨200362451372003016346875421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 267149935162670688462500561 200362451372003016346875421)
              ·
                refine ⟨75135919264501131130078283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 200362451372003016346875421 75135919264501131130078283)
                ·
                  refine ⟨112703878896751696695117425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 75135919264501131130078283 112703878896751696695117425)
                  ·
                    refine ⟨84527909172563772521338069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 112703878896751696695117425 84527909172563772521338069)
                    ·
                      refine ⟨1981122871231963418468861, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 84527909172563772521338069 1981122871231963418468861)
                      ·
                        rfl

theorem cell23_3858223_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 2, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 2, 3, 1, 2, 7].length) (baseStart_3858223 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3858223 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3858223 prefixEnd_3858223 := by exact prefixLift 3858223
  have htrace : WordTrace (prefixWord ++ tailWord_3858223) baseStart_3858223 baseEnd_3858223 := by
    simpa [prefixWord, tailWord_3858223, baseEnd_3858223] using wordTrace_append hprefix tailTrace_3858223
  have hstable : (prefixWord ++ tailWord_3858223).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3858223).length < 2 ^ (prefixWord ++ tailWord_3858223).sum := by decide
  have hdescent : baseEnd_3858223 < baseStart_3858223 := by decide
  rcases family_descends (prefixWord ++ tailWord_3858223) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3858237 : List Nat := [1, 4, 1, 4, 1, 1, 2, 1, 2, 2, 4]
def baseStart_3858237 : Nat := 118140960795 + 3858237 * 2 ^ 59
def prefixEnd_3858237 : Nat := 4983230072969 + 3 ^ 40 * 3858237 * 2
def baseEnd_3858237 : Nat := 1981130059961126363693797

theorem tailTrace_3858237 : CollatzResearch.WordTrace tailWord_3858237 prefixEnd_3858237 1981130059961126363693797 := by
  unfold tailWord_3858237
  simp only [CollatzResearch.WordTrace]
  refine ⟨140721464123273758264260965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93814309415515838842840643 140721464123273758264260965)
  ·
    refine ⟨26385274523113829674548931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 140721464123273758264260965 26385274523113829674548931)
    ·
      refine ⟨39577911784670744511823397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26385274523113829674548931 39577911784670744511823397)
      ·
        refine ⟨7420858459625764595966887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 39577911784670744511823397 7420858459625764595966887)
        ·
          refine ⟨11131287689438646893950331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7420858459625764595966887 11131287689438646893950331)
          ·
            refine ⟨16696931534157970340925497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11131287689438646893950331 16696931534157970340925497)
            ·
              refine ⟨12522698650618477755694123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16696931534157970340925497 12522698650618477755694123)
              ·
                refine ⟨18784047975927716633541185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12522698650618477755694123 18784047975927716633541185)
                ·
                  refine ⟨14088035981945787475155889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18784047975927716633541185 14088035981945787475155889)
                  ·
                    refine ⟨10566026986459340606366917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14088035981945787475155889 10566026986459340606366917)
                    ·
                      refine ⟨1981130059961126363693797, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10566026986459340606366917 1981130059961126363693797)
                      ·
                        rfl

theorem cell23_3858237_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 1, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 1, 2, 1, 2, 2, 4].length) (baseStart_3858237 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3858237 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3858237 prefixEnd_3858237 := by exact prefixLift 3858237
  have htrace : WordTrace (prefixWord ++ tailWord_3858237) baseStart_3858237 baseEnd_3858237 := by
    simpa [prefixWord, tailWord_3858237, baseEnd_3858237] using wordTrace_append hprefix tailTrace_3858237
  have hstable : (prefixWord ++ tailWord_3858237).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3858237).length < 2 ^ (prefixWord ++ tailWord_3858237).sum := by decide
  have hdescent : baseEnd_3858237 < baseStart_3858237 := by decide
  rcases family_descends (prefixWord ++ tailWord_3858237) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3858297 : List Nat := [1, 2, 1, 3, 2, 2, 2, 1, 1, 6, 2]
def baseStart_3858297 : Nat := 118140960795 + 3858297 * 2 ^ 59
def prefixEnd_3858297 : Nat := 4983230072969 + 3 ^ 40 * 3858297 * 2
def baseEnd_3858297 : Nat := 1981160868800396128943521

theorem tailTrace_3858297 : CollatzResearch.WordTrace tailWord_3858297 prefixEnd_3858297 1981160868800396128943521 := by
  unfold tailWord_3858297
  simp only [CollatzResearch.WordTrace]
  refine ⟨140723652503056388511445145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93815768335370925674296763 140723652503056388511445145)
  ·
    refine ⟨105542739377292291383583859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 140723652503056388511445145 105542739377292291383583859)
    ·
      refine ⟨158314109065938437075375789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105542739377292291383583859 158314109065938437075375789)
      ·
        refine ⟨59367790899726913903265921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 158314109065938437075375789 59367790899726913903265921)
        ·
          refine ⟨44525843174795185427449441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59367790899726913903265921 44525843174795185427449441)
          ·
            refine ⟨33394382381096389070587081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44525843174795185427449441 33394382381096389070587081)
            ·
              refine ⟨25045786785822291802940311, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33394382381096389070587081 25045786785822291802940311)
              ·
                refine ⟨37568680178733437704410467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25045786785822291802940311 37568680178733437704410467)
                ·
                  refine ⟨56353020268100156556615701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37568680178733437704410467 56353020268100156556615701)
                  ·
                    refine ⟨2641547825067194838591361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 56353020268100156556615701 2641547825067194838591361)
                    ·
                      refine ⟨1981160868800396128943521, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2641547825067194838591361 1981160868800396128943521)
                      ·
                        rfl

theorem cell23_3858297_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 2, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 2, 1, 1, 6, 2].length) (baseStart_3858297 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3858297 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3858297 prefixEnd_3858297 := by exact prefixLift 3858297
  have htrace : WordTrace (prefixWord ++ tailWord_3858297) baseStart_3858297 baseEnd_3858297 := by
    simpa [prefixWord, tailWord_3858297, baseEnd_3858297] using wordTrace_append hprefix tailTrace_3858297
  have hstable : (prefixWord ++ tailWord_3858297).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3858297).length < 2 ^ (prefixWord ++ tailWord_3858297).sum := by decide
  have hdescent : baseEnd_3858297 < baseStart_3858297 := by decide
  rcases family_descends (prefixWord ++ tailWord_3858297) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3858360 : List Nat := [2, 1, 2, 1, 2, 3, 1, 1, 2, 1, 7]
def baseStart_3858360 : Nat := 118140960795 + 3858360 * 2 ^ 59
def prefixEnd_3858360 : Nat := 4983230072969 + 3 ^ 40 * 3858360 * 2
def baseEnd_3858360 : Nat := 1981193218081629382455731

theorem tailTrace_3858360 : CollatzResearch.WordTrace tailWord_3858360 prefixEnd_3858360 1981193218081629382455731 := by
  unfold tailWord_3858360
  simp only [CollatzResearch.WordTrace]
  refine ⟨70362975150914075135494267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93817300201218766847325689 70362975150914075135494267)
  ·
    refine ⟨105544462726371112703241401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70362975150914075135494267 105544462726371112703241401)
    ·
      refine ⟨79158347044778334527431051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 105544462726371112703241401 79158347044778334527431051)
      ·
        refine ⟨118737520567167501791146577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79158347044778334527431051 118737520567167501791146577)
        ·
          refine ⟨89053140425375626343359933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 118737520567167501791146577 89053140425375626343359933)
          ·
            refine ⟨33394927659515859878759975, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 89053140425375626343359933 33394927659515859878759975)
            ·
              refine ⟨50092391489273789818139963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33394927659515859878759975 50092391489273789818139963)
              ·
                refine ⟨75138587233910684727209945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50092391489273789818139963 75138587233910684727209945)
                ·
                  refine ⟨56353940425433013545407459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 75138587233910684727209945 56353940425433013545407459)
                  ·
                    refine ⟨84530910638149520318111189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 56353940425433013545407459 84530910638149520318111189)
                    ·
                      refine ⟨1981193218081629382455731, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 84530910638149520318111189 1981193218081629382455731)
                      ·
                        rfl

theorem cell23_3858360_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 1, 1, 2, 1, 7].length) (baseStart_3858360 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3858360 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3858360 prefixEnd_3858360 := by exact prefixLift 3858360
  have htrace : WordTrace (prefixWord ++ tailWord_3858360) baseStart_3858360 baseEnd_3858360 := by
    simpa [prefixWord, tailWord_3858360, baseEnd_3858360] using wordTrace_append hprefix tailTrace_3858360
  have hstable : (prefixWord ++ tailWord_3858360).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3858360).length < 2 ^ (prefixWord ++ tailWord_3858360).sum := by decide
  have hdescent : baseEnd_3858360 < baseStart_3858360 := by decide
  rcases family_descends (prefixWord ++ tailWord_3858360) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3858367 : List Nat := [1, 1, 2, 2, 2, 1, 4, 4, 1, 5]
def baseStart_3858367 : Nat := 118140960795 + 3858367 * 2 ^ 59
def prefixEnd_3858367 : Nat := 4983230072969 + 3 ^ 40 * 3858367 * 2
def baseEnd_3858367 : Nat := 660398937482070285022733

theorem tailTrace_3858367 : CollatzResearch.WordTrace tailWord_3858367 prefixEnd_3858367 660398937482070285022733 := by
  unfold tailWord_3858367
  simp only [CollatzResearch.WordTrace]
  refine ⟨140726205612802790466493355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93817470408535193644328903 140726205612802790466493355)
  ·
    refine ⟨211089308419204185699740033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140726205612802790466493355 211089308419204185699740033)
    ·
      refine ⟨158316981314403139274805025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 211089308419204185699740033 158316981314403139274805025)
      ·
        refine ⟨118737735985802354456103769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 158316981314403139274805025 118737735985802354456103769)
        ·
          refine ⟨89053301989351765842077827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 118737735985802354456103769 89053301989351765842077827)
          ·
            refine ⟨133579952984027648763116741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 89053301989351765842077827 133579952984027648763116741)
            ·
              refine ⟨25046241184505184143084389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 133579952984027648763116741 25046241184505184143084389)
              ·
                refine ⟨4696170222094722026828323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25046241184505184143084389 4696170222094722026828323)
                ·
                  refine ⟨7044255333142083040242485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4696170222094722026828323 7044255333142083040242485)
                  ·
                    refine ⟨660398937482070285022733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7044255333142083040242485 660398937482070285022733)
                    ·
                      rfl

theorem cell23_3858367_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 4, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 4, 4, 1, 5].length) (baseStart_3858367 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3858367 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3858367 prefixEnd_3858367 := by exact prefixLift 3858367
  have htrace : WordTrace (prefixWord ++ tailWord_3858367) baseStart_3858367 baseEnd_3858367 := by
    simpa [prefixWord, tailWord_3858367, baseEnd_3858367] using wordTrace_append hprefix tailTrace_3858367
  have hstable : (prefixWord ++ tailWord_3858367).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3858367).length < 2 ^ (prefixWord ++ tailWord_3858367).sum := by decide
  have hdescent : baseEnd_3858367 < baseStart_3858367 := by decide
  rcases family_descends (prefixWord ++ tailWord_3858367) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3858384 : List Nat := [2, 1, 1, 1, 1, 2, 8, 1, 1, 5]
def baseStart_3858384 : Nat := 118140960795 + 3858384 * 2 ^ 59
def prefixEnd_3858384 : Nat := 4983230072969 + 3 ^ 40 * 3858384 * 2
def baseEnd_3858384 : Nat := 660401847205779096185207

theorem tailTrace_3858384 : CollatzResearch.WordTrace tailWord_3858384 prefixEnd_3858384 660401847205779096185207 := by
  unfold tailWord_3858384
  simp only [CollatzResearch.WordTrace]
  refine ⟨70363412826870601184931103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93817883769160801579908137 70363412826870601184931103)
  ·
    refine ⟨105545119240305901777396655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70363412826870601184931103 105545119240305901777396655)
    ·
      refine ⟨158317678860458852666094983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105545119240305901777396655 158317678860458852666094983)
      ·
        refine ⟨237476518290688278999142475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 158317678860458852666094983 237476518290688278999142475)
        ·
          refine ⟨356214777436032418498713713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 237476518290688278999142475 356214777436032418498713713)
          ·
            refine ⟨267161083077024313874035285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 356214777436032418498713713 267161083077024313874035285)
            ·
              refine ⟨3130793942308878678211351, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 267161083077024313874035285 3130793942308878678211351)
              ·
                refine ⟨4696190913463318017317027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3130793942308878678211351 4696190913463318017317027)
                ·
                  refine ⟨7044286370194977025975541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4696190913463318017317027 7044286370194977025975541)
                  ·
                    refine ⟨660401847205779096185207, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7044286370194977025975541 660401847205779096185207)
                    ·
                      rfl

theorem cell23_3858384_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 8, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 8, 1, 1, 5].length) (baseStart_3858384 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3858384 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3858384 prefixEnd_3858384 := by exact prefixLift 3858384
  have htrace : WordTrace (prefixWord ++ tailWord_3858384) baseStart_3858384 baseEnd_3858384 := by
    simpa [prefixWord, tailWord_3858384, baseEnd_3858384] using wordTrace_append hprefix tailTrace_3858384
  have hstable : (prefixWord ++ tailWord_3858384).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3858384).length < 2 ^ (prefixWord ++ tailWord_3858384).sum := by decide
  have hdescent : baseEnd_3858384 < baseStart_3858384 := by decide
  rcases family_descends (prefixWord ++ tailWord_3858384) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3858414 : List Nat := [4, 1, 2, 1, 3, 1, 3, 1, 1, 6]
def baseStart_3858414 : Nat := 118140960795 + 3858414 * 2 ^ 59
def prefixEnd_3858414 : Nat := 4983230072969 + 3 ^ 40 * 3858414 * 2
def baseEnd_3858414 : Nat := 660406982012324057060161

theorem tailTrace_3858414 : CollatzResearch.WordTrace tailWord_3858414 prefixEnd_3858414 660406982012324057060161 := by
  unfold tailWord_3858414
  simp only [CollatzResearch.WordTrace]
  refine ⟨17590989980454064686681787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 93818613229088344995636197 17590989980454064686681787)
  ·
    refine ⟨26386484970681097030022681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17590989980454064686681787 26386484970681097030022681)
    ·
      refine ⟨19789863728010822772517011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26386484970681097030022681 19789863728010822772517011)
      ·
        refine ⟨29684795592016234158775517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19789863728010822772517011 29684795592016234158775517)
        ·
          refine ⟨11131798347006087809540819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29684795592016234158775517 11131798347006087809540819)
          ·
            refine ⟨16697697520509131714311229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11131798347006087809540819 16697697520509131714311229)
            ·
              refine ⟨6261636570190924392866711, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16697697520509131714311229 6261636570190924392866711)
              ·
                refine ⟨9392454855286386589300067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6261636570190924392866711 9392454855286386589300067)
                ·
                  refine ⟨14088682282929579883950101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9392454855286386589300067 14088682282929579883950101)
                  ·
                    refine ⟨660406982012324057060161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 14088682282929579883950101 660406982012324057060161)
                    ·
                      rfl

theorem cell23_3858414_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 1, 3, 1, 1, 6].length) (baseStart_3858414 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3858414 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3858414 prefixEnd_3858414 := by exact prefixLift 3858414
  have htrace : WordTrace (prefixWord ++ tailWord_3858414) baseStart_3858414 baseEnd_3858414 := by
    simpa [prefixWord, tailWord_3858414, baseEnd_3858414] using wordTrace_append hprefix tailTrace_3858414
  have hstable : (prefixWord ++ tailWord_3858414).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3858414).length < 2 ^ (prefixWord ++ tailWord_3858414).sum := by decide
  have hdescent : baseEnd_3858414 < baseStart_3858414 := by decide
  rcases family_descends (prefixWord ++ tailWord_3858414) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3858424 : List Nat := [2, 1, 2, 1, 1, 3, 3, 4, 1, 2, 3]
def baseStart_3858424 : Nat := 118140960795 + 3858424 * 2 ^ 59
def prefixEnd_3858424 : Nat := 4983230072969 + 3 ^ 40 * 3858424 * 2
def baseEnd_3858424 : Nat := 1981226080843517132055437

theorem tailTrace_3858424 : CollatzResearch.WordTrace tailWord_3858424 prefixEnd_3858424 1981226080843517132055437 := by
  unfold tailWord_3858424
  simp only [CollatzResearch.WordTrace]
  refine ⟨70364142286798144600659163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93818856382397526134212217 70364142286798144600659163)
  ·
    refine ⟨105546213430197216900988745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70364142286798144600659163 105546213430197216900988745)
    ·
      refine ⟨79159660072647912675741559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 105546213430197216900988745 79159660072647912675741559)
      ·
        refine ⟨118739490108971869013612339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79159660072647912675741559 118739490108971869013612339)
        ·
          refine ⟨178109235163457803520418509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 118739490108971869013612339 178109235163457803520418509)
          ·
            refine ⟨66790963186296676320156941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 178109235163457803520418509 66790963186296676320156941)
            ·
              refine ⟨25046611194861253620058853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 66790963186296676320156941 25046611194861253620058853)
              ·
                refine ⟨4696239599036485053761035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25046611194861253620058853 4696239599036485053761035)
                ·
                  refine ⟨7044359398554727580641553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4696239599036485053761035 7044359398554727580641553)
                  ·
                    refine ⟨5283269548916045685481165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7044359398554727580641553 5283269548916045685481165)
                    ·
                      refine ⟨1981226080843517132055437, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5283269548916045685481165 1981226080843517132055437)
                      ·
                        rfl

theorem cell23_3858424_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 3, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 3, 4, 1, 2, 3].length) (baseStart_3858424 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3858424 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3858424 prefixEnd_3858424 := by exact prefixLift 3858424
  have htrace : WordTrace (prefixWord ++ tailWord_3858424) baseStart_3858424 baseEnd_3858424 := by
    simpa [prefixWord, tailWord_3858424, baseEnd_3858424] using wordTrace_append hprefix tailTrace_3858424
  have hstable : (prefixWord ++ tailWord_3858424).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3858424).length < 2 ^ (prefixWord ++ tailWord_3858424).sum := by decide
  have hdescent : baseEnd_3858424 < baseStart_3858424 := by decide
  rcases family_descends (prefixWord ++ tailWord_3858424) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3858427 : List Nat := [1, 1, 1, 1, 1, 3, 8, 7]
def baseStart_3858427 : Nat := 118140960795 + 3858427 * 2 ^ 59
def prefixEnd_3858427 : Nat := 4983230072969 + 3 ^ 40 * 3858427 * 2
def baseEnd_3858427 : Nat := 73378800788351134085849

theorem tailTrace_3858427 : CollatzResearch.WordTrace tailWord_3858427 prefixEnd_3858427 73378800788351134085849 := by
  unfold tailWord_3858427
  simp only [CollatzResearch.WordTrace]
  refine ⟨140728393992585420713677535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93818929328390280475785023 140728393992585420713677535)
  ·
    refine ⟨211092590988878131070516303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140728393992585420713677535 211092590988878131070516303)
    ·
      refine ⟨316638886483317196605774455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 211092590988878131070516303 316638886483317196605774455)
      ·
        refine ⟨474958329724975794908661683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 316638886483317196605774455 474958329724975794908661683)
        ·
          refine ⟨712437494587463692362992525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 474958329724975794908661683 712437494587463692362992525)
          ·
            refine ⟨267164060470298884636122197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 712437494587463692362992525 267164060470298884636122197)
            ·
              refine ⟨3130828833636315054329557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 267164060470298884636122197 3130828833636315054329557)
              ·
                refine ⟨73378800788351134085849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3130828833636315054329557 73378800788351134085849)
                ·
                  rfl

theorem cell23_3858427_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 8, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 8, 7].length) (baseStart_3858427 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3858427 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3858427 prefixEnd_3858427 := by exact prefixLift 3858427
  have htrace : WordTrace (prefixWord ++ tailWord_3858427) baseStart_3858427 baseEnd_3858427 := by
    simpa [prefixWord, tailWord_3858427, baseEnd_3858427] using wordTrace_append hprefix tailTrace_3858427
  have hstable : (prefixWord ++ tailWord_3858427).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3858427).length < 2 ^ (prefixWord ++ tailWord_3858427).sum := by decide
  have hdescent : baseEnd_3858427 < baseStart_3858427 := by decide
  rcases family_descends (prefixWord ++ tailWord_3858427) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3858455 : List Nat := [1, 1, 3, 5, 2, 2, 1, 1, 3, 2, 2]
def baseStart_3858455 : Nat := 118140960795 + 3858455 * 2 ^ 59
def prefixEnd_3858455 : Nat := 4983230072969 + 3 ^ 40 * 3858455 * 2
def baseEnd_3858455 : Nat := 1981241998743806510767795

theorem tailTrace_3858455 : CollatzResearch.WordTrace tailWord_3858455 prefixEnd_3858455 1981241998743806510767795 := by
  unfold tailWord_3858455
  simp only [CollatzResearch.WordTrace]
  refine ⟨140729415236483981495696819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93819610157655987663797879 140729415236483981495696819)
  ·
    refine ⟨211094122854725972243545229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140729415236483981495696819 211094122854725972243545229)
    ·
      refine ⟨79160296070522239591329461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 211094122854725972243545229 79160296070522239591329461)
      ·
        refine ⟨7421277756611459961687137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 79160296070522239591329461 7421277756611459961687137)
        ·
          refine ⟨5565958317458594971265353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7421277756611459961687137 5565958317458594971265353)
          ·
            refine ⟨4174468738093946228449015, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5565958317458594971265353 4174468738093946228449015)
            ·
              refine ⟨6261703107140919342673523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4174468738093946228449015 6261703107140919342673523)
              ·
                refine ⟨9392554660711379014010285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6261703107140919342673523 9392554660711379014010285)
                ·
                  refine ⟨3522207997766767130253857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9392554660711379014010285 3522207997766767130253857)
                  ·
                    refine ⟨2641655998325075347690393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3522207997766767130253857 2641655998325075347690393)
                    ·
                      refine ⟨1981241998743806510767795, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2641655998325075347690393 1981241998743806510767795)
                      ·
                        rfl

theorem cell23_3858455_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 2, 2, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 2, 2, 1, 1, 3, 2, 2].length) (baseStart_3858455 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3858455 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3858455 prefixEnd_3858455 := by exact prefixLift 3858455
  have htrace : WordTrace (prefixWord ++ tailWord_3858455) baseStart_3858455 baseEnd_3858455 := by
    simpa [prefixWord, tailWord_3858455, baseEnd_3858455] using wordTrace_append hprefix tailTrace_3858455
  have hstable : (prefixWord ++ tailWord_3858455).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3858455).length < 2 ^ (prefixWord ++ tailWord_3858455).sum := by decide
  have hdescent : baseEnd_3858455 < baseStart_3858455 := by decide
  rcases family_descends (prefixWord ++ tailWord_3858455) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3858465 : List Nat := [1, 2, 3, 2, 5, 1, 2, 1, 2, 4]
def baseStart_3858465 : Nat := 118140960795 + 3858465 * 2 ^ 59
def prefixEnd_3858465 : Nat := 4983230072969 + 3 ^ 40 * 3858465 * 2
def baseEnd_3858465 : Nat := 660415711183450490547583

theorem tailTrace_3858465 : CollatzResearch.WordTrace tailWord_3858465 prefixEnd_3858465 660415711183450490547583 := by
  unfold tailWord_3858465
  simp only [CollatzResearch.WordTrace]
  refine ⟨140729779966447753203560849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93819853310965168802373899 140729779966447753203560849)
  ·
    refine ⟨105547334974835814902670637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 140729779966447753203560849 105547334974835814902670637)
    ·
      refine ⟨39580250615563430588501489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 105547334974835814902670637 39580250615563430588501489)
      ·
        refine ⟨29685187961672572941376117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39580250615563430588501489 29685187961672572941376117)
        ·
          refine ⟨2782986371406803713254011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 29685187961672572941376117 2782986371406803713254011)
          ·
            refine ⟨4174479557110205569881017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2782986371406803713254011 4174479557110205569881017)
            ·
              refine ⟨3130859667832654177410763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4174479557110205569881017 3130859667832654177410763)
              ·
                refine ⟨4696289501748981266116145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3130859667832654177410763 4696289501748981266116145)
                ·
                  refine ⟨3522217126311735949587109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4696289501748981266116145 3522217126311735949587109)
                  ·
                    refine ⟨660415711183450490547583, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3522217126311735949587109 660415711183450490547583)
                    ·
                      rfl

theorem cell23_3858465_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 5, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 5, 1, 2, 1, 2, 4].length) (baseStart_3858465 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3858465 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3858465 prefixEnd_3858465 := by exact prefixLift 3858465
  have htrace : WordTrace (prefixWord ++ tailWord_3858465) baseStart_3858465 baseEnd_3858465 := by
    simpa [prefixWord, tailWord_3858465, baseEnd_3858465] using wordTrace_append hprefix tailTrace_3858465
  have hstable : (prefixWord ++ tailWord_3858465).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3858465).length < 2 ^ (prefixWord ++ tailWord_3858465).sum := by decide
  have hdescent : baseEnd_3858465 < baseStart_3858465 := by decide
  rcases family_descends (prefixWord ++ tailWord_3858465) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3858481 : List Nat := [1, 2, 2, 3, 1, 4, 1, 1, 3, 3, 2]
def baseStart_3858481 : Nat := 118140960795 + 3858481 * 2 ^ 59
def prefixEnd_3858481 : Nat := 4983230072969 + 3 ^ 40 * 3858481 * 2
def baseEnd_3858481 : Nat := 1981255349240823409042675

theorem tailTrace_3858481 : CollatzResearch.WordTrace tailWord_3858481 prefixEnd_3858481 1981255349240823409042675 := by
  unfold tailWord_3858481
  simp only [CollatzResearch.WordTrace]
  refine ⟨140730363534389787936143297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93820242356259858624095531 140730363534389787936143297)
  ·
    refine ⟨105547772650792340952107473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 140730363534389787936143297 105547772650792340952107473)
    ·
      refine ⟨79160829488094255714080605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 105547772650792340952107473 79160829488094255714080605)
      ·
        refine ⟨29685311058035345892780227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 79160829488094255714080605 29685311058035345892780227)
        ·
          refine ⟨44527966587053018839170341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29685311058035345892780227 44527966587053018839170341)
          ·
            refine ⟨8348993735072441032344439, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 44527966587053018839170341 8348993735072441032344439)
            ·
              refine ⟨12523490602608661548516659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8348993735072441032344439 12523490602608661548516659)
              ·
                refine ⟨18785235903912992322774989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12523490602608661548516659 18785235903912992322774989)
                ·
                  refine ⟨7044463463967372121040621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18785235903912992322774989 7044463463967372121040621)
                  ·
                    refine ⟨2641673798987764545390233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7044463463967372121040621 2641673798987764545390233)
                    ·
                      refine ⟨1981255349240823409042675, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2641673798987764545390233 1981255349240823409042675)
                      ·
                        rfl

theorem cell23_3858481_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 4, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 4, 1, 1, 3, 3, 2].length) (baseStart_3858481 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3858481 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3858481 prefixEnd_3858481 := by exact prefixLift 3858481
  have htrace : WordTrace (prefixWord ++ tailWord_3858481) baseStart_3858481 baseEnd_3858481 := by
    simpa [prefixWord, tailWord_3858481, baseEnd_3858481] using wordTrace_append hprefix tailTrace_3858481
  have hstable : (prefixWord ++ tailWord_3858481).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3858481).length < 2 ^ (prefixWord ++ tailWord_3858481).sum := by decide
  have hdescent : baseEnd_3858481 < baseStart_3858481 := by decide
  rcases family_descends (prefixWord ++ tailWord_3858481) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3858507 : List Nat := [1, 1, 1, 1, 3, 1, 2, 3, 4, 2, 4]
def baseStart_3858507 : Nat := 118140960795 + 3858507 * 2 ^ 59
def prefixEnd_3858507 : Nat := 4983230072969 + 3 ^ 40 * 3858507 * 2
def baseEnd_3858507 : Nat := 1981268699737840307317555

theorem tailTrace_3858507 : CollatzResearch.WordTrace tailWord_3858507 prefixEnd_3858507 1981268699737840307317555 := by
  unfold tailWord_3858507
  simp only [CollatzResearch.WordTrace]
  refine ⟨140731311832295594376589775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93820874554863729584393183 140731311832295594376589775)
  ·
    refine ⟨211096967748443391564884663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140731311832295594376589775 211096967748443391564884663)
    ·
      refine ⟨316645451622665087347326995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 211096967748443391564884663 316645451622665087347326995)
      ·
        refine ⟨474968177433997631020990493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 316645451622665087347326995 474968177433997631020990493)
        ·
          refine ⟨178113066537749111632871435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 474968177433997631020990493 178113066537749111632871435)
          ·
            refine ⟨267169599806623667449307153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 178113066537749111632871435 267169599806623667449307153)
            ·
              refine ⟨200377199854967750586980365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 267169599806623667449307153 200377199854967750586980365)
              ·
                refine ⟨75141449945612906470117637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 200377199854967750586980365 75141449945612906470117637)
                ·
                  refine ⟨14089021864802419963147057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 75141449945612906470117637 14089021864802419963147057)
                  ·
                    refine ⟨10566766398601814972360293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14089021864802419963147057 10566766398601814972360293)
                    ·
                      refine ⟨1981268699737840307317555, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10566766398601814972360293 1981268699737840307317555)
                      ·
                        rfl

theorem cell23_3858507_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 2, 3, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 2, 3, 4, 2, 4].length) (baseStart_3858507 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3858507 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3858507 prefixEnd_3858507 := by exact prefixLift 3858507
  have htrace : WordTrace (prefixWord ++ tailWord_3858507) baseStart_3858507 baseEnd_3858507 := by
    simpa [prefixWord, tailWord_3858507, baseEnd_3858507] using wordTrace_append hprefix tailTrace_3858507
  have hstable : (prefixWord ++ tailWord_3858507).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3858507).length < 2 ^ (prefixWord ++ tailWord_3858507).sum := by decide
  have hdescent : baseEnd_3858507 < baseStart_3858507 := by decide
  rcases family_descends (prefixWord ++ tailWord_3858507) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3858524 : List Nat := [2, 2, 4, 1, 1, 2, 1, 1, 1, 4, 4]
def baseStart_3858524 : Nat := 118140960795 + 3858524 * 2 ^ 59
def prefixEnd_3858524 : Nat := 4983230072969 + 3 ^ 40 * 3858524 * 2
def baseEnd_3858524 : Nat := 1981277428908966740804977

theorem tailTrace_3858524 : CollatzResearch.WordTrace tailWord_3858524 prefixEnd_3858524 1981277428908966740804977 := by
  unfold tailWord_3858524
  simp only [CollatzResearch.WordTrace]
  refine ⟨70365965936617003139979313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93821287915489337519972417 70365965936617003139979313)
  ·
    refine ⟨52774474452462752354984485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70365965936617003139979313 52774474452462752354984485)
    ·
      refine ⟨9895213959836766066559591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 52774474452462752354984485 9895213959836766066559591)
      ·
        refine ⟨14842820939755149099839387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9895213959836766066559591 14842820939755149099839387)
        ·
          refine ⟨22264231409632723649759081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14842820939755149099839387 22264231409632723649759081)
          ·
            refine ⟨16698173557224542737319311, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22264231409632723649759081 16698173557224542737319311)
            ·
              refine ⟨25047260335836814105978967, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16698173557224542737319311 25047260335836814105978967)
              ·
                refine ⟨37570890503755221158968451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25047260335836814105978967 37570890503755221158968451)
                ·
                  refine ⟨56356335755632831738452677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37570890503755221158968451 56356335755632831738452677)
                  ·
                    refine ⟨10566812954181155950959877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 56356335755632831738452677 10566812954181155950959877)
                    ·
                      refine ⟨1981277428908966740804977, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10566812954181155950959877 1981277428908966740804977)
                      ·
                        rfl

theorem cell23_3858524_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 2, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 2, 1, 1, 1, 4, 4].length) (baseStart_3858524 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3858524 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3858524 prefixEnd_3858524 := by exact prefixLift 3858524
  have htrace : WordTrace (prefixWord ++ tailWord_3858524) baseStart_3858524 baseEnd_3858524 := by
    simpa [prefixWord, tailWord_3858524, baseEnd_3858524] using wordTrace_append hprefix tailTrace_3858524
  have hstable : (prefixWord ++ tailWord_3858524).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3858524).length < 2 ^ (prefixWord ++ tailWord_3858524).sum := by decide
  have hdescent : baseEnd_3858524 < baseStart_3858524 := by decide
  rcases family_descends (prefixWord ++ tailWord_3858524) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3858528 : List Nat := [2, 1, 1, 3, 2, 3, 2, 3, 2, 2, 2]
def baseStart_3858528 : Nat := 118140960795 + 3858528 * 2 ^ 59
def prefixEnd_3858528 : Nat := 4983230072969 + 3 ^ 40 * 3858528 * 2
def baseEnd_3858528 : Nat := 1981279482831584725154959

theorem tailTrace_3858528 : CollatzResearch.WordTrace tailWord_3858528 prefixEnd_3858528 1981279482831584725154959 := by
  unfold tailWord_3858528
  simp only [CollatzResearch.WordTrace]
  refine ⟨70366038882609757481552119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93821385176813009975402825 70366038882609757481552119)
  ·
    refine ⟨105549058323914636222328179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70366038882609757481552119 105549058323914636222328179)
    ·
      refine ⟨158323587485871954333492269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105549058323914636222328179 158323587485871954333492269)
      ·
        refine ⟨59371345307201982875059601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 158323587485871954333492269 59371345307201982875059601)
        ·
          refine ⟨44528508980401487156294701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59371345307201982875059601 44528508980401487156294701)
          ·
            refine ⟨16698190867650557683610513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 44528508980401487156294701 16698190867650557683610513)
            ·
              refine ⟨12523643150737918262707885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16698190867650557683610513 12523643150737918262707885)
              ·
                refine ⟨4696366181526719348515457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12523643150737918262707885 4696366181526719348515457)
                ·
                  refine ⟨3522274636145039511386593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4696366181526719348515457 3522274636145039511386593)
                  ·
                    refine ⟨2641705977108779633539945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3522274636145039511386593 2641705977108779633539945)
                    ·
                      refine ⟨1981279482831584725154959, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2641705977108779633539945 1981279482831584725154959)
                      ·
                        rfl

theorem cell23_3858528_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 3, 2, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 3, 2, 3, 2, 2, 2].length) (baseStart_3858528 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3858528 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3858528 prefixEnd_3858528 := by exact prefixLift 3858528
  have htrace : WordTrace (prefixWord ++ tailWord_3858528) baseStart_3858528 baseEnd_3858528 := by
    simpa [prefixWord, tailWord_3858528, baseEnd_3858528] using wordTrace_append hprefix tailTrace_3858528
  have hstable : (prefixWord ++ tailWord_3858528).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3858528).length < 2 ^ (prefixWord ++ tailWord_3858528).sum := by decide
  have hdescent : baseEnd_3858528 < baseStart_3858528 := by decide
  rcases family_descends (prefixWord ++ tailWord_3858528) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3858551 : List Nat := [1, 1, 3, 1, 1, 6, 2, 3, 5]
def baseStart_3858551 : Nat := 118140960795 + 3858551 * 2 ^ 59
def prefixEnd_3858551 : Nat := 4983230072969 + 3 ^ 40 * 3858551 * 2
def baseEnd_3858551 : Nat := 220143476987404237240817

theorem tailTrace_3858551 : CollatzResearch.WordTrace tailWord_3858551 prefixEnd_3858551 220143476987404237240817 := by
  unfold tailWord_3858551
  simp only [CollatzResearch.WordTrace]
  refine ⟨140732916644136189891191507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93821944429424126594127671 140732916644136189891191507)
  ·
    refine ⟨211099374966204284836787261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140732916644136189891191507 211099374966204284836787261)
    ·
      refine ⟨79162265612326606813795223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 211099374966204284836787261 79162265612326606813795223)
      ·
        refine ⟨118743398418489910220692835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79162265612326606813795223 118743398418489910220692835)
        ·
          refine ⟨178115097627734865331039253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 118743398418489910220692835 178115097627734865331039253)
          ·
            refine ⟨8349145201300071812392465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 178115097627734865331039253 8349145201300071812392465)
            ·
              refine ⟨6261858900975053859294349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8349145201300071812392465 6261858900975053859294349)
              ·
                refine ⟨2348197087865645197235381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6261858900975053859294349 2348197087865645197235381)
                ·
                  refine ⟨220143476987404237240817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2348197087865645197235381 220143476987404237240817)
                  ·
                    rfl

theorem cell23_3858551_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 6, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 6, 2, 3, 5].length) (baseStart_3858551 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3858551 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3858551 prefixEnd_3858551 := by exact prefixLift 3858551
  have htrace : WordTrace (prefixWord ++ tailWord_3858551) baseStart_3858551 baseEnd_3858551 := by
    simpa [prefixWord, tailWord_3858551, baseEnd_3858551] using wordTrace_append hprefix tailTrace_3858551
  have hstable : (prefixWord ++ tailWord_3858551).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3858551).length < 2 ^ (prefixWord ++ tailWord_3858551).sum := by decide
  have hdescent : baseEnd_3858551 < baseStart_3858551 := by decide
  rcases family_descends (prefixWord ++ tailWord_3858551) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3858564 : List Nat := [2, 3, 2, 1, 2, 1, 2, 1, 4, 5]
def baseStart_3858564 : Nat := 118140960795 + 3858564 * 2 ^ 59
def prefixEnd_3858564 : Nat := 4983230072969 + 3 ^ 40 * 3858564 * 2
def baseEnd_3858564 : Nat := 660432656045048861434931

theorem tailTrace_3858564 : CollatzResearch.WordTrace tailWord_3858564 prefixEnd_3858564 660432656045048861434931 := by
  unfold tailWord_3858564
  simp only [CollatzResearch.WordTrace]
  refine ⟨70366695396544546555707373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93822260528726062074276497 70366695396544546555707373)
  ·
    refine ⟨26387510773704204958390265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 70366695396544546555707373 26387510773704204958390265)
    ·
      refine ⟨19790633080278153718792699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26387510773704204958390265 19790633080278153718792699)
      ·
        refine ⟨29685949620417230578189049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19790633080278153718792699 29685949620417230578189049)
        ·
          refine ⟨22264462215312922933641787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29685949620417230578189049 22264462215312922933641787)
          ·
            refine ⟨33396693322969384400462681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22264462215312922933641787 33396693322969384400462681)
            ·
              refine ⟨25047519992227038300347011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33396693322969384400462681 25047519992227038300347011)
              ·
                refine ⟨37571279988340557450520517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25047519992227038300347011 37571279988340557450520517)
                ·
                  refine ⟨7044614997813854521972597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 37571279988340557450520517 7044614997813854521972597)
                  ·
                    refine ⟨660432656045048861434931, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7044614997813854521972597 660432656045048861434931)
                    ·
                      rfl

theorem cell23_3858564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 2, 1, 4, 5].length) (baseStart_3858564 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3858564 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3858564 prefixEnd_3858564 := by exact prefixLift 3858564
  have htrace : WordTrace (prefixWord ++ tailWord_3858564) baseStart_3858564 baseEnd_3858564 := by
    simpa [prefixWord, tailWord_3858564, baseEnd_3858564] using wordTrace_append hprefix tailTrace_3858564
  have hstable : (prefixWord ++ tailWord_3858564).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3858564).length < 2 ^ (prefixWord ++ tailWord_3858564).sum := by decide
  have hdescent : baseEnd_3858564 < baseStart_3858564 := by decide
  rcases family_descends (prefixWord ++ tailWord_3858564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3858587 : List Nat := [1, 1, 1, 1, 1, 1, 2, 4, 1, 5, 5]
def baseStart_3858587 : Nat := 118140960795 + 3858587 * 2 ^ 59
def prefixEnd_3858587 : Nat := 4983230072969 + 3 ^ 40 * 3858587 * 2
def baseEnd_3858587 : Nat := 1981309778190199994317187

theorem tailTrace_3858587 : CollatzResearch.WordTrace tailWord_3858587 prefixEnd_3858587 1981309778190199994317187 := by
  unfold tailWord_3858587
  simp only [CollatzResearch.WordTrace]
  refine ⟨140734229672005768039502015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93822819781337178693001343 140734229672005768039502015)
  ·
    refine ⟨211101344508008652059253023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140734229672005768039502015 211101344508008652059253023)
    ·
      refine ⟨316652016762012978088879535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 211101344508008652059253023 316652016762012978088879535)
      ·
        refine ⟨474978025143019467133319303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 316652016762012978088879535 474978025143019467133319303)
        ·
          refine ⟨712467037714529200699978955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 474978025143019467133319303 712467037714529200699978955)
          ·
            refine ⟨1068700556571793801049968433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 712467037714529200699978955 1068700556571793801049968433)
            ·
              refine ⟨801525417428845350787476325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1068700556571793801049968433 801525417428845350787476325)
              ·
                refine ⟨150286015767908503272651811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 801525417428845350787476325 150286015767908503272651811)
                ·
                  refine ⟨225429023651862754908977717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 150286015767908503272651811 225429023651862754908977717)
                  ·
                    refine ⟨21133970967362133272716661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 225429023651862754908977717 21133970967362133272716661)
                    ·
                      refine ⟨1981309778190199994317187, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 21133970967362133272716661 1981309778190199994317187)
                      ·
                        rfl

theorem cell23_3858587_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 4, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 4, 1, 5, 5].length) (baseStart_3858587 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3858587 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3858587 prefixEnd_3858587 := by exact prefixLift 3858587
  have htrace : WordTrace (prefixWord ++ tailWord_3858587) baseStart_3858587 baseEnd_3858587 := by
    simpa [prefixWord, tailWord_3858587, baseEnd_3858587] using wordTrace_append hprefix tailTrace_3858587
  have hstable : (prefixWord ++ tailWord_3858587).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3858587).length < 2 ^ (prefixWord ++ tailWord_3858587).sum := by decide
  have hdescent : baseEnd_3858587 < baseStart_3858587 := by decide
  rcases family_descends (prefixWord ++ tailWord_3858587) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3858602 : List Nat := [3, 1, 5, 1, 3, 1, 1, 3, 5]
def baseStart_3858602 : Nat := 118140960795 + 3858602 * 2 ^ 59
def prefixEnd_3858602 : Nat := 4983230072969 + 3 ^ 40 * 3858602 * 2
def baseEnd_3858602 : Nat := 220146386711113048403291

theorem tailTrace_3858602 : CollatzResearch.WordTrace tailWord_3858602 prefixEnd_3858602 220146386711113048403291 := by
  unfold tailWord_3858602
  simp only [CollatzResearch.WordTrace]
  refine ⟨35183694191737856400324515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 93823184511300950400865373 35183694191737856400324515)
  ·
    refine ⟨52775541287606784600486773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35183694191737856400324515 52775541287606784600486773)
    ·
      refine ⟨4947706995713136056295635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 52775541287606784600486773 4947706995713136056295635)
      ·
        refine ⟨7421560493569704084443453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4947706995713136056295635 7421560493569704084443453)
        ·
          refine ⟨2783085185088639031666295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7421560493569704084443453 2783085185088639031666295)
          ·
            refine ⟨4174627777632958547499443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2783085185088639031666295 4174627777632958547499443)
            ·
              refine ⟨6261941666449437821249165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4174627777632958547499443 6261941666449437821249165)
              ·
                refine ⟨2348228124918539182968437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6261941666449437821249165 2348228124918539182968437)
                ·
                  refine ⟨220146386711113048403291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2348228124918539182968437 220146386711113048403291)
                  ·
                    rfl

theorem cell23_3858602_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 3, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 3, 1, 1, 3, 5].length) (baseStart_3858602 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3858602 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3858602 prefixEnd_3858602 := by exact prefixLift 3858602
  have htrace : WordTrace (prefixWord ++ tailWord_3858602) baseStart_3858602 baseEnd_3858602 := by
    simpa [prefixWord, tailWord_3858602, baseEnd_3858602] using wordTrace_append hprefix tailTrace_3858602
  have hstable : (prefixWord ++ tailWord_3858602).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3858602).length < 2 ^ (prefixWord ++ tailWord_3858602).sum := by decide
  have hdescent : baseEnd_3858602 < baseStart_3858602 := by decide
  rcases family_descends (prefixWord ++ tailWord_3858602) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3858624 : List Nat := [2, 1, 1, 2, 5, 1, 2, 1, 8]
def baseStart_3858624 : Nat := 118140960795 + 3858624 * 2 ^ 59
def prefixEnd_3858624 : Nat := 4983230072969 + 3 ^ 40 * 3858624 * 2
def baseEnd_3858624 : Nat := 220147641886046261061613

theorem tailTrace_3858624 : CollatzResearch.WordTrace tailWord_3858624 prefixEnd_3858624 220147641886046261061613 := by
  unfold tailWord_3858624
  simp only [CollatzResearch.WordTrace]
  refine ⟨70367789586435861679299463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93823719448581148905732617 70367789586435861679299463)
  ·
    refine ⟨105551684379653792518949195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70367789586435861679299463 105551684379653792518949195)
    ·
      refine ⟨158327526569480688778423793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105551684379653792518949195 158327526569480688778423793)
      ·
        refine ⟨118745644927110516583817845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 158327526569480688778423793 118745644927110516583817845)
        ·
          refine ⟨11132404211916610929732923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 118745644927110516583817845 11132404211916610929732923)
          ·
            refine ⟨16698606317874916394599385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11132404211916610929732923 16698606317874916394599385)
            ·
              refine ⟨12523954738406187295949539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16698606317874916394599385 12523954738406187295949539)
              ·
                refine ⟨18785932107609280943924309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12523954738406187295949539 18785932107609280943924309)
                ·
                  refine ⟨220147641886046261061613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 18785932107609280943924309 220147641886046261061613)
                  ·
                    rfl

theorem cell23_3858624_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 1, 2, 1, 8].length) (baseStart_3858624 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3858624 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3858624 prefixEnd_3858624 := by exact prefixLift 3858624
  have htrace : WordTrace (prefixWord ++ tailWord_3858624) baseStart_3858624 baseEnd_3858624 := by
    simpa [prefixWord, tailWord_3858624, baseEnd_3858624] using wordTrace_append hprefix tailTrace_3858624
  have hstable : (prefixWord ++ tailWord_3858624).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3858624).length < 2 ^ (prefixWord ++ tailWord_3858624).sum := by decide
  have hdescent : baseEnd_3858624 < baseStart_3858624 := by decide
  rcases family_descends (prefixWord ++ tailWord_3858624) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3858628 : List Nat := [2, 3, 3, 1, 2, 1, 3, 1, 3, 4]
def baseStart_3858628 : Nat := 118140960795 + 3858628 * 2 ^ 59
def prefixEnd_3858628 : Nat := 4983230072969 + 3 ^ 40 * 3858628 * 2
def baseEnd_3858628 : Nat := 660443610299011444634833

theorem tailTrace_3858628 : CollatzResearch.WordTrace tailWord_3858628 prefixEnd_3858628 660443610299011444634833 := by
  unfold tailWord_3858628
  simp only [CollatzResearch.WordTrace]
  refine ⟨70367862532428616020872269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93823816709904821361163025 70367862532428616020872269)
  ·
    refine ⟨26387948449660731007827101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 70367862532428616020872269 26387948449660731007827101)
    ·
      refine ⟨9895480668622774127935163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26387948449660731007827101 9895480668622774127935163)
      ·
        refine ⟨14843221002934161191902745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9895480668622774127935163 14843221002934161191902745)
        ·
          refine ⟨11132415752200620893927059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14843221002934161191902745 11132415752200620893927059)
          ·
            refine ⟨16698623628300931340890589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11132415752200620893927059 16698623628300931340890589)
            ·
              refine ⟨6261983860612849252833971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16698623628300931340890589 6261983860612849252833971)
              ·
                refine ⟨9392975790919273879250957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6261983860612849252833971 9392975790919273879250957)
                ·
                  refine ⟨3522365921594727704719109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9392975790919273879250957 3522365921594727704719109)
                  ·
                    refine ⟨660443610299011444634833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3522365921594727704719109 660443610299011444634833)
                    ·
                      rfl

theorem cell23_3858628_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 1, 3, 1, 3, 4].length) (baseStart_3858628 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3858628 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3858628 prefixEnd_3858628 := by exact prefixLift 3858628
  have htrace : WordTrace (prefixWord ++ tailWord_3858628) baseStart_3858628 baseEnd_3858628 := by
    simpa [prefixWord, tailWord_3858628, baseEnd_3858628] using wordTrace_append hprefix tailTrace_3858628
  have hstable : (prefixWord ++ tailWord_3858628).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3858628).length < 2 ^ (prefixWord ++ tailWord_3858628).sum := by decide
  have hdescent : baseEnd_3858628 < baseStart_3858628 := by decide
  rcases family_descends (prefixWord ++ tailWord_3858628) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3858641 : List Nat := [1, 2, 2, 1, 2, 2, 6, 1, 6]
def baseStart_3858641 : Nat := 118140960795 + 3858641 * 2 ^ 59
def prefixEnd_3858641 : Nat := 4983230072969 + 3 ^ 40 * 3858641 * 2
def baseEnd_3858641 : Nat := 220148611793949198115771

theorem tailTrace_3858641 : CollatzResearch.WordTrace tailWord_3858641 prefixEnd_3858641 220148611793949198115771 := by
  unfold tailWord_3858641
  simp only [CollatzResearch.WordTrace]
  refine ⟨140736199213810135261967777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93824132809206756841311851 140736199213810135261967777)
  ·
    refine ⟨105552149410357601446475833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 140736199213810135261967777 105552149410357601446475833)
    ·
      refine ⟨79164112057768201084856875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 105552149410357601446475833 79164112057768201084856875)
      ·
        refine ⟨118746168086652301627285313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79164112057768201084856875 118746168086652301627285313)
        ·
          refine ⟨89059626064989226220463985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 118746168086652301627285313 89059626064989226220463985)
          ·
            refine ⟨66794719548741919665347989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 89059626064989226220463985 66794719548741919665347989)
            ·
              refine ⟨3131002478847277484313187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 66794719548741919665347989 3131002478847277484313187)
              ·
                refine ⟨4696503718270916226469781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3131002478847277484313187 4696503718270916226469781)
                ·
                  refine ⟨220148611793949198115771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4696503718270916226469781 220148611793949198115771)
                  ·
                    rfl

theorem cell23_3858641_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 6, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 6, 1, 6].length) (baseStart_3858641 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3858641 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3858641 prefixEnd_3858641 := by exact prefixLift 3858641
  have htrace : WordTrace (prefixWord ++ tailWord_3858641) baseStart_3858641 baseEnd_3858641 := by
    simpa [prefixWord, tailWord_3858641, baseEnd_3858641] using wordTrace_append hprefix tailTrace_3858641
  have hstable : (prefixWord ++ tailWord_3858641).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3858641).length < 2 ^ (prefixWord ++ tailWord_3858641).sum := by decide
  have hdescent : baseEnd_3858641 < baseStart_3858641 := by decide
  rcases family_descends (prefixWord ++ tailWord_3858641) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3858721 : List Nat := [1, 2, 3, 2, 1, 1, 4, 2, 1, 2, 4]
def baseStart_3858721 : Nat := 118140960795 + 3858721 * 2 ^ 59
def prefixEnd_3858721 : Nat := 4983230072969 + 3 ^ 40 * 3858721 * 2
def baseEnd_3858721 : Nat := 1981378584597902470041571

theorem tailTrace_3858721 : CollatzResearch.WordTrace tailWord_3858721 prefixEnd_3858721 1981378584597902470041571 := by
  unfold tailWord_3858721
  simp only [CollatzResearch.WordTrace]
  refine ⟨140739117053520308924880017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93826078035680205949920011 140739117053520308924880017)
  ·
    refine ⟨105554337790140231693660013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 140739117053520308924880017 105554337790140231693660013)
    ·
      refine ⟨39582876671302586885122505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 105554337790140231693660013 39582876671302586885122505)
      ·
        refine ⟨29687157503476940163841879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39582876671302586885122505 29687157503476940163841879)
        ·
          refine ⟨44530736255215410245762819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29687157503476940163841879 44530736255215410245762819)
          ·
            refine ⟨66796104382823115368644229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44530736255215410245762819 66796104382823115368644229)
            ·
              refine ⟨12524269571779334131620793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 66796104382823115368644229 12524269571779334131620793)
              ·
                refine ⟨9393202178834500598715595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12524269571779334131620793 9393202178834500598715595)
                ·
                  refine ⟨14089803268251750898073393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9393202178834500598715595 14089803268251750898073393)
                  ·
                    refine ⟨10567352451188813173555045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14089803268251750898073393 10567352451188813173555045)
                    ·
                      refine ⟨1981378584597902470041571, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10567352451188813173555045 1981378584597902470041571)
                      ·
                        rfl

theorem cell23_3858721_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 4, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 4, 2, 1, 2, 4].length) (baseStart_3858721 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3858721 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3858721 prefixEnd_3858721 := by exact prefixLift 3858721
  have htrace : WordTrace (prefixWord ++ tailWord_3858721) baseStart_3858721 baseEnd_3858721 := by
    simpa [prefixWord, tailWord_3858721, baseEnd_3858721] using wordTrace_append hprefix tailTrace_3858721
  have hstable : (prefixWord ++ tailWord_3858721).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3858721).length < 2 ^ (prefixWord ++ tailWord_3858721).sum := by decide
  have hdescent : baseEnd_3858721 < baseStart_3858721 := by decide
  rcases family_descends (prefixWord ++ tailWord_3858721) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3858744 : List Nat := [2, 1, 2, 1, 3, 1, 2, 1, 1, 9]
def baseStart_3858744 : Nat := 118140960795 + 3858744 * 2 ^ 59
def prefixEnd_3858744 : Nat := 4983230072969 + 3 ^ 40 * 3858744 * 2
def baseEnd_3858744 : Nat := 660463464884318626684655

theorem tailTrace_3858744 : CollatzResearch.WordTrace tailWord_3858744 prefixEnd_3858744 660463464884318626684655 := by
  unfold tailWord_3858744
  simp only [CollatzResearch.WordTrace]
  refine ⟨70369977966218491926483643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93826637288291322568644857 70369977966218491926483643)
  ·
    refine ⟨105554966949327737889725465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70369977966218491926483643 105554966949327737889725465)
    ·
      refine ⟨79166225211995803417294099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 105554966949327737889725465 79166225211995803417294099)
      ·
        refine ⟨118749337817993705125941149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79166225211995803417294099 118749337817993705125941149)
        ·
          refine ⟨44531001681747639422227931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 118749337817993705125941149 44531001681747639422227931)
          ·
            refine ⟨66796502522621459133341897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44531001681747639422227931 66796502522621459133341897)
            ·
              refine ⟨50097376891966094350006423, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 66796502522621459133341897 50097376891966094350006423)
              ·
                refine ⟨75146065337949141525009635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50097376891966094350006423 75146065337949141525009635)
                ·
                  refine ⟨112719098006923712287514453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 75146065337949141525009635 112719098006923712287514453)
                  ·
                    refine ⟨660463464884318626684655, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 112719098006923712287514453 660463464884318626684655)
                    ·
                      rfl

theorem cell23_3858744_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 2, 1, 1, 9].length) (baseStart_3858744 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3858744 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3858744 prefixEnd_3858744 := by exact prefixLift 3858744
  have htrace : WordTrace (prefixWord ++ tailWord_3858744) baseStart_3858744 baseEnd_3858744 := by
    simpa [prefixWord, tailWord_3858744, baseEnd_3858744] using wordTrace_append hprefix tailTrace_3858744
  have hstable : (prefixWord ++ tailWord_3858744).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3858744).length < 2 ^ (prefixWord ++ tailWord_3858744).sum := by decide
  have hdescent : baseEnd_3858744 < baseStart_3858744 := by decide
  rcases family_descends (prefixWord ++ tailWord_3858744) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3858801 : List Nat := [1, 2, 2, 2, 1, 2, 1, 3, 2, 4, 3]
def baseStart_3858801 : Nat := 118140960795 + 3858801 * 2 ^ 59
def prefixEnd_3858801 : Nat := 4983230072969 + 3 ^ 40 * 3858801 * 2
def baseEnd_3858801 : Nat := 1981419663050262157041203

theorem tailTrace_3858801 : CollatzResearch.WordTrace tailWord_3858801 prefixEnd_3858801 1981419663050262157041203 := by
  unfold tailWord_3858801
  simp only [CollatzResearch.WordTrace]
  refine ⟨140742034893230482587792257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93828023262153655058528171 140742034893230482587792257)
  ·
    refine ⟨105556526169922861940844193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 140742034893230482587792257 105556526169922861940844193)
    ·
      refine ⟨79167394627442146455633145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 105556526169922861940844193 79167394627442146455633145)
      ·
        refine ⟨59375545970581609841724859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 79167394627442146455633145 59375545970581609841724859)
        ·
          refine ⟨89063318955872414762587289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59375545970581609841724859 89063318955872414762587289)
          ·
            refine ⟨66797489216904311071940467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 89063318955872414762587289 66797489216904311071940467)
            ·
              refine ⟨100196233825356466607910701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 66797489216904311071940467 100196233825356466607910701)
              ·
                refine ⟨37573587684508674977966513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 100196233825356466607910701 37573587684508674977966513)
                ·
                  refine ⟨28180190763381506233474885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 37573587684508674977966513 28180190763381506233474885)
                  ·
                    refine ⟨5283785768134032418776541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 28180190763381506233474885 5283785768134032418776541)
                    ·
                      refine ⟨1981419663050262157041203, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5283785768134032418776541 1981419663050262157041203)
                      ·
                        rfl

theorem cell23_3858801_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 1, 3, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 1, 3, 2, 4, 3].length) (baseStart_3858801 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3858801 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3858801 prefixEnd_3858801 := by exact prefixLift 3858801
  have htrace : WordTrace (prefixWord ++ tailWord_3858801) baseStart_3858801 baseEnd_3858801 := by
    simpa [prefixWord, tailWord_3858801, baseEnd_3858801] using wordTrace_append hprefix tailTrace_3858801
  have hstable : (prefixWord ++ tailWord_3858801).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3858801).length < 2 ^ (prefixWord ++ tailWord_3858801).sum := by decide
  have hdescent : baseEnd_3858801 < baseStart_3858801 := by decide
  rcases family_descends (prefixWord ++ tailWord_3858801) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3858815 : List Nat := [1, 1, 2, 2, 1, 1, 2, 7, 2, 2, 2]
def baseStart_3858815 : Nat := 118140960795 + 3858815 * 2 ^ 59
def prefixEnd_3858815 : Nat := 4983230072969 + 3 ^ 40 * 3858815 * 2
def baseEnd_3858815 : Nat := 1981426851779425102266139

theorem tailTrace_3858815 : CollatzResearch.WordTrace tailWord_3858815 prefixEnd_3858815 1981426851779425102266139 := by
  unfold tailWord_3858815
  simp only [CollatzResearch.WordTrace]
  refine ⟨140742545515179762978801899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93828363676786508652534599 140742545515179762978801899)
  ·
    refine ⟨211113818272769644468202849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140742545515179762978801899 211113818272769644468202849)
    ·
      refine ⟨158335363704577233351152137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 211113818272769644468202849 158335363704577233351152137)
      ·
        refine ⟨118751522778432925013364103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 158335363704577233351152137 118751522778432925013364103)
        ·
          refine ⟨178127284167649387520046155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 118751522778432925013364103 178127284167649387520046155)
          ·
            refine ⟨267190926251474081280069233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 178127284167649387520046155 267190926251474081280069233)
            ·
              refine ⟨200393194688605560960051925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 267190926251474081280069233 200393194688605560960051925)
              ·
                refine ⟨4696715500514192835001217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 200393194688605560960051925 4696715500514192835001217)
                ·
                  refine ⟨3522536625385644626250913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4696715500514192835001217 3522536625385644626250913)
                  ·
                    refine ⟨2641902469039233469688185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3522536625385644626250913 2641902469039233469688185)
                    ·
                      refine ⟨1981426851779425102266139, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2641902469039233469688185 1981426851779425102266139)
                      ·
                        rfl

theorem cell23_3858815_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 2, 7, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 2, 7, 2, 2, 2].length) (baseStart_3858815 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3858815 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3858815 prefixEnd_3858815 := by exact prefixLift 3858815
  have htrace : WordTrace (prefixWord ++ tailWord_3858815) baseStart_3858815 baseEnd_3858815 := by
    simpa [prefixWord, tailWord_3858815, baseEnd_3858815] using wordTrace_append hprefix tailTrace_3858815
  have hstable : (prefixWord ++ tailWord_3858815).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3858815).length < 2 ^ (prefixWord ++ tailWord_3858815).sum := by decide
  have hdescent : baseEnd_3858815 < baseStart_3858815 := by decide
  rcases family_descends (prefixWord ++ tailWord_3858815) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3858819 : List Nat := [1, 1, 1, 3, 7, 1, 1, 2, 1, 3, 2]
def baseStart_3858819 : Nat := 118140960795 + 3858819 * 2 ^ 59
def prefixEnd_3858819 : Nat := 4983230072969 + 3 ^ 40 * 3858819 * 2
def baseEnd_3858819 : Nat := 1981428905702043086616121

theorem tailTrace_3858819 : CollatzResearch.WordTrace tailWord_3858819 prefixEnd_3858819 1981428905702043086616121 := by
  unfold tailWord_3858819
  simp only [CollatzResearch.WordTrace]
  refine ⟨140742691407165271661947511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93828460938110181107965007 140742691407165271661947511)
  ·
    refine ⟨211114037110747907492921267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140742691407165271661947511 211114037110747907492921267)
    ·
      refine ⟨316671055666121861239381901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 211114037110747907492921267 316671055666121861239381901)
      ·
        refine ⟨118751645874795697964768213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 316671055666121861239381901 118751645874795697964768213)
        ·
          refine ⟨2783241700190524171049255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 118751645874795697964768213 2783241700190524171049255)
          ·
            refine ⟨4174862550285786256573883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2783241700190524171049255 4174862550285786256573883)
            ·
              refine ⟨6262293825428679384860825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4174862550285786256573883 6262293825428679384860825)
              ·
                refine ⟨4696720369071509538645619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6262293825428679384860825 4696720369071509538645619)
                ·
                  refine ⟨7045080553607264307968429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4696720369071509538645619 7045080553607264307968429)
                  ·
                    refine ⟨2641905207602724115488161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7045080553607264307968429 2641905207602724115488161)
                    ·
                      refine ⟨1981428905702043086616121, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2641905207602724115488161 1981428905702043086616121)
                      ·
                        rfl

theorem cell23_3858819_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 7, 1, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 7, 1, 1, 2, 1, 3, 2].length) (baseStart_3858819 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3858819 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3858819 prefixEnd_3858819 := by exact prefixLift 3858819
  have htrace : WordTrace (prefixWord ++ tailWord_3858819) baseStart_3858819 baseEnd_3858819 := by
    simpa [prefixWord, tailWord_3858819, baseEnd_3858819] using wordTrace_append hprefix tailTrace_3858819
  have hstable : (prefixWord ++ tailWord_3858819).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3858819).length < 2 ^ (prefixWord ++ tailWord_3858819).sum := by decide
  have hdescent : baseEnd_3858819 < baseStart_3858819 := by decide
  rcases family_descends (prefixWord ++ tailWord_3858819) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3858855 : List Nat := [1, 1, 6, 1, 1, 3, 1, 4, 5]
def baseStart_3858855 : Nat := 118140960795 + 3858855 * 2 ^ 59
def prefixEnd_3858855 : Nat := 4983230072969 + 3 ^ 40 * 3858855 * 2
def baseEnd_3858855 : Nat := 220160821222844993973995

theorem tailTrace_3858855 : CollatzResearch.WordTrace tailWord_3858855 prefixEnd_3858855 220160821222844993973995 := by
  unfold tailWord_3858855
  simp only [CollatzResearch.WordTrace]
  refine ⟨140744004435034849810258019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93829336290023233206838679 140744004435034849810258019)
  ·
    refine ⟨211116006652552274715387029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140744004435034849810258019 211116006652552274715387029)
    ·
      refine ⟨9896062811838387877283767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 211116006652552274715387029 9896062811838387877283767)
      ·
        refine ⟨14844094217757581815925651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9896062811838387877283767 14844094217757581815925651)
        ·
          refine ⟨22266141326636372723888477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14844094217757581815925651 22266141326636372723888477)
          ·
            refine ⟨8349802997488639771458179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22266141326636372723888477 8349802997488639771458179)
            ·
              refine ⟨12524704496232959657187269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8349802997488639771458179 12524704496232959657187269)
              ·
                refine ⟨2348382093043679935722613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12524704496232959657187269 2348382093043679935722613)
                ·
                  refine ⟨220160821222844993973995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2348382093043679935722613 220160821222844993973995)
                  ·
                    rfl

theorem cell23_3858855_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 3, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 3, 1, 4, 5].length) (baseStart_3858855 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3858855 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3858855 prefixEnd_3858855 := by exact prefixLift 3858855
  have htrace : WordTrace (prefixWord ++ tailWord_3858855) baseStart_3858855 baseEnd_3858855 := by
    simpa [prefixWord, tailWord_3858855, baseEnd_3858855] using wordTrace_append hprefix tailTrace_3858855
  have hstable : (prefixWord ++ tailWord_3858855).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3858855).length < 2 ^ (prefixWord ++ tailWord_3858855).sum := by decide
  have hdescent : baseEnd_3858855 < baseStart_3858855 := by decide
  rcases family_descends (prefixWord ++ tailWord_3858855) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3858888 : List Nat := [2, 1, 3, 1, 3, 3, 1, 1, 1, 3, 4]
def baseStart_3858888 : Nat := 118140960795 + 3858888 * 2 ^ 59
def prefixEnd_3858888 : Nat := 4983230072969 + 3 ^ 40 * 3858888 * 2
def baseEnd_3858888 : Nat := 1981464335867203316653303

theorem tailTrace_3858888 : CollatzResearch.WordTrace tailWord_3858888 prefixEnd_3858888 1981464335867203316653303 := by
  unfold tailWord_3858888
  simp only [CollatzResearch.WordTrace]
  refine ⟨70372604021957648223104659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93830138695943530964139545 70372604021957648223104659)
  ·
    refine ⟨105558906032936472334656989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70372604021957648223104659 105558906032936472334656989)
    ·
      refine ⟨39584589762351177125496371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 105558906032936472334656989 39584589762351177125496371)
      ·
        refine ⟨59376884643526765688244557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39584589762351177125496371 59376884643526765688244557)
        ·
          refine ⟨22266331741322537133091709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 59376884643526765688244557 22266331741322537133091709)
          ·
            refine ⟨8349874402995951424909391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22266331741322537133091709 8349874402995951424909391)
            ·
              refine ⟨12524811604493927137364087, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8349874402995951424909391 12524811604493927137364087)
              ·
                refine ⟨18787217406740890706046131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12524811604493927137364087 18787217406740890706046131)
                ·
                  refine ⟨28180826110111336059069197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18787217406740890706046131 28180826110111336059069197)
                  ·
                    refine ⟨10567809791291751022150949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 28180826110111336059069197 10567809791291751022150949)
                    ·
                      refine ⟨1981464335867203316653303, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10567809791291751022150949 1981464335867203316653303)
                      ·
                        rfl

theorem cell23_3858888_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 3, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 3, 1, 1, 1, 3, 4].length) (baseStart_3858888 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3858888 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3858888 prefixEnd_3858888 := by exact prefixLift 3858888
  have htrace : WordTrace (prefixWord ++ tailWord_3858888) baseStart_3858888 baseEnd_3858888 := by
    simpa [prefixWord, tailWord_3858888, baseEnd_3858888] using wordTrace_append hprefix tailTrace_3858888
  have hstable : (prefixWord ++ tailWord_3858888).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3858888).length < 2 ^ (prefixWord ++ tailWord_3858888).sum := by decide
  have hdescent : baseEnd_3858888 < baseStart_3858888 := by decide
  rcases family_descends (prefixWord ++ tailWord_3858888) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3858925 : List Nat := [1, 5, 1, 3, 1, 1, 1, 2, 1, 4, 3]
def baseStart_3858925 : Nat := 118140960795 + 3858925 * 2 ^ 59
def prefixEnd_3858925 : Nat := 4983230072969 + 3 ^ 40 * 3858925 * 2
def baseEnd_3858925 : Nat := 1981483334651419671890633

theorem tailTrace_3858925 : CollatzResearch.WordTrace tailWord_3858925 prefixEnd_3858925 1981483334651419671890633 := by
  unfold tailWord_3858925
  simp only [CollatzResearch.WordTrace]
  refine ⟨140746557544781251765306229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93831038363187501176870819 140746557544781251765306229)
  ·
    refine ⟨13194989769823242352997459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 140746557544781251765306229 13194989769823242352997459)
    ·
      refine ⟨19792484654734863529496189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13194989769823242352997459 19792484654734863529496189)
      ·
        refine ⟨7422181745525573823561071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19792484654734863529496189 7422181745525573823561071)
        ·
          refine ⟨11133272618288360735341607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7422181745525573823561071 11133272618288360735341607)
          ·
            refine ⟨16699908927432541103012411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11133272618288360735341607 16699908927432541103012411)
            ·
              refine ⟨25049863391148811654518617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16699908927432541103012411 25049863391148811654518617)
              ·
                refine ⟨18787397543361608740888963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25049863391148811654518617 18787397543361608740888963)
                ·
                  refine ⟨28181096315042413111333445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18787397543361608740888963 28181096315042413111333445)
                  ·
                    refine ⟨5283955559070452458375021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 28181096315042413111333445 5283955559070452458375021)
                    ·
                      refine ⟨1981483334651419671890633, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5283955559070452458375021 1981483334651419671890633)
                      ·
                        rfl

theorem cell23_3858925_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 1, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 1, 1, 2, 1, 4, 3].length) (baseStart_3858925 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3858925 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3858925 prefixEnd_3858925 := by exact prefixLift 3858925
  have htrace : WordTrace (prefixWord ++ tailWord_3858925) baseStart_3858925 baseEnd_3858925 := by
    simpa [prefixWord, tailWord_3858925, baseEnd_3858925] using wordTrace_append hprefix tailTrace_3858925
  have hstable : (prefixWord ++ tailWord_3858925).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3858925).length < 2 ^ (prefixWord ++ tailWord_3858925).sum := by decide
  have hdescent : baseEnd_3858925 < baseStart_3858925 := by decide
  rcases family_descends (prefixWord ++ tailWord_3858925) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3858931 : List Nat := [1, 1, 1, 2, 2, 2, 3, 2, 1, 2, 6]
def baseStart_3858931 : Nat := 118140960795 + 3858931 * 2 ^ 59
def prefixEnd_3858931 : Nat := 4983230072969 + 3 ^ 40 * 3858931 * 2
def baseEnd_3858931 : Nat := 1981486415535346648415605

theorem tailTrace_3858931 : CollatzResearch.WordTrace tailWord_3858931 prefixEnd_3858931 1981486415535346648415605 := by
  unfold tailWord_3858931
  simp only [CollatzResearch.WordTrace]
  refine ⟨140746776382759514790024647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93831184255173009860016431 140746776382759514790024647)
  ·
    refine ⟨211120164574139272185036971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140746776382759514790024647 211120164574139272185036971)
    ·
      refine ⟨316680246861208908277555457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 211120164574139272185036971 316680246861208908277555457)
      ·
        refine ⟨237510185145906681208166593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 316680246861208908277555457 237510185145906681208166593)
        ·
          refine ⟨178132638859430010906124945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 237510185145906681208166593 178132638859430010906124945)
          ·
            refine ⟨133599479144572508179593709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 178132638859430010906124945 133599479144572508179593709)
            ·
              refine ⟨50099804679214690567347641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 133599479144572508179593709 50099804679214690567347641)
              ·
                refine ⟨37574853509411017925510731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 50099804679214690567347641 37574853509411017925510731)
                ·
                  refine ⟨56362280264116526888266097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37574853509411017925510731 56362280264116526888266097)
                  ·
                    refine ⟨42271710198087395166199573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 56362280264116526888266097 42271710198087395166199573)
                    ·
                      refine ⟨1981486415535346648415605, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 42271710198087395166199573 1981486415535346648415605)
                      ·
                        rfl

theorem cell23_3858931_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 3, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 3, 2, 1, 2, 6].length) (baseStart_3858931 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3858931 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3858931 prefixEnd_3858931 := by exact prefixLift 3858931
  have htrace : WordTrace (prefixWord ++ tailWord_3858931) baseStart_3858931 baseEnd_3858931 := by
    simpa [prefixWord, tailWord_3858931, baseEnd_3858931] using wordTrace_append hprefix tailTrace_3858931
  have hstable : (prefixWord ++ tailWord_3858931).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3858931).length < 2 ^ (prefixWord ++ tailWord_3858931).sum := by decide
  have hdescent : baseEnd_3858931 < baseStart_3858931 := by decide
  rcases family_descends (prefixWord ++ tailWord_3858931) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3858972 : List Nat := [2, 2, 3, 1, 2, 2, 3, 1, 3, 1, 3]
def baseStart_3858972 : Nat := 118140960795 + 3858972 * 2 ^ 59
def prefixEnd_3858972 : Nat := 4983230072969 + 3 ^ 40 * 3858972 * 2
def baseEnd_3858972 : Nat := 1981507468242180988002917

theorem tailTrace_3858972 : CollatzResearch.WordTrace tailWord_3858972 prefixEnd_3858972 1981507468242180988002917 := by
  unfold tailWord_3858972
  simp only [CollatzResearch.WordTrace]
  refine ⟨70374135887805489396133585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93832181183740652528178113 70374135887805489396133585)
  ·
    refine ⟨52780601915854117047100189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70374135887805489396133585 52780601915854117047100189)
    ·
      refine ⟨19792725718445293892662571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 52780601915854117047100189 19792725718445293892662571)
      ·
        refine ⟨29689088577667940838993857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19792725718445293892662571 29689088577667940838993857)
        ·
          refine ⟨22266816433250955629245393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29689088577667940838993857 22266816433250955629245393)
          ·
            refine ⟨16700112324938216721934045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22266816433250955629245393 16700112324938216721934045)
            ·
              refine ⟨6262542121851831270725267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16700112324938216721934045 6262542121851831270725267)
              ·
                refine ⟨9393813182777746906087901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6262542121851831270725267 9393813182777746906087901)
                ·
                  refine ⟨3522679943541655089782963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9393813182777746906087901 3522679943541655089782963)
                  ·
                    refine ⟨5284019915312482634674445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3522679943541655089782963 5284019915312482634674445)
                    ·
                      refine ⟨1981507468242180988002917, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5284019915312482634674445 1981507468242180988002917)
                      ·
                        rfl

theorem cell23_3858972_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 2, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 2, 3, 1, 3, 1, 3].length) (baseStart_3858972 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3858972 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3858972 prefixEnd_3858972 := by exact prefixLift 3858972
  have htrace : WordTrace (prefixWord ++ tailWord_3858972) baseStart_3858972 baseEnd_3858972 := by
    simpa [prefixWord, tailWord_3858972, baseEnd_3858972] using wordTrace_append hprefix tailTrace_3858972
  have hstable : (prefixWord ++ tailWord_3858972).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3858972).length < 2 ^ (prefixWord ++ tailWord_3858972).sum := by decide
  have hdescent : baseEnd_3858972 < baseStart_3858972 := by decide
  rcases family_descends (prefixWord ++ tailWord_3858972) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3858978 : List Nat := [3, 3, 1, 1, 1, 1, 1, 1, 2, 5, 4]
def baseStart_3858978 : Nat := 118140960795 + 3858978 * 2 ^ 59
def prefixEnd_3858978 : Nat := 4983230072969 + 3 ^ 40 * 3858978 * 2
def baseEnd_3858978 : Nat := 1981510549126107964527889

theorem tailTrace_3858978 : CollatzResearch.WordTrace tailWord_3858978 prefixEnd_3858978 1981510549126107964527889 := by
  unfold tailWord_3858978
  simp only [CollatzResearch.WordTrace]
  refine ⟨35187122653397310454246397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 93832327075726161211323725 35187122653397310454246397)
  ·
    refine ⟨13195170995023991420342399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 35187122653397310454246397 13195170995023991420342399)
    ·
      refine ⟨19792756492535987130513599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13195170995023991420342399 19792756492535987130513599)
      ·
        refine ⟨29689134738803980695770399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19792756492535987130513599 29689134738803980695770399)
        ·
          refine ⟨44533702108205971043655599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29689134738803980695770399 44533702108205971043655599)
          ·
            refine ⟨66800553162308956565483399, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44533702108205971043655599 66800553162308956565483399)
            ·
              refine ⟨100200829743463434848225099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 66800553162308956565483399 100200829743463434848225099)
              ·
                refine ⟨150301244615195152272337649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 100200829743463434848225099 150301244615195152272337649)
                ·
                  refine ⟨112725933461396364204253237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 150301244615195152272337649 112725933461396364204253237)
                  ·
                    refine ⟨10568056262005909144148741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 112725933461396364204253237 10568056262005909144148741)
                    ·
                      refine ⟨1981510549126107964527889, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10568056262005909144148741 1981510549126107964527889)
                      ·
                        rfl

theorem cell23_3858978_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 1, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 1, 1, 2, 5, 4].length) (baseStart_3858978 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3858978 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3858978 prefixEnd_3858978 := by exact prefixLift 3858978
  have htrace : WordTrace (prefixWord ++ tailWord_3858978) baseStart_3858978 baseEnd_3858978 := by
    simpa [prefixWord, tailWord_3858978, baseEnd_3858978] using wordTrace_append hprefix tailTrace_3858978
  have hstable : (prefixWord ++ tailWord_3858978).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3858978).length < 2 ^ (prefixWord ++ tailWord_3858978).sum := by decide
  have hdescent : baseEnd_3858978 < baseStart_3858978 := by decide
  rcases family_descends (prefixWord ++ tailWord_3858978) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3859005 : List Nat := [1, 4, 1, 3, 2, 2, 1, 2, 1, 6]
def baseStart_3859005 : Nat := 118140960795 + 3859005 * 2 ^ 59
def prefixEnd_3859005 : Nat := 4983230072969 + 3 ^ 40 * 3859005 * 2
def baseEnd_3859005 : Nat := 660508137701259786296755

theorem tailTrace_3859005 : CollatzResearch.WordTrace tailWord_3859005 prefixEnd_3859005 660508137701259786296755 := by
  unfold tailWord_3859005
  simp only [CollatzResearch.WordTrace]
  refine ⟨140749475384491425428218469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93832983589660950285478979 140749475384491425428218469)
  ·
    refine ⟨26390526634592142267790963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 140749475384491425428218469 26390526634592142267790963)
    ·
      refine ⟨39585789951888213401686445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26390526634592142267790963 39585789951888213401686445)
      ·
        refine ⟨14844671231958080025632417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 39585789951888213401686445 14844671231958080025632417)
        ·
          refine ⟨11133503423968560019224313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14844671231958080025632417 11133503423968560019224313)
          ·
            refine ⟨8350127567976420014418235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11133503423968560019224313 8350127567976420014418235)
            ·
              refine ⟨12525191351964630021627353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8350127567976420014418235 12525191351964630021627353)
              ·
                refine ⟨9393893513973472516220515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12525191351964630021627353 9393893513973472516220515)
                ·
                  refine ⟨14090840270960208774330773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9393893513973472516220515 14090840270960208774330773)
                  ·
                    refine ⟨660508137701259786296755, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 14090840270960208774330773 660508137701259786296755)
                    ·
                      rfl

theorem cell23_3859005_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 2, 1, 2, 1, 6].length) (baseStart_3859005 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3859005 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3859005 prefixEnd_3859005 := by exact prefixLift 3859005
  have htrace : WordTrace (prefixWord ++ tailWord_3859005) baseStart_3859005 baseEnd_3859005 := by
    simpa [prefixWord, tailWord_3859005, baseEnd_3859005] using wordTrace_append hprefix tailTrace_3859005
  have hstable : (prefixWord ++ tailWord_3859005).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3859005).length < 2 ^ (prefixWord ++ tailWord_3859005).sum := by decide
  have hdescent : baseEnd_3859005 < baseStart_3859005 := by decide
  rcases family_descends (prefixWord ++ tailWord_3859005) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3859008 : List Nat := [2, 1, 1, 2, 2, 2, 3, 1, 3, 2, 4]
def baseStart_3859008 : Nat := 118140960795 + 3859008 * 2 ^ 59
def prefixEnd_3859008 : Nat := 4983230072969 + 3 ^ 40 * 3859008 * 2
def baseEnd_3859008 : Nat := 1981525953545742847152751

theorem tailTrace_3859008 : CollatzResearch.WordTrace tailWord_3859008 prefixEnd_3859008 1981525953545742847152751 := by
  unfold tailWord_3859008
  simp only [CollatzResearch.WordTrace]
  refine ⟨70374792401740278470288839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93833056535653704627051785 70374792401740278470288839)
  ·
    refine ⟨105562188602610417705433259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70374792401740278470288839 105562188602610417705433259)
    ·
      refine ⟨158343282903915626558149889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105562188602610417705433259 158343282903915626558149889)
      ·
        refine ⟨118757462177936719918612417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 158343282903915626558149889 118757462177936719918612417)
        ·
          refine ⟨89068096633452539938959313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 118757462177936719918612417 89068096633452539938959313)
          ·
            refine ⟨66801072475089404954219485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 89068096633452539938959313 66801072475089404954219485)
            ·
              refine ⟨25050402178158526857832307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 66801072475089404954219485 25050402178158526857832307)
              ·
                refine ⟨37575603267237790286748461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25050402178158526857832307 37575603267237790286748461)
                ·
                  refine ⟨14090851225214171357530673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 37575603267237790286748461 14090851225214171357530673)
                  ·
                    refine ⟨10568138418910628518148005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14090851225214171357530673 10568138418910628518148005)
                    ·
                      refine ⟨1981525953545742847152751, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10568138418910628518148005 1981525953545742847152751)
                      ·
                        rfl

theorem cell23_3859008_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 3, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 3, 1, 3, 2, 4].length) (baseStart_3859008 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3859008 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3859008 prefixEnd_3859008 := by exact prefixLift 3859008
  have htrace : WordTrace (prefixWord ++ tailWord_3859008) baseStart_3859008 baseEnd_3859008 := by
    simpa [prefixWord, tailWord_3859008, baseEnd_3859008] using wordTrace_append hprefix tailTrace_3859008
  have hstable : (prefixWord ++ tailWord_3859008).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3859008).length < 2 ^ (prefixWord ++ tailWord_3859008).sum := by decide
  have hdescent : baseEnd_3859008 < baseStart_3859008 := by decide
  rcases family_descends (prefixWord ++ tailWord_3859008) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3859015 : List Nat := [1, 1, 4, 1, 4, 1, 3, 1, 1, 1, 5]
def baseStart_3859015 : Nat := 118140960795 + 3859015 * 2 ^ 59
def prefixEnd_3859015 : Nat := 4983230072969 + 3 ^ 40 * 3859015 * 2
def baseEnd_3859015 : Nat := 1981529547910324319765219

theorem tailTrace_3859015 : CollatzResearch.WordTrace tailWord_3859015 prefixEnd_3859015 1981529547910324319765219 := by
  unfold tailWord_3859015
  simp only [CollatzResearch.WordTrace]
  refine ⟨140749840114455197136082499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93833226742970131424054999 140749840114455197136082499)
  ·
    refine ⟨211124760171682795704123749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140749840114455197136082499 211124760171682795704123749)
    ·
      refine ⟨39585892532190524194523203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 211124760171682795704123749 39585892532190524194523203)
      ·
        refine ⟨59378838798285786291784805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39585892532190524194523203 59378838798285786291784805)
        ·
          refine ⟨11133532274678584929709651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 59378838798285786291784805 11133532274678584929709651)
          ·
            refine ⟨16700298412017877394564477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11133532274678584929709651 16700298412017877394564477)
            ·
              refine ⟨6262611904506704022961679, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16700298412017877394564477 6262611904506704022961679)
              ·
                refine ⟨9393917856760056034442519, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6262611904506704022961679 9393917856760056034442519)
                ·
                  refine ⟨14090876785140084051663779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9393917856760056034442519 14090876785140084051663779)
                  ·
                    refine ⟨21136315177710126077495669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14090876785140084051663779 21136315177710126077495669)
                    ·
                      refine ⟨1981529547910324319765219, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 21136315177710126077495669 1981529547910324319765219)
                      ·
                        rfl

theorem cell23_3859015_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 1, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 1, 3, 1, 1, 1, 5].length) (baseStart_3859015 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3859015 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3859015 prefixEnd_3859015 := by exact prefixLift 3859015
  have htrace : WordTrace (prefixWord ++ tailWord_3859015) baseStart_3859015 baseEnd_3859015 := by
    simpa [prefixWord, tailWord_3859015, baseEnd_3859015] using wordTrace_append hprefix tailTrace_3859015
  have hstable : (prefixWord ++ tailWord_3859015).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3859015).length < 2 ^ (prefixWord ++ tailWord_3859015).sum := by decide
  have hdescent : baseEnd_3859015 < baseStart_3859015 := by decide
  rcases family_descends (prefixWord ++ tailWord_3859015) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3859088 : List Nat := [2, 1, 1, 1, 1, 1, 3, 1, 6, 1, 5]
def baseStart_3859088 : Nat := 118140960795 + 3859088 * 2 ^ 59
def prefixEnd_3859088 : Nat := 4983230072969 + 3 ^ 40 * 3859088 * 2
def baseEnd_3859088 : Nat := 1981567031998102534152383

theorem tailTrace_3859088 : CollatzResearch.WordTrace tailWord_3859088 prefixEnd_3859088 1981567031998102534152383 := by
  unfold tailWord_3859088
  simp only [CollatzResearch.WordTrace]
  refine ⟨70376251321595365301744959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93835001762127153735659945 70376251321595365301744959)
  ·
    refine ⟨105564376982393047952617439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70376251321595365301744959 105564376982393047952617439)
    ·
      refine ⟨158346565473589571928926159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105564376982393047952617439 158346565473589571928926159)
      ·
        refine ⟨237519848210384357893389239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 158346565473589571928926159 237519848210384357893389239)
        ·
          refine ⟨356279772315576536840083859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 237519848210384357893389239 356279772315576536840083859)
          ·
            refine ⟨534419658473364805260125789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 356279772315576536840083859 534419658473364805260125789)
            ·
              refine ⟨200407371927511801972547171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 534419658473364805260125789 200407371927511801972547171)
              ·
                refine ⟨300611057891267702958820757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 200407371927511801972547171 300611057891267702958820757)
                ·
                  refine ⟨14091143338653173576194723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 300611057891267702958820757 14091143338653173576194723)
                  ·
                    refine ⟨21136715007979760364292085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14091143338653173576194723 21136715007979760364292085)
                    ·
                      refine ⟨1981567031998102534152383, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 21136715007979760364292085 1981567031998102534152383)
                      ·
                        rfl

theorem cell23_3859088_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 3, 1, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 3, 1, 6, 1, 5].length) (baseStart_3859088 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3859088 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3859088 prefixEnd_3859088 := by exact prefixLift 3859088
  have htrace : WordTrace (prefixWord ++ tailWord_3859088) baseStart_3859088 baseEnd_3859088 := by
    simpa [prefixWord, tailWord_3859088, baseEnd_3859088] using wordTrace_append hprefix tailTrace_3859088
  have hstable : (prefixWord ++ tailWord_3859088).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3859088).length < 2 ^ (prefixWord ++ tailWord_3859088).sum := by decide
  have hdescent : baseEnd_3859088 < baseStart_3859088 := by decide
  rcases family_descends (prefixWord ++ tailWord_3859088) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3859128 : List Nat := [2, 1, 2, 1, 2, 1, 1, 1, 2, 4, 6]
def baseStart_3859128 : Nat := 118140960795 + 3859128 * 2 ^ 59
def prefixEnd_3859128 : Nat := 4983230072969 + 3 ^ 40 * 3859128 * 2
def baseEnd_3859128 : Nat := 1981587571224282377652199

theorem tailTrace_3859128 : CollatzResearch.WordTrace tailWord_3859128 prefixEnd_3859128 1981587571224282377652199 := by
  unfold tailWord_3859128
  simp only [CollatzResearch.WordTrace]
  refine ⟨70376980781522908717473019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93835974375363878289964025 70376980781522908717473019)
  ·
    refine ⟨105565471172284363076209529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70376980781522908717473019 105565471172284363076209529)
    ·
      refine ⟨79174103379213272307157147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 105565471172284363076209529 79174103379213272307157147)
      ·
        refine ⟨118761155068819908460735721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79174103379213272307157147 118761155068819908460735721)
        ·
          refine ⟨89070866301614931345551791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 118761155068819908460735721 89070866301614931345551791)
          ·
            refine ⟨133606299452422397018327687, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 89070866301614931345551791 133606299452422397018327687)
            ·
              refine ⟨200409449178633595527491531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 133606299452422397018327687 200409449178633595527491531)
              ·
                refine ⟨300614173767950393291237297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 200409449178633595527491531 300614173767950393291237297)
                ·
                  refine ⟨225460630325962794968427973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 300614173767950393291237297 225460630325962794968427973)
                  ·
                    refine ⟨42273868186118024056580245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 225460630325962794968427973 42273868186118024056580245)
                    ·
                      refine ⟨1981587571224282377652199, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 42273868186118024056580245 1981587571224282377652199)
                      ·
                        rfl

theorem cell23_3859128_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 1, 1, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 1, 1, 2, 4, 6].length) (baseStart_3859128 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3859128 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3859128 prefixEnd_3859128 := by exact prefixLift 3859128
  have htrace : WordTrace (prefixWord ++ tailWord_3859128) baseStart_3859128 baseEnd_3859128 := by
    simpa [prefixWord, tailWord_3859128, baseEnd_3859128] using wordTrace_append hprefix tailTrace_3859128
  have hstable : (prefixWord ++ tailWord_3859128).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3859128).length < 2 ^ (prefixWord ++ tailWord_3859128).sum := by decide
  have hdescent : baseEnd_3859128 < baseStart_3859128 := by decide
  rcases family_descends (prefixWord ++ tailWord_3859128) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3859172 : List Nat := [2, 3, 1, 1, 1, 5, 2, 1, 2, 5]
def baseStart_3859172 : Nat := 118140960795 + 3859172 * 2 ^ 59
def prefixEnd_3859172 : Nat := 4983230072969 + 3 ^ 40 * 3859172 * 2
def baseEnd_3859172 : Nat := 660536721457693401833999

theorem tailTrace_3859172 : CollatzResearch.WordTrace tailWord_3859172 prefixEnd_3859172 660536721457693401833999 := by
  unfold tailWord_3859172
  simp only [CollatzResearch.WordTrace]
  refine ⟨70377783187443206474773885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93837044249924275299698513 70377783187443206474773885)
  ·
    refine ⟨26391668695291202428040207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 70377783187443206474773885 26391668695291202428040207)
    ·
      refine ⟨39587503042936803642060311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26391668695291202428040207 39587503042936803642060311)
      ·
        refine ⟨59381254564405205463090467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39587503042936803642060311 59381254564405205463090467)
        ·
          refine ⟨89071881846607808194635701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59381254564405205463090467 89071881846607808194635701)
          ·
            refine ⟨8350488923119482018247097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 89071881846607808194635701 8350488923119482018247097)
            ·
              refine ⟨6262866692339611513685323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8350488923119482018247097 6262866692339611513685323)
              ·
                refine ⟨9394300038509417270527985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6262866692339611513685323 9394300038509417270527985)
                ·
                  refine ⟨7045725028882062952895989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9394300038509417270527985 7045725028882062952895989)
                  ·
                    refine ⟨660536721457693401833999, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7045725028882062952895989 660536721457693401833999)
                    ·
                      rfl

theorem cell23_3859172_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 5, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 5, 2, 1, 2, 5].length) (baseStart_3859172 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3859172 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3859172 prefixEnd_3859172 := by exact prefixLift 3859172
  have htrace : WordTrace (prefixWord ++ tailWord_3859172) baseStart_3859172 baseEnd_3859172 := by
    simpa [prefixWord, tailWord_3859172, baseEnd_3859172] using wordTrace_append hprefix tailTrace_3859172
  have hstable : (prefixWord ++ tailWord_3859172).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3859172).length < 2 ^ (prefixWord ++ tailWord_3859172).sum := by decide
  have hdescent : baseEnd_3859172 < baseStart_3859172 := by decide
  rcases family_descends (prefixWord ++ tailWord_3859172) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3859192 : List Nat := [2, 1, 2, 1, 1, 2, 4, 2, 2, 4, 2]
def baseStart_3859192 : Nat := 118140960795 + 3859192 * 2 ^ 59
def prefixEnd_3859192 : Nat := 4983230072969 + 3 ^ 40 * 3859192 * 2
def baseEnd_3859192 : Nat := 1981620433986170127251905

theorem tailTrace_3859192 : CollatzResearch.WordTrace tailWord_3859192 prefixEnd_3859192 1981620433986170127251905 := by
  unfold tailWord_3859192
  simp only [CollatzResearch.WordTrace]
  refine ⟨70378147917406978182637915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93837530556542637576850553 70378147917406978182637915)
  ·
    refine ⟨105567221876110467273956873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70378147917406978182637915 105567221876110467273956873)
    ·
      refine ⟨79175416407082850455467655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 105567221876110467273956873 79175416407082850455467655)
      ·
        refine ⟨118763124610624275683201483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79175416407082850455467655 118763124610624275683201483)
        ·
          refine ⟨178144686915936413524802225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 118763124610624275683201483 178144686915936413524802225)
          ·
            refine ⟨133608515186952310143601669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 178144686915936413524802225 133608515186952310143601669)
            ·
              refine ⟨25051596597553558151925313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 133608515186952310143601669 25051596597553558151925313)
              ·
                refine ⟨18788697448165168613943985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25051596597553558151925313 18788697448165168613943985)
                ·
                  refine ⟨14091523086123876460457989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18788697448165168613943985 14091523086123876460457989)
                  ·
                    refine ⟨2642160578648226836335873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 14091523086123876460457989 2642160578648226836335873)
                    ·
                      refine ⟨1981620433986170127251905, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2642160578648226836335873 1981620433986170127251905)
                      ·
                        rfl

theorem cell23_3859192_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 4, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 4, 2, 2, 4, 2].length) (baseStart_3859192 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3859192 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3859192 prefixEnd_3859192 := by exact prefixLift 3859192
  have htrace : WordTrace (prefixWord ++ tailWord_3859192) baseStart_3859192 baseEnd_3859192 := by
    simpa [prefixWord, tailWord_3859192, baseEnd_3859192] using wordTrace_append hprefix tailTrace_3859192
  have hstable : (prefixWord ++ tailWord_3859192).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3859192).length < 2 ^ (prefixWord ++ tailWord_3859192).sum := by decide
  have hdescent : baseEnd_3859192 < baseStart_3859192 := by decide
  rcases family_descends (prefixWord ++ tailWord_3859192) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3859215 : List Nat := [1, 1, 2, 1, 1, 1, 5, 5, 6]
def baseStart_3859215 : Nat := 118140960795 + 3859215 * 2 ^ 59
def prefixEnd_3859215 : Nat := 4983230072969 + 3 ^ 40 * 3859215 * 2
def baseEnd_3859215 : Nat := 220181360449024837473811

theorem tailTrace_3859215 : CollatzResearch.WordTrace tailWord_3859215 prefixEnd_3859215 220181360449024837473811 := by
  unfold tailWord_3859215
  simp only [CollatzResearch.WordTrace]
  refine ⟨140757134713730631293363099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93838089809153754195575399 140757134713730631293363099)
  ·
    refine ⟨211135702070595946940044649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140757134713730631293363099 211135702070595946940044649)
    ·
      refine ⟨158351776552946960205033487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 211135702070595946940044649 158351776552946960205033487)
      ·
        refine ⟨237527664829420440307550231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 158351776552946960205033487 237527664829420440307550231)
        ·
          refine ⟨356291497244130660461325347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 237527664829420440307550231 356291497244130660461325347)
          ·
            refine ⟨534437245866195990691988021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 356291497244130660461325347 534437245866195990691988021)
            ·
              refine ⟨50103491799955874127373877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 534437245866195990691988021 50103491799955874127373877)
              ·
                refine ⟨4697202356245863199441301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 50103491799955874127373877 4697202356245863199441301)
                ·
                  refine ⟨220181360449024837473811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4697202356245863199441301 220181360449024837473811)
                  ·
                    rfl

theorem cell23_3859215_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 5, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 5, 5, 6].length) (baseStart_3859215 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3859215 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3859215 prefixEnd_3859215 := by exact prefixLift 3859215
  have htrace : WordTrace (prefixWord ++ tailWord_3859215) baseStart_3859215 baseEnd_3859215 := by
    simpa [prefixWord, tailWord_3859215, baseEnd_3859215] using wordTrace_append hprefix tailTrace_3859215
  have hstable : (prefixWord ++ tailWord_3859215).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3859215).length < 2 ^ (prefixWord ++ tailWord_3859215).sum := by decide
  have hdescent : baseEnd_3859215 < baseStart_3859215 := by decide
  rcases family_descends (prefixWord ++ tailWord_3859215) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3859225 : List Nat := [1, 2, 1, 2, 1, 1, 1, 3, 1, 7, 3]
def baseStart_3859225 : Nat := 118140960795 + 3859225 * 2 ^ 59
def prefixEnd_3859225 : Nat := 4983230072969 + 3 ^ 40 * 3859225 * 2
def baseEnd_3859225 : Nat := 1981637378847768498139253

theorem tailTrace_3859225 : CollatzResearch.WordTrace tailWord_3859225 prefixEnd_3859225 1981637378847768498139253 := by
  unfold tailWord_3859225
  simp only [CollatzResearch.WordTrace]
  refine ⟨140757499443694403001227129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93838332962462935334151419 140757499443694403001227129)
  ·
    refine ⟨105568124582770802250920347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 140757499443694403001227129 105568124582770802250920347)
    ·
      refine ⟨158352186874156203376380521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105568124582770802250920347 158352186874156203376380521)
      ·
        refine ⟨118764140155617152532285391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 158352186874156203376380521 118764140155617152532285391)
        ·
          refine ⟨178146210233425728798428087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 118764140155617152532285391 178146210233425728798428087)
          ·
            refine ⟨267219315350138593197642131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 178146210233425728798428087 267219315350138593197642131)
            ·
              refine ⟨400828973025207889796463197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 267219315350138593197642131 400828973025207889796463197)
              ·
                refine ⟨150310864884452958673673699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 400828973025207889796463197 150310864884452958673673699)
                ·
                  refine ⟨225466297326679438010510549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 150310864884452958673673699 225466297326679438010510549)
                  ·
                    refine ⟨5284366343594049328371341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 225466297326679438010510549 5284366343594049328371341)
                    ·
                      refine ⟨1981637378847768498139253, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5284366343594049328371341 1981637378847768498139253)
                      ·
                        rfl

theorem cell23_3859225_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 3, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 3, 1, 7, 3].length) (baseStart_3859225 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3859225 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3859225 prefixEnd_3859225 := by exact prefixLift 3859225
  have htrace : WordTrace (prefixWord ++ tailWord_3859225) baseStart_3859225 baseEnd_3859225 := by
    simpa [prefixWord, tailWord_3859225, baseEnd_3859225] using wordTrace_append hprefix tailTrace_3859225
  have hstable : (prefixWord ++ tailWord_3859225).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3859225).length < 2 ^ (prefixWord ++ tailWord_3859225).sum := by decide
  have hdescent : baseEnd_3859225 < baseStart_3859225 := by decide
  rcases family_descends (prefixWord ++ tailWord_3859225) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3859299 : List Nat := [1, 1, 1, 5, 3, 1, 2, 3, 1, 1, 4]
def baseStart_3859299 : Nat := 118140960795 + 3859299 * 2 ^ 59
def prefixEnd_3859299 : Nat := 4983230072969 + 3 ^ 40 * 3859299 * 2
def baseEnd_3859299 : Nat := 1981675376416201208613913

theorem tailTrace_3859299 : CollatzResearch.WordTrace tailWord_3859299 prefixEnd_3859299 1981675376416201208613913 := by
  unfold tailWord_3859299
  simp only [CollatzResearch.WordTrace]
  refine ⟨140760198445426313639420951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93840132296950875759613967 140760198445426313639420951)
  ·
    refine ⟨211140297668139470459131427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140760198445426313639420951 211140297668139470459131427)
    ·
      refine ⟨316710446502209205688697141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 211140297668139470459131427 316710446502209205688697141)
      ·
        refine ⟨29691604359582113033315357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 316710446502209205688697141 29691604359582113033315357)
        ·
          refine ⟨11134351634843292387493259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29691604359582113033315357 11134351634843292387493259)
          ·
            refine ⟨16701527452264938581239889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11134351634843292387493259 16701527452264938581239889)
            ·
              refine ⟨12526145589198703935929917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16701527452264938581239889 12526145589198703935929917)
              ·
                refine ⟨4697304595949513975973719, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12526145589198703935929917 4697304595949513975973719)
                ·
                  refine ⟨7045956893924270963960579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4697304595949513975973719 7045956893924270963960579)
                  ·
                    refine ⟨10568935340886406445940869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7045956893924270963960579 10568935340886406445940869)
                    ·
                      refine ⟨1981675376416201208613913, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10568935340886406445940869 1981675376416201208613913)
                      ·
                        rfl

theorem cell23_3859299_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 1, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 1, 2, 3, 1, 1, 4].length) (baseStart_3859299 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3859299 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3859299 prefixEnd_3859299 := by exact prefixLift 3859299
  have htrace : WordTrace (prefixWord ++ tailWord_3859299) baseStart_3859299 baseEnd_3859299 := by
    simpa [prefixWord, tailWord_3859299, baseEnd_3859299] using wordTrace_append hprefix tailTrace_3859299
  have hstable : (prefixWord ++ tailWord_3859299).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3859299).length < 2 ^ (prefixWord ++ tailWord_3859299).sum := by decide
  have hdescent : baseEnd_3859299 < baseStart_3859299 := by decide
  rcases family_descends (prefixWord ++ tailWord_3859299) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3859309 : List Nat := [1, 5, 1, 1, 1, 1, 1, 6, 2, 4]
def baseStart_3859309 : Nat := 118140960795 + 3859309 * 2 ^ 59
def prefixEnd_3859309 : Nat := 4983230072969 + 3 ^ 40 * 3859309 * 2
def baseEnd_3859309 : Nat := 660560170407582056496289

theorem tailTrace_3859309 : CollatzResearch.WordTrace tailWord_3859309 prefixEnd_3859309 660560170407582056496289 := by
  unfold tailWord_3859309
  simp only [CollatzResearch.WordTrace]
  refine ⟨140760563175390085347284981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93840375450260056898189987 140760563175390085347284981)
  ·
    refine ⟨13196302797692820501307967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 140760563175390085347284981 13196302797692820501307967)
    ·
      refine ⟨19794454196539230751961951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13196302797692820501307967 19794454196539230751961951)
      ·
        refine ⟨29691681294808846127942927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19794454196539230751961951 29691681294808846127942927)
        ·
          refine ⟨44537521942213269191914391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29691681294808846127942927 44537521942213269191914391)
          ·
            refine ⟨66806282913319903787871587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44537521942213269191914391 66806282913319903787871587)
            ·
              refine ⟨100209424369979855681807381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 66806282913319903787871587 100209424369979855681807381)
              ·
                refine ⟨4697316767342805735084721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 100209424369979855681807381 4697316767342805735084721)
                ·
                  refine ⟨3522987575507104301313541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4697316767342805735084721 3522987575507104301313541)
                  ·
                    refine ⟨660560170407582056496289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3522987575507104301313541 660560170407582056496289)
                    ·
                      rfl

theorem cell23_3859309_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 1, 6, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 1, 6, 2, 4].length) (baseStart_3859309 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3859309 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3859309 prefixEnd_3859309 := by exact prefixLift 3859309
  have htrace : WordTrace (prefixWord ++ tailWord_3859309) baseStart_3859309 baseEnd_3859309 := by
    simpa [prefixWord, tailWord_3859309, baseEnd_3859309] using wordTrace_append hprefix tailTrace_3859309
  have hstable : (prefixWord ++ tailWord_3859309).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3859309).length < 2 ^ (prefixWord ++ tailWord_3859309).sum := by decide
  have hdescent : baseEnd_3859309 < baseStart_3859309 := by decide
  rcases family_descends (prefixWord ++ tailWord_3859309) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3859310 : List Nat := [4, 1, 2, 3, 3, 1, 1, 1, 3, 1, 3]
def baseStart_3859310 : Nat := 118140960795 + 3859310 * 2 ^ 59
def prefixEnd_3859310 : Nat := 4983230072969 + 3 ^ 40 * 3859310 * 2
def baseEnd_3859310 : Nat := 1981681024703400665576363

theorem tailTrace_3859310 : CollatzResearch.WordTrace tailWord_3859310 prefixEnd_3859310 1981681024703400665576363 := by
  unfold tailWord_3859310
  simp only [CollatzResearch.WordTrace]
  refine ⟨17595074956048307814758923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 93840399765590975012047589 17595074956048307814758923)
  ·
    refine ⟨26392612434072461722138385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17595074956048307814758923 26392612434072461722138385)
    ·
      refine ⟨19794459325554346291603789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26392612434072461722138385 19794459325554346291603789)
      ·
        refine ⟨7422922247082879859351421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19794459325554346291603789 7422922247082879859351421)
        ·
          refine ⟨2783595842656079947256783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7422922247082879859351421 2783595842656079947256783)
          ·
            refine ⟨4175393763984119920885175, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2783595842656079947256783 4175393763984119920885175)
            ·
              refine ⟨6263090645976179881327763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4175393763984119920885175 6263090645976179881327763)
              ·
                refine ⟨9394635968964269821991645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6263090645976179881327763 9394635968964269821991645)
                ·
                  refine ⟨3522988488361601183246867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9394635968964269821991645 3522988488361601183246867)
                  ·
                    refine ⟨5284482732542401774870301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3522988488361601183246867 5284482732542401774870301)
                    ·
                      refine ⟨1981681024703400665576363, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5284482732542401774870301 1981681024703400665576363)
                      ·
                        rfl

theorem cell23_3859310_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 3, 1, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 3, 1, 1, 1, 3, 1, 3].length) (baseStart_3859310 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3859310 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3859310 prefixEnd_3859310 := by exact prefixLift 3859310
  have htrace : WordTrace (prefixWord ++ tailWord_3859310) baseStart_3859310 baseEnd_3859310 := by
    simpa [prefixWord, tailWord_3859310, baseEnd_3859310] using wordTrace_append hprefix tailTrace_3859310
  have hstable : (prefixWord ++ tailWord_3859310).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3859310).length < 2 ^ (prefixWord ++ tailWord_3859310).sum := by decide
  have hdescent : baseEnd_3859310 < baseStart_3859310 := by decide
  rcases family_descends (prefixWord ++ tailWord_3859310) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3859330 : List Nat := [3, 4, 2, 2, 1, 2, 1, 2, 1, 5]
def baseStart_3859330 : Nat := 118140960795 + 3859330 * 2 ^ 59
def prefixEnd_3859330 : Nat := 4983230072969 + 3 ^ 40 * 3859330 * 2
def baseEnd_3859330 : Nat := 660563764772163529108757

theorem tailTrace_3859330 : CollatzResearch.WordTrace tailWord_3859330 prefixEnd_3859330 660563764772163529108757 := by
  unfold tailWord_3859330
  simp only [CollatzResearch.WordTrace]
  refine ⟨35190332277078501483449861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 93840886072209337289199629 35190332277078501483449861)
  ·
    refine ⟨6598187301952219028146849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 35190332277078501483449861 6598187301952219028146849)
    ·
      refine ⟨4948640476464164271110137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6598187301952219028146849 4948640476464164271110137)
      ·
        refine ⟨3711480357348123203332603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4948640476464164271110137 3711480357348123203332603)
        ·
          refine ⟨5567220536022184804998905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3711480357348123203332603 5567220536022184804998905)
          ·
            refine ⟨4175415402016638603749179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5567220536022184804998905 4175415402016638603749179)
            ·
              refine ⟨6263123103024957905623769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4175415402016638603749179 6263123103024957905623769)
              ·
                refine ⟨4697342327268718429217827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6263123103024957905623769 4697342327268718429217827)
                ·
                  refine ⟨7046013490903077643826741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4697342327268718429217827 7046013490903077643826741)
                  ·
                    refine ⟨660563764772163529108757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7046013490903077643826741 660563764772163529108757)
                    ·
                      rfl

theorem cell23_3859330_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 2, 1, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 2, 1, 2, 1, 2, 1, 5].length) (baseStart_3859330 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3859330 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3859330 prefixEnd_3859330 := by exact prefixLift 3859330
  have htrace : WordTrace (prefixWord ++ tailWord_3859330) baseStart_3859330 baseEnd_3859330 := by
    simpa [prefixWord, tailWord_3859330, baseEnd_3859330] using wordTrace_append hprefix tailTrace_3859330
  have hstable : (prefixWord ++ tailWord_3859330).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3859330).length < 2 ^ (prefixWord ++ tailWord_3859330).sum := by decide
  have hdescent : baseEnd_3859330 < baseStart_3859330 := by decide
  rcases family_descends (prefixWord ++ tailWord_3859330) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3859336 : List Nat := [2, 1, 3, 3, 2, 1, 3, 2, 1, 2, 3]
def baseStart_3859336 : Nat := 118140960795 + 3859336 * 2 ^ 59
def prefixEnd_3859336 : Nat := 4983230072969 + 3 ^ 40 * 3859336 * 2
def baseEnd_3859336 : Nat := 1981694375200417563851243

theorem tailTrace_3859336 : CollatzResearch.WordTrace tailWord_3859336 prefixEnd_3859336 1981694375200417563851243 := by
  unfold tailWord_3859336
  simp only [CollatzResearch.WordTrace]
  refine ⟨70380773973146134479258931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93841031964194845972345241 70380773973146134479258931)
  ·
    refine ⟨105571160959719201718888397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70380773973146134479258931 105571160959719201718888397)
    ·
      refine ⟨39589185359894700644583149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 105571160959719201718888397 39589185359894700644583149)
      ·
        refine ⟨14845944509960512741718681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 39589185359894700644583149 14845944509960512741718681)
        ·
          refine ⟨11134458382470384556289011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14845944509960512741718681 11134458382470384556289011)
          ·
            refine ⟨16701687573705576834433517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11134458382470384556289011 16701687573705576834433517)
            ·
              refine ⟨6263132840139591312912569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16701687573705576834433517 6263132840139591312912569)
              ·
                refine ⟨4697349630104693484684427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6263132840139591312912569 4697349630104693484684427)
                ·
                  refine ⟨7046024445157040227026641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4697349630104693484684427 7046024445157040227026641)
                  ·
                    refine ⟨5284518333867780170269981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7046024445157040227026641 5284518333867780170269981)
                    ·
                      refine ⟨1981694375200417563851243, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5284518333867780170269981 1981694375200417563851243)
                      ·
                        rfl

theorem cell23_3859336_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 1, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 1, 3, 2, 1, 2, 3].length) (baseStart_3859336 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3859336 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3859336 prefixEnd_3859336 := by exact prefixLift 3859336
  have htrace : WordTrace (prefixWord ++ tailWord_3859336) baseStart_3859336 baseEnd_3859336 := by
    simpa [prefixWord, tailWord_3859336, baseEnd_3859336] using wordTrace_append hprefix tailTrace_3859336
  have hstable : (prefixWord ++ tailWord_3859336).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3859336).length < 2 ^ (prefixWord ++ tailWord_3859336).sum := by decide
  have hdescent : baseEnd_3859336 < baseStart_3859336 := by decide
  rcases family_descends (prefixWord ++ tailWord_3859336) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3859346 : List Nat := [3, 2, 3, 2, 2, 1, 1, 2, 1, 2, 4]
def baseStart_3859346 : Nat := 118140960795 + 3859346 * 2 ^ 59
def prefixEnd_3859346 : Nat := 4983230072969 + 3 ^ 40 * 3859346 * 2
def baseEnd_3859346 : Nat := 1981699510006962524726197

theorem tailTrace_3859346 : CollatzResearch.WordTrace tailWord_3859346 prefixEnd_3859346 1981699510006962524726197 := by
  unfold tailWord_3859346
  simp only [CollatzResearch.WordTrace]
  refine ⟨35190478169064010166595473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 93841275117504027110921261 35190478169064010166595473)
  ·
    refine ⟨26392858626798007624946605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35190478169064010166595473 26392858626798007624946605)
    ·
      refine ⟨9897321985049252859354977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26392858626798007624946605 9897321985049252859354977)
      ·
        refine ⟨7422991488786939644516233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9897321985049252859354977 7422991488786939644516233)
        ·
          refine ⟨5567243616590204733387175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7422991488786939644516233 5567243616590204733387175)
          ·
            refine ⟨8350865424885307100080763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5567243616590204733387175 8350865424885307100080763)
            ·
              refine ⟨12526298137327960650121145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8350865424885307100080763 12526298137327960650121145)
              ·
                refine ⟨9394723602995970487590859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12526298137327960650121145 9394723602995970487590859)
                ·
                  refine ⟨14092085404493955731386289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9394723602995970487590859 14092085404493955731386289)
                  ·
                    refine ⟨10569064053370466798539717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14092085404493955731386289 10569064053370466798539717)
                    ·
                      refine ⟨1981699510006962524726197, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10569064053370466798539717 1981699510006962524726197)
                      ·
                        rfl

theorem cell23_3859346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 2, 1, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 2, 1, 1, 2, 1, 2, 4].length) (baseStart_3859346 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3859346 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3859346 prefixEnd_3859346 := by exact prefixLift 3859346
  have htrace : WordTrace (prefixWord ++ tailWord_3859346) baseStart_3859346 baseEnd_3859346 := by
    simpa [prefixWord, tailWord_3859346, baseEnd_3859346] using wordTrace_append hprefix tailTrace_3859346
  have hstable : (prefixWord ++ tailWord_3859346).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3859346).length < 2 ^ (prefixWord ++ tailWord_3859346).sum := by decide
  have hdescent : baseEnd_3859346 < baseStart_3859346 := by decide
  rcases family_descends (prefixWord ++ tailWord_3859346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3859349 : List Nat := [1, 3, 2, 1, 1, 5, 1, 2, 1, 3, 3]
def baseStart_3859349 : Nat := 118140960795 + 3859349 * 2 ^ 59
def prefixEnd_3859349 : Nat := 4983230072969 + 3 ^ 40 * 3859349 * 2
def baseEnd_3859349 : Nat := 1981701050448926012988683

theorem tailTrace_3859349 : CollatzResearch.WordTrace tailWord_3859349 prefixEnd_3859349 1981701050448926012988683 := by
  unfold tailWord_3859349
  simp only [CollatzResearch.WordTrace]
  refine ⟨140762022095245172178741101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93841348063496781452494067 140762022095245172178741101)
  ·
    refine ⟨52785758285716939567027913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 140762022095245172178741101 52785758285716939567027913)
    ·
      refine ⟨39589318714287704675270935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52785758285716939567027913 39589318714287704675270935)
      ·
        refine ⟨59383978071431557012906403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39589318714287704675270935 59383978071431557012906403)
        ·
          refine ⟨89075967107147335519359605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59383978071431557012906403 89075967107147335519359605)
          ·
            refine ⟨8350871916295062704939963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 89075967107147335519359605 8350871916295062704939963)
            ·
              refine ⟨12526307874442594057409945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8350871916295062704939963 12526307874442594057409945)
              ·
                refine ⟨9394730905831945543057459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12526307874442594057409945 9394730905831945543057459)
                ·
                  refine ⟨14092096358747918314586189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9394730905831945543057459 14092096358747918314586189)
                  ·
                    refine ⟨5284536134530469367969821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14092096358747918314586189 5284536134530469367969821)
                    ·
                      refine ⟨1981701050448926012988683, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5284536134530469367969821 1981701050448926012988683)
                      ·
                        rfl

theorem cell23_3859349_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 5, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 5, 1, 2, 1, 3, 3].length) (baseStart_3859349 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3859349 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3859349 prefixEnd_3859349 := by exact prefixLift 3859349
  have htrace : WordTrace (prefixWord ++ tailWord_3859349) baseStart_3859349 baseEnd_3859349 := by
    simpa [prefixWord, tailWord_3859349, baseEnd_3859349] using wordTrace_append hprefix tailTrace_3859349
  have hstable : (prefixWord ++ tailWord_3859349).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3859349).length < 2 ^ (prefixWord ++ tailWord_3859349).sum := by decide
  have hdescent : baseEnd_3859349 < baseStart_3859349 := by decide
  rcases family_descends (prefixWord ++ tailWord_3859349) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3859373 : List Nat := [1, 5, 2, 3, 2, 1, 1, 8]
def baseStart_3859373 : Nat := 118140960795 + 3859373 * 2 ^ 59
def prefixEnd_3859373 : Nat := 4983230072969 + 3 ^ 40 * 3859373 * 2
def baseEnd_3859373 : Nat := 73396791629060515521799

theorem tailTrace_3859373 : CollatzResearch.WordTrace tailWord_3859373 prefixEnd_3859373 73396791629060515521799 := by
  unfold tailWord_3859373
  simp only [CollatzResearch.WordTrace]
  refine ⟨140762897447158224277614773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93841931631438816185076515 140762897447158224277614773)
  ·
    refine ⟨13196521635671083526026385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 140762897447158224277614773 13196521635671083526026385)
    ·
      refine ⟨9897391226753312644519789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13196521635671083526026385 9897391226753312644519789)
      ·
        refine ⟨3711521710032492241694921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9897391226753312644519789 3711521710032492241694921)
        ·
          refine ⟨2783641282524369181271191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3711521710032492241694921 2783641282524369181271191)
          ·
            refine ⟨4175461923786553771906787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2783641282524369181271191 4175461923786553771906787)
            ·
              refine ⟨6263192885679830657860181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4175461923786553771906787 6263192885679830657860181)
              ·
                refine ⟨73396791629060515521799, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 6263192885679830657860181 73396791629060515521799)
                ·
                  rfl

theorem cell23_3859373_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 3, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 3, 2, 1, 1, 8].length) (baseStart_3859373 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3859373 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3859373 prefixEnd_3859373 := by exact prefixLift 3859373
  have htrace : WordTrace (prefixWord ++ tailWord_3859373) baseStart_3859373 baseEnd_3859373 := by
    simpa [prefixWord, tailWord_3859373, baseEnd_3859373] using wordTrace_append hprefix tailTrace_3859373
  have hstable : (prefixWord ++ tailWord_3859373).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3859373).length < 2 ^ (prefixWord ++ tailWord_3859373).sum := by decide
  have hdescent : baseEnd_3859373 < baseStart_3859373 := by decide
  rcases family_descends (prefixWord ++ tailWord_3859373) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3859402 : List Nat := [3, 1, 2, 1, 2, 1, 1, 1, 3, 4, 4]
def baseStart_3859402 : Nat := 118140960795 + 3859402 * 2 ^ 59
def prefixEnd_3859402 : Nat := 4983230072969 + 3 ^ 40 * 3859402 * 2
def baseEnd_3859402 : Nat := 1981728264923614305625939

theorem tailTrace_3859402 : CollatzResearch.WordTrace tailWord_3859402 prefixEnd_3859402 1981728264923614305625939 := by
  unfold tailWord_3859402
  simp only [CollatzResearch.WordTrace]
  refine ⟨35190988791013290557605115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 93842636776035441486946973 35190988791013290557605115)
  ·
    refine ⟨52786483186519935836407673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35190988791013290557605115 52786483186519935836407673)
    ·
      refine ⟨39589862389889951877305755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52786483186519935836407673 39589862389889951877305755)
      ·
        refine ⟨59384793584834927815958633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39589862389889951877305755 59384793584834927815958633)
        ·
          refine ⟨44538595188626195861968975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59384793584834927815958633 44538595188626195861968975)
          ·
            refine ⟨66807892782939293792953463, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44538595188626195861968975 66807892782939293792953463)
            ·
              refine ⟨100211839174408940689430195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 66807892782939293792953463 100211839174408940689430195)
              ·
                refine ⟨150317758761613411034145293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 100211839174408940689430195 150317758761613411034145293)
                ·
                  refine ⟨56369159535605029137804485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 150317758761613411034145293 56369159535605029137804485)
                  ·
                    refine ⟨10569217412925942963338341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 56369159535605029137804485 10569217412925942963338341)
                    ·
                      refine ⟨1981728264923614305625939, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10569217412925942963338341 1981728264923614305625939)
                      ·
                        rfl

theorem cell23_3859402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 1, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 1, 1, 3, 4, 4].length) (baseStart_3859402 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3859402 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3859402 prefixEnd_3859402 := by exact prefixLift 3859402
  have htrace : WordTrace (prefixWord ++ tailWord_3859402) baseStart_3859402 baseEnd_3859402 := by
    simpa [prefixWord, tailWord_3859402, baseEnd_3859402] using wordTrace_append hprefix tailTrace_3859402
  have hstable : (prefixWord ++ tailWord_3859402).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3859402).length < 2 ^ (prefixWord ++ tailWord_3859402).sum := by decide
  have hdescent : baseEnd_3859402 < baseStart_3859402 := by decide
  rcases family_descends (prefixWord ++ tailWord_3859402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3859406 : List Nat := [4, 1, 1, 1, 2, 3, 2, 2, 1, 4, 2]
def baseStart_3859406 : Nat := 118140960795 + 3859406 * 2 ^ 59
def prefixEnd_3859406 : Nat := 4983230072969 + 3 ^ 40 * 3859406 * 2
def baseEnd_3859406 : Nat := 1981730318846232289975921

theorem tailTrace_3859406 : CollatzResearch.WordTrace tailWord_3859406 prefixEnd_3859406 1981730318846232289975921 := by
  unfold tailWord_3859406
  simp only [CollatzResearch.WordTrace]
  refine ⟨17595512632004833864195759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 93842734037359113942377381 17595512632004833864195759)
  ·
    refine ⟨26393268948007250796293639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17595512632004833864195759 26393268948007250796293639)
    ·
      refine ⟨39589903422010876194440459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26393268948007250796293639 39589903422010876194440459)
      ·
        refine ⟨59384855133016314291660689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39589903422010876194440459 59384855133016314291660689)
        ·
          refine ⟨44538641349762235718745517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59384855133016314291660689 44538641349762235718745517)
          ·
            refine ⟨16701990506160838394529569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 44538641349762235718745517 16701990506160838394529569)
            ·
              refine ⟨12526492879620628795897177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16701990506160838394529569 12526492879620628795897177)
              ·
                refine ⟨9394869659715471596922883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12526492879620628795897177 9394869659715471596922883)
                ·
                  refine ⟨14092304489573207395384325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9394869659715471596922883 14092304489573207395384325)
                  ·
                    refine ⟨2642307091794976386634561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 14092304489573207395384325 2642307091794976386634561)
                    ·
                      refine ⟨1981730318846232289975921, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2642307091794976386634561 1981730318846232289975921)
                      ·
                        rfl

theorem cell23_3859406_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 3, 2, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 3, 2, 2, 1, 4, 2].length) (baseStart_3859406 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3859406 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3859406 prefixEnd_3859406 := by exact prefixLift 3859406
  have htrace : WordTrace (prefixWord ++ tailWord_3859406) baseStart_3859406 baseEnd_3859406 := by
    simpa [prefixWord, tailWord_3859406, baseEnd_3859406] using wordTrace_append hprefix tailTrace_3859406
  have hstable : (prefixWord ++ tailWord_3859406).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3859406).length < 2 ^ (prefixWord ++ tailWord_3859406).sum := by decide
  have hdescent : baseEnd_3859406 < baseStart_3859406 := by decide
  rcases family_descends (prefixWord ++ tailWord_3859406) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3859410 : List Nat := [3, 2, 2, 3, 1, 1, 4, 1, 1, 3, 2]
def baseStart_3859410 : Nat := 118140960795 + 3859410 * 2 ^ 59
def prefixEnd_3859410 : Nat := 4983230072969 + 3 ^ 40 * 3859410 * 2
def baseEnd_3859410 : Nat := 1981732372768850274325903

theorem tailTrace_3859410 : CollatzResearch.WordTrace tailWord_3859410 prefixEnd_3859410 1981732372768850274325903 := by
  unfold tailWord_3859410
  simp only [CollatzResearch.WordTrace]
  refine ⟨35191061737006044899177921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 93842831298682786397807789 35191061737006044899177921)
  ·
    refine ⟨26393296302754533674383441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35191061737006044899177921 26393296302754533674383441)
    ·
      refine ⟨19794972227065900255787581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26393296302754533674383441 19794972227065900255787581)
      ·
        refine ⟨7423114585149712595920343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19794972227065900255787581 7423114585149712595920343)
        ·
          refine ⟨11134671877724568893880515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7423114585149712595920343 11134671877724568893880515)
          ·
            refine ⟨16702007816586853340820773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11134671877724568893880515 16702007816586853340820773)
            ·
              refine ⟨3131626465610035001403895, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16702007816586853340820773 3131626465610035001403895)
              ·
                refine ⟨4697439698415052502105843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3131626465610035001403895 4697439698415052502105843)
                ·
                  refine ⟨7046159547622578753158765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4697439698415052502105843 7046159547622578753158765)
                  ·
                    refine ⟨2642309830358467032434537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7046159547622578753158765 2642309830358467032434537)
                    ·
                      refine ⟨1981732372768850274325903, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2642309830358467032434537 1981732372768850274325903)
                      ·
                        rfl

theorem cell23_3859410_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 1, 4, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 1, 4, 1, 1, 3, 2].length) (baseStart_3859410 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3859410 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3859410 prefixEnd_3859410 := by exact prefixLift 3859410
  have htrace : WordTrace (prefixWord ++ tailWord_3859410) baseStart_3859410 baseEnd_3859410 := by
    simpa [prefixWord, tailWord_3859410, baseEnd_3859410] using wordTrace_append hprefix tailTrace_3859410
  have hstable : (prefixWord ++ tailWord_3859410).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3859410).length < 2 ^ (prefixWord ++ tailWord_3859410).sum := by decide
  have hdescent : baseEnd_3859410 < baseStart_3859410 := by decide
  rcases family_descends (prefixWord ++ tailWord_3859410) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3859423 : List Nat := [1, 1, 2, 3, 5, 1, 1, 1, 4, 2, 2]
def baseStart_3859423 : Nat := 118140960795 + 3859423 * 2 ^ 59
def prefixEnd_3859423 : Nat := 4983230072969 + 3 ^ 40 * 3859423 * 2
def baseEnd_3859423 : Nat := 1981739048017358723463343

theorem tailTrace_3859423 : CollatzResearch.WordTrace tailWord_3859423 prefixEnd_3859423 1981739048017358723463343 := by
  unfold tailWord_3859423
  simp only [CollatzResearch.WordTrace]
  refine ⟨140764721096977082816934923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93843147397984721877956615 140764721096977082816934923)
  ·
    refine ⟨211147081645465624225402385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140764721096977082816934923 211147081645465624225402385)
    ·
      refine ⟨158360311234099218169051789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 211147081645465624225402385 158360311234099218169051789)
      ·
        refine ⟨59385116712787206813394421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 158360311234099218169051789 59385116712787206813394421)
        ·
          refine ⟨5567354691823800638755727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 59385116712787206813394421 5567354691823800638755727)
          ·
            refine ⟨8351032037735700958133591, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5567354691823800638755727 8351032037735700958133591)
            ·
              refine ⟨12526548056603551437200387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8351032037735700958133591 12526548056603551437200387)
              ·
                refine ⟨18789822084905327155800581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12526548056603551437200387 18789822084905327155800581)
                ·
                  refine ⟨3523091640919748841712609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 18789822084905327155800581 3523091640919748841712609)
                  ·
                    refine ⟨2642318730689811631284457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3523091640919748841712609 2642318730689811631284457)
                    ·
                      refine ⟨1981739048017358723463343, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2642318730689811631284457 1981739048017358723463343)
                      ·
                        rfl

theorem cell23_3859423_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 5, 1, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 5, 1, 1, 1, 4, 2, 2].length) (baseStart_3859423 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3859423 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3859423 prefixEnd_3859423 := by exact prefixLift 3859423
  have htrace : WordTrace (prefixWord ++ tailWord_3859423) baseStart_3859423 baseEnd_3859423 := by
    simpa [prefixWord, tailWord_3859423, baseEnd_3859423] using wordTrace_append hprefix tailTrace_3859423
  have hstable : (prefixWord ++ tailWord_3859423).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3859423).length < 2 ^ (prefixWord ++ tailWord_3859423).sum := by decide
  have hdescent : baseEnd_3859423 < baseStart_3859423 := by decide
  rcases family_descends (prefixWord ++ tailWord_3859423) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3859439 : List Nat := [1, 1, 2, 1, 4, 3, 2, 1, 2, 3, 3]
def baseStart_3859439 : Nat := 118140960795 + 3859439 * 2 ^ 59
def prefixEnd_3859439 : Nat := 4983230072969 + 3 ^ 40 * 3859439 * 2
def baseEnd_3859439 : Nat := 1981747263707830660863269

theorem tailTrace_3859439 : CollatzResearch.WordTrace tailWord_3859439 prefixEnd_3859439 1981747263707830660863269 := by
  unfold tailWord_3859439
  simp only [CollatzResearch.WordTrace]
  refine ⟨140765304664919117549517371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93843536443279411699678247 140765304664919117549517371)
  ·
    refine ⟨211147956997378676324276057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140765304664919117549517371 211147956997378676324276057)
    ·
      refine ⟨158360967748034007243207043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 211147956997378676324276057 158360967748034007243207043)
      ·
        refine ⟨237541451622051010864810565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 158360967748034007243207043 237541451622051010864810565)
        ·
          refine ⟨44539022179134564537151981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 237541451622051010864810565 44539022179134564537151981)
          ·
            refine ⟨16702133317175461701431993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 44539022179134564537151981 16702133317175461701431993)
            ·
              refine ⟨12526599987881596276073995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16702133317175461701431993 12526599987881596276073995)
              ·
                refine ⟨18789899981822394414110993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12526599987881596276073995 18789899981822394414110993)
                ·
                  refine ⟨14092424986366795810583245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18789899981822394414110993 14092424986366795810583245)
                  ·
                    refine ⟨5284659369887548428968717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14092424986366795810583245 5284659369887548428968717)
                    ·
                      refine ⟨1981747263707830660863269, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5284659369887548428968717 1981747263707830660863269)
                      ·
                        rfl

theorem cell23_3859439_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 3, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 3, 2, 1, 2, 3, 3].length) (baseStart_3859439 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3859439 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3859439 prefixEnd_3859439 := by exact prefixLift 3859439
  have htrace : WordTrace (prefixWord ++ tailWord_3859439) baseStart_3859439 baseEnd_3859439 := by
    simpa [prefixWord, tailWord_3859439, baseEnd_3859439] using wordTrace_append hprefix tailTrace_3859439
  have hstable : (prefixWord ++ tailWord_3859439).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3859439).length < 2 ^ (prefixWord ++ tailWord_3859439).sum := by decide
  have hdescent : baseEnd_3859439 < baseStart_3859439 := by decide
  rcases family_descends (prefixWord ++ tailWord_3859439) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3859499 : List Nat := [1, 1, 1, 1, 2, 1, 5, 2, 4, 2, 3]
def baseStart_3859499 : Nat := 118140960795 + 3859499 * 2 ^ 59
def prefixEnd_3859499 : Nat := 4983230072969 + 3 ^ 40 * 3859499 * 2
def baseEnd_3859499 : Nat := 1981778072547100426112993

theorem tailTrace_3859499 : CollatzResearch.WordTrace tailWord_3859499 prefixEnd_3859499 1981778072547100426112993 := by
  unfold tailWord_3859499
  simp only [CollatzResearch.WordTrace]
  refine ⟨140767493044701747796701551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93844995363134498531134367 140767493044701747796701551)
  ·
    refine ⟨211151239567052621695052327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140767493044701747796701551 211151239567052621695052327)
    ·
      refine ⟨316726859350578932542578491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 211151239567052621695052327 316726859350578932542578491)
      ·
        refine ⟨475090289025868398813867737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 316726859350578932542578491 475090289025868398813867737)
        ·
          refine ⟨356317716769401299110400803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 475090289025868398813867737 356317716769401299110400803)
          ·
            refine ⟨534476575154101948665601205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 356317716769401299110400803 534476575154101948665601205)
            ·
              refine ⟨50107178920697057687400113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 534476575154101948665601205 50107178920697057687400113)
              ·
                refine ⟨37580384190522793265550085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 50107178920697057687400113 37580384190522793265550085)
                ·
                  refine ⟨7046322035723023737290641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 37580384190522793265550085 7046322035723023737290641)
                  ·
                    refine ⟨5284741526792267802967981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7046322035723023737290641 5284741526792267802967981)
                    ·
                      refine ⟨1981778072547100426112993, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5284741526792267802967981 1981778072547100426112993)
                      ·
                        rfl

theorem cell23_3859499_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 5, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 5, 2, 4, 2, 3].length) (baseStart_3859499 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3859499 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3859499 prefixEnd_3859499 := by exact prefixLift 3859499
  have htrace : WordTrace (prefixWord ++ tailWord_3859499) baseStart_3859499 baseEnd_3859499 := by
    simpa [prefixWord, tailWord_3859499, baseEnd_3859499] using wordTrace_append hprefix tailTrace_3859499
  have hstable : (prefixWord ++ tailWord_3859499).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3859499).length < 2 ^ (prefixWord ++ tailWord_3859499).sum := by decide
  have hdescent : baseEnd_3859499 < baseStart_3859499 := by decide
  rcases family_descends (prefixWord ++ tailWord_3859499) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3859516 : List Nat := [2, 2, 2, 2, 2, 2, 1, 3, 2, 2, 3]
def baseStart_3859516 : Nat := 118140960795 + 3859516 * 2 ^ 59
def prefixEnd_3859516 : Nat := 4983230072969 + 3 ^ 40 * 3859516 * 2
def baseEnd_3859516 : Nat := 1981786801718226859600415

theorem tailTrace_3859516 : CollatzResearch.WordTrace tailWord_3859516 prefixEnd_3859516 1981786801718226859600415 := by
  unfold tailWord_3859516
  simp only [CollatzResearch.WordTrace]
  refine ⟨70384056542820079850035201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93845408723760106466713601 70384056542820079850035201)
  ·
    refine ⟨52788042407115059887526401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70384056542820079850035201 52788042407115059887526401)
    ·
      refine ⟨39591031805336294915644801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52788042407115059887526401 39591031805336294915644801)
      ·
        refine ⟨29693273854002221186733601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39591031805336294915644801 29693273854002221186733601)
        ·
          refine ⟨22269955390501665890050201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29693273854002221186733601 22269955390501665890050201)
          ·
            refine ⟨16702466542876249417537651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22269955390501665890050201 16702466542876249417537651)
            ·
              refine ⟨25053699814314374126306477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16702466542876249417537651 25053699814314374126306477)
              ·
                refine ⟨9395137430367890297364929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25053699814314374126306477 9395137430367890297364929)
                ·
                  refine ⟨7046353072775917723023697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9395137430367890297364929 7046353072775917723023697)
                  ·
                    refine ⟨5284764804581938292267773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7046353072775917723023697 5284764804581938292267773)
                    ·
                      refine ⟨1981786801718226859600415, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5284764804581938292267773 1981786801718226859600415)
                      ·
                        rfl

theorem cell23_3859516_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 2, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 2, 1, 3, 2, 2, 3].length) (baseStart_3859516 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3859516 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3859516 prefixEnd_3859516 := by exact prefixLift 3859516
  have htrace : WordTrace (prefixWord ++ tailWord_3859516) baseStart_3859516 baseEnd_3859516 := by
    simpa [prefixWord, tailWord_3859516, baseEnd_3859516] using wordTrace_append hprefix tailTrace_3859516
  have hstable : (prefixWord ++ tailWord_3859516).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3859516).length < 2 ^ (prefixWord ++ tailWord_3859516).sum := by decide
  have hdescent : baseEnd_3859516 < baseStart_3859516 := by decide
  rcases family_descends (prefixWord ++ tailWord_3859516) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3859533 : List Nat := [1, 6, 1, 1, 1, 2, 2, 2, 2, 2, 3]
def baseStart_3859533 : Nat := 118140960795 + 3859533 * 2 ^ 59
def prefixEnd_3859533 : Nat := 4983230072969 + 3 ^ 40 * 3859533 * 2
def baseEnd_3859533 : Nat := 1981795530889353293087837

theorem tailTrace_3859533 : CollatzResearch.WordTrace tailWord_3859533 prefixEnd_3859533 1981795530889353293087837 := by
  unfold tailWord_3859533
  simp only [CollatzResearch.WordTrace]
  refine ⟨140768733126578571603439253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93845822084385714402292835 140768733126578571603439253)
  ·
    refine ⟨6598534365308370543911215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 140768733126578571603439253 6598534365308370543911215)
    ·
      refine ⟨9897801547962555815866823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6598534365308370543911215 9897801547962555815866823)
      ·
        refine ⟨14846702321943833723800235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9897801547962555815866823 14846702321943833723800235)
        ·
          refine ⟨22270053482915750585700353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14846702321943833723800235 22270053482915750585700353)
          ·
            refine ⟨16702540112186812939275265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22270053482915750585700353 16702540112186812939275265)
            ·
              refine ⟨12526905084140109704456449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16702540112186812939275265 12526905084140109704456449)
              ·
                refine ⟨9395178813105082278342337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12526905084140109704456449 9395178813105082278342337)
                ·
                  refine ⟨7046384109828811708756753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9395178813105082278342337 7046384109828811708756753)
                  ·
                    refine ⟨5284788082371608781567565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7046384109828811708756753 5284788082371608781567565)
                    ·
                      refine ⟨1981795530889353293087837, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5284788082371608781567565 1981795530889353293087837)
                      ·
                        rfl

theorem cell23_3859533_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 2, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 2, 2, 2, 2, 2, 3].length) (baseStart_3859533 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3859533 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3859533 prefixEnd_3859533 := by exact prefixLift 3859533
  have htrace : WordTrace (prefixWord ++ tailWord_3859533) baseStart_3859533 baseEnd_3859533 := by
    simpa [prefixWord, tailWord_3859533, baseEnd_3859533] using wordTrace_append hprefix tailTrace_3859533
  have hstable : (prefixWord ++ tailWord_3859533).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3859533).length < 2 ^ (prefixWord ++ tailWord_3859533).sum := by decide
  have hdescent : baseEnd_3859533 < baseStart_3859533 := by decide
  rcases family_descends (prefixWord ++ tailWord_3859533) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3859540 : List Nat := [2, 4, 1, 1, 1, 1, 6, 2, 1, 4]
def baseStart_3859540 : Nat := 118140960795 + 3859540 * 2 ^ 59
def prefixEnd_3859540 : Nat := 4983230072969 + 3 ^ 40 * 3859540 * 2
def baseEnd_3859540 : Nat := 660599708417978255233435

theorem tailTrace_3859540 : CollatzResearch.WordTrace tailWord_3859540 prefixEnd_3859540 660599708417978255233435 := by
  unfold tailWord_3859540
  simp only [CollatzResearch.WordTrace]
  refine ⟨70384494218776605899472037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93845992291702141199296049 70384494218776605899472037)
  ·
    refine ⟨13197092666020613606151007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 70384494218776605899472037 13197092666020613606151007)
    ·
      refine ⟨19795638999030920409226511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13197092666020613606151007 19795638999030920409226511)
      ·
        refine ⟨29693458498546380613839767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19795638999030920409226511 29693458498546380613839767)
        ·
          refine ⟨44540187747819570920759651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29693458498546380613839767 44540187747819570920759651)
          ·
            refine ⟨66810281621729356381139477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44540187747819570920759651 66810281621729356381139477)
            ·
              refine ⟨3131731951018563580365913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 66810281621729356381139477 3131731951018563580365913)
              ·
                refine ⟨2348798963263922685274435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3131731951018563580365913 2348798963263922685274435)
                ·
                  refine ⟨3523198444895884027911653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2348798963263922685274435 3523198444895884027911653)
                  ·
                    refine ⟨660599708417978255233435, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3523198444895884027911653 660599708417978255233435)
                    ·
                      rfl

theorem cell23_3859540_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 6, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 6, 2, 1, 4].length) (baseStart_3859540 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3859540 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3859540 prefixEnd_3859540 := by exact prefixLift 3859540
  have htrace : WordTrace (prefixWord ++ tailWord_3859540) baseStart_3859540 baseEnd_3859540 := by
    simpa [prefixWord, tailWord_3859540, baseEnd_3859540] using wordTrace_append hprefix tailTrace_3859540
  have hstable : (prefixWord ++ tailWord_3859540).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3859540).length < 2 ^ (prefixWord ++ tailWord_3859540).sum := by decide
  have hdescent : baseEnd_3859540 < baseStart_3859540 := by decide
  rcases family_descends (prefixWord ++ tailWord_3859540) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3859556 : List Nat := [2, 3, 1, 1, 2, 1, 1, 4, 1, 5, 2]
def baseStart_3859556 : Nat := 118140960795 + 3859556 * 2 ^ 59
def prefixEnd_3859556 : Nat := 4983230072969 + 3 ^ 40 * 3859556 * 2
def baseEnd_3859556 : Nat := 1981807340944406703100231

theorem tailTrace_3859556 : CollatzResearch.WordTrace tailWord_3859556 prefixEnd_3859556 1981807340944406703100231 := by
  unfold tailWord_3859556
  simp only [CollatzResearch.WordTrace]
  refine ⟨70384786002747623265763261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93846381336996831021017681 70384786002747623265763261)
  ·
    refine ⟨26394294751030358724661223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 70384786002747623265763261 26394294751030358724661223)
    ·
      refine ⟨39591442126545538086991835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26394294751030358724661223 39591442126545538086991835)
      ·
        refine ⟨59387163189818307130487753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39591442126545538086991835 59387163189818307130487753)
        ·
          refine ⟨44540372392363730347865815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59387163189818307130487753 44540372392363730347865815)
          ·
            refine ⟨66810558588545595521798723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44540372392363730347865815 66810558588545595521798723)
            ·
              refine ⟨100215837882818393282698085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 66810558588545595521798723 100215837882818393282698085)
              ·
                refine ⟨18790469603028448740505891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 100215837882818393282698085 18790469603028448740505891)
                ·
                  refine ⟨28185704404542673110758837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18790469603028448740505891 28185704404542673110758837)
                  ·
                    refine ⟨2642409787925875604133641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 28185704404542673110758837 2642409787925875604133641)
                    ·
                      refine ⟨1981807340944406703100231, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2642409787925875604133641 1981807340944406703100231)
                      ·
                        rfl

theorem cell23_3859556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 1, 4, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 1, 4, 1, 5, 2].length) (baseStart_3859556 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3859556 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3859556 prefixEnd_3859556 := by exact prefixLift 3859556
  have htrace : WordTrace (prefixWord ++ tailWord_3859556) baseStart_3859556 baseEnd_3859556 := by
    simpa [prefixWord, tailWord_3859556, baseEnd_3859556] using wordTrace_append hprefix tailTrace_3859556
  have hstable : (prefixWord ++ tailWord_3859556).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3859556).length < 2 ^ (prefixWord ++ tailWord_3859556).sum := by decide
  have hdescent : baseEnd_3859556 < baseStart_3859556 := by decide
  rcases family_descends (prefixWord ++ tailWord_3859556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3859566 : List Nat := [4, 1, 2, 2, 1, 2, 2, 1, 3, 5]
def baseStart_3859566 : Nat := 118140960795 + 3859566 * 2 ^ 59
def prefixEnd_3859566 : Nat := 4983230072969 + 3 ^ 40 * 3859566 * 2
def baseEnd_3859566 : Nat := 660604158583650554658395

theorem tailTrace_3859566 : CollatzResearch.WordTrace tailWord_3859566 prefixEnd_3859566 660604158583650554658395 := by
  unfold tailWord_3859566
  simp only [CollatzResearch.WordTrace]
  refine ⟨17596242091932377279923819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 93846624490306012159593701 17596242091932377279923819)
  ·
    refine ⟨26394363137898565919885729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17596242091932377279923819 26394363137898565919885729)
    ·
      refine ⟨19795772353423924439914297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26394363137898565919885729 19795772353423924439914297)
      ·
        refine ⟨14846829265067943329935723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19795772353423924439914297 14846829265067943329935723)
        ·
          refine ⟨22270243897601914994903585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14846829265067943329935723 22270243897601914994903585)
          ·
            refine ⟨16702682923201436246177689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22270243897601914994903585 16702682923201436246177689)
            ·
              refine ⟨12527012192401077184633267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16702682923201436246177689 12527012192401077184633267)
              ·
                refine ⟨18790518288601615776949901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12527012192401077184633267 18790518288601615776949901)
                ·
                  refine ⟨7046444358225605916356213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18790518288601615776949901 7046444358225605916356213)
                  ·
                    refine ⟨660604158583650554658395, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7046444358225605916356213 660604158583650554658395)
                    ·
                      rfl

theorem cell23_3859566_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 2, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 2, 2, 1, 3, 5].length) (baseStart_3859566 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3859566 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3859566 prefixEnd_3859566 := by exact prefixLift 3859566
  have htrace : WordTrace (prefixWord ++ tailWord_3859566) baseStart_3859566 baseEnd_3859566 := by
    simpa [prefixWord, tailWord_3859566, baseEnd_3859566] using wordTrace_append hprefix tailTrace_3859566
  have hstable : (prefixWord ++ tailWord_3859566).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3859566).length < 2 ^ (prefixWord ++ tailWord_3859566).sum := by decide
  have hdescent : baseEnd_3859566 < baseStart_3859566 := by decide
  rcases family_descends (prefixWord ++ tailWord_3859566) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3859580 : List Nat := [2, 2, 2, 1, 1, 3, 4, 3, 1, 1, 3]
def baseStart_3859580 : Nat := 118140960795 + 3859580 * 2 ^ 59
def prefixEnd_3859580 : Nat := 4983230072969 + 3 ^ 40 * 3859580 * 2
def baseEnd_3859580 : Nat := 1981819664480114609200121

theorem tailTrace_3859580 : CollatzResearch.WordTrace tailWord_3859580 prefixEnd_3859580 1981819664480114609200121 := by
  unfold tailWord_3859580
  simp only [CollatzResearch.WordTrace]
  refine ⟨70385223678704149315200097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93846964904938865753600129 70385223678704149315200097)
  ·
    refine ⟨52788917759028111986400073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70385223678704149315200097 52788917759028111986400073)
    ·
      refine ⟨39591688319271083989800055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52788917759028111986400073 39591688319271083989800055)
      ·
        refine ⟨59387532478906625984700083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39591688319271083989800055 59387532478906625984700083)
        ·
          refine ⟨89081298718359938977050125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59387532478906625984700083 89081298718359938977050125)
          ·
            refine ⟨33405487019384977116393797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 89081298718359938977050125 33405487019384977116393797)
            ·
              refine ⟨6263528816134683209323837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 33405487019384977116393797 6263528816134683209323837)
              ·
                refine ⟨2348823306050506203496439, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6263528816134683209323837 2348823306050506203496439)
                ·
                  refine ⟨3523234959075759305244659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2348823306050506203496439 3523234959075759305244659)
                  ·
                    refine ⟨5284852438613638957866989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3523234959075759305244659 5284852438613638957866989)
                    ·
                      refine ⟨1981819664480114609200121, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5284852438613638957866989 1981819664480114609200121)
                      ·
                        rfl

theorem cell23_3859580_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 4, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 4, 3, 1, 1, 3].length) (baseStart_3859580 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3859580 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3859580 prefixEnd_3859580 := by exact prefixLift 3859580
  have htrace : WordTrace (prefixWord ++ tailWord_3859580) baseStart_3859580 baseEnd_3859580 := by
    simpa [prefixWord, tailWord_3859580, baseEnd_3859580] using wordTrace_append hprefix tailTrace_3859580
  have hstable : (prefixWord ++ tailWord_3859580).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3859580).length < 2 ^ (prefixWord ++ tailWord_3859580).sum := by decide
  have hdescent : baseEnd_3859580 < baseStart_3859580 := by decide
  rcases family_descends (prefixWord ++ tailWord_3859580) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3859603 : List Nat := [1, 1, 1, 2, 1, 2, 5, 3, 3, 2, 2]
def baseStart_3859603 : Nat := 118140960795 + 3859603 * 2 ^ 59
def prefixEnd_3859603 : Nat := 4983230072969 + 3 ^ 40 * 3859603 * 2
def baseEnd_3859603 : Nat := 1981831474535168019212515

theorem tailTrace_3859603 : CollatzResearch.WordTrace tailWord_3859603 prefixEnd_3859603 1981831474535168019212515 := by
  unfold tailWord_3859603
  simp only [CollatzResearch.WordTrace]
  refine ⟨140771286236324973558487463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93847524157549982372324975 140771286236324973558487463)
  ·
    refine ⟨211156929354487460337731195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140771286236324973558487463 211156929354487460337731195)
    ·
      refine ⟨316735394031731190506596793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 211156929354487460337731195 316735394031731190506596793)
      ·
        refine ⟨237551545523798392879947595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 316735394031731190506596793 237551545523798392879947595)
        ·
          refine ⟨356327318285697589319921393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 237551545523798392879947595 356327318285697589319921393)
          ·
            refine ⟨267245488714273191989941045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 356327318285697589319921393 267245488714273191989941045)
            ·
              refine ⟨25054264566963111749056973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 267245488714273191989941045 25054264566963111749056973)
              ·
                refine ⟨9395349212611166905896365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25054264566963111749056973 9395349212611166905896365)
                ·
                  refine ⟨3523255954729187589711137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9395349212611166905896365 3523255954729187589711137)
                  ·
                    refine ⟨2642441966046890692283353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3523255954729187589711137 2642441966046890692283353)
                    ·
                      refine ⟨1981831474535168019212515, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2642441966046890692283353 1981831474535168019212515)
                      ·
                        rfl

theorem cell23_3859603_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 5, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 5, 3, 3, 2, 2].length) (baseStart_3859603 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3859603 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3859603 prefixEnd_3859603 := by exact prefixLift 3859603
  have htrace : WordTrace (prefixWord ++ tailWord_3859603) baseStart_3859603 baseEnd_3859603 := by
    simpa [prefixWord, tailWord_3859603, baseEnd_3859603] using wordTrace_append hprefix tailTrace_3859603
  have hstable : (prefixWord ++ tailWord_3859603).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3859603).length < 2 ^ (prefixWord ++ tailWord_3859603).sum := by decide
  have hdescent : baseEnd_3859603 < baseStart_3859603 := by decide
  rcases family_descends (prefixWord ++ tailWord_3859603) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3859620 : List Nat := [2, 3, 1, 2, 3, 1, 2, 2, 3, 2, 2]
def baseStart_3859620 : Nat := 118140960795 + 3859620 * 2 ^ 59
def prefixEnd_3859620 : Nat := 4983230072969 + 3 ^ 40 * 3859620 * 2
def baseEnd_3859620 : Nat := 1981840203706294452699937

theorem tailTrace_3859620 : CollatzResearch.WordTrace tailWord_3859620 prefixEnd_3859620 1981840203706294452699937 := by
  unfold tailWord_3859620
  simp only [CollatzResearch.WordTrace]
  refine ⟨70385953138631692730928157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93847937518175590307904209 70385953138631692730928157)
  ·
    refine ⟨26394732426986884774098059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 70385953138631692730928157 26394732426986884774098059)
    ·
      refine ⟨39592098640480327161147089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26394732426986884774098059 39592098640480327161147089)
      ·
        refine ⟨29694073980360245370860317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39592098640480327161147089 29694073980360245370860317)
        ·
          refine ⟨11135277742635092014072619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29694073980360245370860317 11135277742635092014072619)
          ·
            refine ⟨16702916613952638021108929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11135277742635092014072619 16702916613952638021108929)
            ·
              refine ⟨12527187460464478515831697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16702916613952638021108929 12527187460464478515831697)
              ·
                refine ⟨9395390595348358886873773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12527187460464478515831697 9395390595348358886873773)
                ·
                  refine ⟨3523271473255634582577665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9395390595348358886873773 3523271473255634582577665)
                  ·
                    refine ⟨2642453604941725936933249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3523271473255634582577665 2642453604941725936933249)
                    ·
                      refine ⟨1981840203706294452699937, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2642453604941725936933249 1981840203706294452699937)
                      ·
                        rfl

theorem cell23_3859620_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 1, 2, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 1, 2, 2, 3, 2, 2].length) (baseStart_3859620 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3859620 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3859620 prefixEnd_3859620 := by exact prefixLift 3859620
  have htrace : WordTrace (prefixWord ++ tailWord_3859620) baseStart_3859620 baseEnd_3859620 := by
    simpa [prefixWord, tailWord_3859620, baseEnd_3859620] using wordTrace_append hprefix tailTrace_3859620
  have hstable : (prefixWord ++ tailWord_3859620).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3859620).length < 2 ^ (prefixWord ++ tailWord_3859620).sum := by decide
  have hdescent : baseEnd_3859620 < baseStart_3859620 := by decide
  rcases family_descends (prefixWord ++ tailWord_3859620) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3859653 : List Nat := [1, 3, 1, 1, 1, 1, 3, 6, 2, 1, 3]
def baseStart_3859653 : Nat := 118140960795 + 3859653 * 2 ^ 59
def prefixEnd_3859653 : Nat := 4983230072969 + 3 ^ 40 * 3859653 * 2
def baseEnd_3859653 : Nat := 1981857148567892823587285

theorem tailTrace_3859653 : CollatzResearch.WordTrace tailWord_3859653 prefixEnd_3859653 1981857148567892823587285 := by
  unfold tailWord_3859653
  simp only [CollatzResearch.WordTrace]
  refine ⟨140773109886143832097807613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93848739924095888065205075 140773109886143832097807613)
  ·
    refine ⟨52789916207303937036677855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 140773109886143832097807613 52789916207303937036677855)
    ·
      refine ⟨79184874310955905555016783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52789916207303937036677855 79184874310955905555016783)
      ·
        refine ⟨118777311466433858332525175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79184874310955905555016783 118777311466433858332525175)
        ·
          refine ⟨178165967199650787498787763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 118777311466433858332525175 178165967199650787498787763)
          ·
            refine ⟨267248950799476181248181645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 178165967199650787498787763 267248950799476181248181645)
            ·
              refine ⟨100218356549803567968068117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 267248950799476181248181645 100218356549803567968068117)
              ·
                refine ⟨4697735463272042248503193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 100218356549803567968068117 4697735463272042248503193)
                ·
                  refine ⟨3523301597454031686377395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4697735463272042248503193 3523301597454031686377395)
                  ·
                    refine ⟨5284952396181047529566093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3523301597454031686377395 5284952396181047529566093)
                    ·
                      refine ⟨1981857148567892823587285, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5284952396181047529566093 1981857148567892823587285)
                      ·
                        rfl

theorem cell23_3859653_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 3, 6, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 3, 6, 2, 1, 3].length) (baseStart_3859653 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3859653 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3859653 prefixEnd_3859653 := by exact prefixLift 3859653
  have htrace : WordTrace (prefixWord ++ tailWord_3859653) baseStart_3859653 baseEnd_3859653 := by
    simpa [prefixWord, tailWord_3859653, baseEnd_3859653] using wordTrace_append hprefix tailTrace_3859653
  have hstable : (prefixWord ++ tailWord_3859653).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3859653).length < 2 ^ (prefixWord ++ tailWord_3859653).sum := by decide
  have hdescent : baseEnd_3859653 < baseStart_3859653 := by decide
  rcases family_descends (prefixWord ++ tailWord_3859653) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3859680 : List Nat := [2, 1, 1, 3, 1, 4, 3, 2, 1, 3, 2]
def baseStart_3859680 : Nat := 118140960795 + 3859680 * 2 ^ 59
def prefixEnd_3859680 : Nat := 4983230072969 + 3 ^ 40 * 3859680 * 2
def baseEnd_3859680 : Nat := 1981871012545564217949661

theorem tailTrace_3859680 : CollatzResearch.WordTrace tailWord_3859680 prefixEnd_3859680 1981871012545564217949661 := by
  unfold tailWord_3859680
  simp only [CollatzResearch.WordTrace]
  refine ⟨70387047328523007854520247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93849396438030677139360329 70387047328523007854520247)
  ·
    refine ⟨105580570992784511781780371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70387047328523007854520247 105580570992784511781780371)
    ·
      refine ⟨158370856489176767672670557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105580570992784511781780371 158370856489176767672670557)
      ·
        refine ⟨59389071183441287877251459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 158370856489176767672670557 59389071183441287877251459)
        ·
          refine ⟨89083606775161931815877189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59389071183441287877251459 89083606775161931815877189)
          ·
            refine ⟨16703176270342862215476973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 89083606775161931815877189 16703176270342862215476973)
            ·
              refine ⟨6263691101378573330803865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16703176270342862215476973 6263691101378573330803865)
              ·
                refine ⟨4697768326033929998102899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6263691101378573330803865 4697768326033929998102899)
                ·
                  refine ⟨7046652489050894997154349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4697768326033929998102899 7046652489050894997154349)
                  ·
                    refine ⟨2642494683394085623932881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7046652489050894997154349 2642494683394085623932881)
                    ·
                      refine ⟨1981871012545564217949661, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2642494683394085623932881 1981871012545564217949661)
                      ·
                        rfl

theorem cell23_3859680_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 4, 3, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 4, 3, 2, 1, 3, 2].length) (baseStart_3859680 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3859680 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3859680 prefixEnd_3859680 := by exact prefixLift 3859680
  have htrace : WordTrace (prefixWord ++ tailWord_3859680) baseStart_3859680 baseEnd_3859680 := by
    simpa [prefixWord, tailWord_3859680, baseEnd_3859680] using wordTrace_append hprefix tailTrace_3859680
  have hstable : (prefixWord ++ tailWord_3859680).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3859680).length < 2 ^ (prefixWord ++ tailWord_3859680).sum := by decide
  have hdescent : baseEnd_3859680 < baseStart_3859680 := by decide
  rcases family_descends (prefixWord ++ tailWord_3859680) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3859706 : List Nat := [3, 1, 1, 1, 1, 4, 2, 2, 2, 2, 4]
def baseStart_3859706 : Nat := 118140960795 + 3859706 * 2 ^ 59
def prefixEnd_3859706 : Nat := 4983230072969 + 3 ^ 40 * 3859706 * 2
def baseEnd_3859706 : Nat := 1981884363042581116224541

theorem tailTrace_3859706 : CollatzResearch.WordTrace tailWord_3859706 prefixEnd_3859706 1981884363042581116224541 := by
  unfold tailWord_3859706
  simp only [CollatzResearch.WordTrace]
  refine ⟨35193760738737955537371743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 93850028636634548099657981 35193760738737955537371743)
  ·
    refine ⟨52790641108106933306057615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35193760738737955537371743 52790641108106933306057615)
    ·
      refine ⟨79185961662160399959086423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52790641108106933306057615 79185961662160399959086423)
      ·
        refine ⟨118778942493240599938629635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79185961662160399959086423 118778942493240599938629635)
        ·
          refine ⟨178168413739860899907944453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 118778942493240599938629635 178168413739860899907944453)
          ·
            refine ⟨33406577576223918732739585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 178168413739860899907944453 33406577576223918732739585)
            ·
              refine ⟨25054933182167939049554689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33406577576223918732739585 25054933182167939049554689)
              ·
                refine ⟨18791199886625954287166017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25054933182167939049554689 18791199886625954287166017)
                ·
                  refine ⟨14093399914969465715374513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18791199886625954287166017 14093399914969465715374513)
                  ·
                    refine ⟨10570049936227099286530885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14093399914969465715374513 10570049936227099286530885)
                    ·
                      refine ⟨1981884363042581116224541, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10570049936227099286530885 1981884363042581116224541)
                      ·
                        rfl

theorem cell23_3859706_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 2, 2, 2, 2, 4].length) (baseStart_3859706 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3859706 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3859706 prefixEnd_3859706 := by exact prefixLift 3859706
  have htrace : WordTrace (prefixWord ++ tailWord_3859706) baseStart_3859706 baseEnd_3859706 := by
    simpa [prefixWord, tailWord_3859706, baseEnd_3859706] using wordTrace_append hprefix tailTrace_3859706
  have hstable : (prefixWord ++ tailWord_3859706).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3859706).length < 2 ^ (prefixWord ++ tailWord_3859706).sum := by decide
  have hdescent : baseEnd_3859706 < baseStart_3859706 := by decide
  rcases family_descends (prefixWord ++ tailWord_3859706) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3859793 : List Nat := [1, 2, 2, 1, 4, 1, 1, 4, 3, 4]
def baseStart_3859793 : Nat := 118140960795 + 3859793 * 2 ^ 59
def prefixEnd_3859793 : Nat := 4983230072969 + 3 ^ 40 * 3859793 * 2
def baseEnd_3859793 : Nat := 660643011953174091945547

theorem tailTrace_3859793 : CollatzResearch.WordTrace tailWord_3859793 prefixEnd_3859793 660643011953174091945547 := by
  unfold tailWord_3859793
  simp only [CollatzResearch.WordTrace]
  refine ⟨140778216105636636007904033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93852144070424424005269355 140778216105636636007904033)
  ·
    refine ⟨105583662079227477005928025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 140778216105636636007904033 105583662079227477005928025)
    ·
      refine ⟨79187746559420607754446019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 105583662079227477005928025 79187746559420607754446019)
      ·
        refine ⟨118781619839130911631669029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79187746559420607754446019 118781619839130911631669029)
        ·
          refine ⟨22271553719837045930937943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 118781619839130911631669029 22271553719837045930937943)
          ·
            refine ⟨33407330579755568896406915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22271553719837045930937943 33407330579755568896406915)
            ·
              refine ⟨50110995869633353344610373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33407330579755568896406915 50110995869633353344610373)
              ·
                refine ⟨9395811725556253752114445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 50110995869633353344610373 9395811725556253752114445)
                ·
                  refine ⟨3523429397083595157042917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9395811725556253752114445 3523429397083595157042917)
                  ·
                    refine ⟨660643011953174091945547, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3523429397083595157042917 660643011953174091945547)
                    ·
                      rfl

theorem cell23_3859793_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 1, 4, 3, 4].length) (baseStart_3859793 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3859793 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3859793 prefixEnd_3859793 := by exact prefixLift 3859793
  have htrace : WordTrace (prefixWord ++ tailWord_3859793) baseStart_3859793 baseEnd_3859793 := by
    simpa [prefixWord, tailWord_3859793, baseEnd_3859793] using wordTrace_append hprefix tailTrace_3859793
  have hstable : (prefixWord ++ tailWord_3859793).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3859793).length < 2 ^ (prefixWord ++ tailWord_3859793).sum := by decide
  have hdescent : baseEnd_3859793 < baseStart_3859793 := by decide
  rcases family_descends (prefixWord ++ tailWord_3859793) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3859820 : List Nat := [2, 2, 1, 1, 5, 2, 1, 2, 2, 2, 3]
def baseStart_3859820 : Nat := 118140960795 + 3859820 * 2 ^ 59
def prefixEnd_3859820 : Nat := 4983230072969 + 3 ^ 40 * 3859820 * 2
def baseEnd_3859820 : Nat := 1981942899837193670199017

theorem tailTrace_3859820 : CollatzResearch.WordTrace tailWord_3859820 prefixEnd_3859820 1981942899837193670199017 := by
  unfold tailWord_3859820
  simp only [CollatzResearch.WordTrace]
  refine ⟨70389600438269409809568457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93852800584359213079424609 70389600438269409809568457)
  ·
    refine ⟨52792200328702057357176343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70389600438269409809568457 52792200328702057357176343)
    ·
      refine ⟨79188300493053086035764515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52792200328702057357176343 79188300493053086035764515)
      ·
        refine ⟨118782450739579629053646773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79188300493053086035764515 118782450739579629053646773)
        ·
          refine ⟨11135854756835590223779385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 118782450739579629053646773 11135854756835590223779385)
          ·
            refine ⟨8351891067626692667834539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11135854756835590223779385 8351891067626692667834539)
            ·
              refine ⟨12527836601440039001751809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8351891067626692667834539 12527836601440039001751809)
              ·
                refine ⟨9395877451080029251313857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12527836601440039001751809 9395877451080029251313857)
                ·
                  refine ⟨7046908088310021938485393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9395877451080029251313857 7046908088310021938485393)
                  ·
                    refine ⟨5285181066232516453864045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7046908088310021938485393 5285181066232516453864045)
                    ·
                      refine ⟨1981942899837193670199017, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5285181066232516453864045 1981942899837193670199017)
                      ·
                        rfl

theorem cell23_3859820_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 2, 2, 3].length) (baseStart_3859820 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3859820 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3859820 prefixEnd_3859820 := by exact prefixLift 3859820
  have htrace : WordTrace (prefixWord ++ tailWord_3859820) baseStart_3859820 baseEnd_3859820 := by
    simpa [prefixWord, tailWord_3859820, baseEnd_3859820] using wordTrace_append hprefix tailTrace_3859820
  have hstable : (prefixWord ++ tailWord_3859820).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3859820).length < 2 ^ (prefixWord ++ tailWord_3859820).sum := by decide
  have hdescent : baseEnd_3859820 < baseStart_3859820 := by decide
  rcases family_descends (prefixWord ++ tailWord_3859820) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3859884 : List Nat := [2, 2, 1, 1, 1, 1, 8, 2, 1, 1, 3]
def baseStart_3859884 : Nat := 118140960795 + 3859884 * 2 ^ 59
def prefixEnd_3859884 : Nat := 4983230072969 + 3 ^ 40 * 3859884 * 2
def baseEnd_3859884 : Nat := 1981975762599081419798723

theorem tailTrace_3859884 : CollatzResearch.WordTrace tailWord_3859884 prefixEnd_3859884 1981975762599081419798723 := by
  unfold tailWord_3859884
  simp only [CollatzResearch.WordTrace]
  refine ⟨70390767574153479274733353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93854356765537972366311137 70390767574153479274733353)
  ·
    refine ⟨52793075680615109456050015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70390767574153479274733353 52793075680615109456050015)
    ·
      refine ⟨79189613520922664184075023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52793075680615109456050015 79189613520922664184075023)
      ·
        refine ⟨118784420281383996276112535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79189613520922664184075023 118784420281383996276112535)
        ·
          refine ⟨178176630422075994414168803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 118784420281383996276112535 178176630422075994414168803)
          ·
            refine ⟨267264945633113991621253205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 178176630422075994414168803 267264945633113991621253205)
            ·
              refine ⟨3132011081638054589311561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 267264945633113991621253205 3132011081638054589311561)
              ·
                refine ⟨2349008311228540941983671, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3132011081638054589311561 2349008311228540941983671)
                ·
                  refine ⟨3523512466842811412975507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2349008311228540941983671 3523512466842811412975507)
                  ·
                    refine ⟨5285268700264217119463261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3523512466842811412975507 5285268700264217119463261)
                    ·
                      refine ⟨1981975762599081419798723, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5285268700264217119463261 1981975762599081419798723)
                      ·
                        rfl

theorem cell23_3859884_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 8, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 8, 2, 1, 1, 3].length) (baseStart_3859884 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3859884 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3859884 prefixEnd_3859884 := by exact prefixLift 3859884
  have htrace : WordTrace (prefixWord ++ tailWord_3859884) baseStart_3859884 baseEnd_3859884 := by
    simpa [prefixWord, tailWord_3859884, baseEnd_3859884] using wordTrace_append hprefix tailTrace_3859884
  have hstable : (prefixWord ++ tailWord_3859884).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3859884).length < 2 ^ (prefixWord ++ tailWord_3859884).sum := by decide
  have hdescent : baseEnd_3859884 < baseStart_3859884 := by decide
  rcases family_descends (prefixWord ++ tailWord_3859884) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3859941 : List Nat := [1, 3, 1, 5, 1, 1, 2, 4, 1, 2, 2]
def baseStart_3859941 : Nat := 118140960795 + 3859941 * 2 ^ 59
def prefixEnd_3859941 : Nat := 4983230072969 + 3 ^ 40 * 3859941 * 2
def baseEnd_3859941 : Nat := 1982005030996387696785961

theorem tailTrace_3859941 : CollatzResearch.WordTrace tailWord_3859941 prefixEnd_3859941 1982005030996387696785961 := by
  unfold tailWord_3859941
  simp only [CollatzResearch.WordTrace]
  refine ⟨140783614109100457284291677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93855742739400304856194451 140783614109100457284291677)
  ·
    refine ⟨52793855290912671481609379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 140783614109100457284291677 52793855290912671481609379)
    ·
      refine ⟨79190782936369007222414069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52793855290912671481609379 79190782936369007222414069)
      ·
        refine ⟨7424135900284594427101319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 79190782936369007222414069 7424135900284594427101319)
        ·
          refine ⟨11136203850426891640651979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7424135900284594427101319 11136203850426891640651979)
          ·
            refine ⟨16704305775640337460977969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11136203850426891640651979 16704305775640337460977969)
            ·
              refine ⟨12528229331730253095733477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16704305775640337460977969 12528229331730253095733477)
              ·
                refine ⟨2349042999699422455450027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12528229331730253095733477 2349042999699422455450027)
                ·
                  refine ⟨3523564499549133683175041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2349042999699422455450027 3523564499549133683175041)
                  ·
                    refine ⟨2642673374661850262381281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3523564499549133683175041 2642673374661850262381281)
                    ·
                      refine ⟨1982005030996387696785961, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2642673374661850262381281 1982005030996387696785961)
                      ·
                        rfl

theorem cell23_3859941_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 1, 2, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 1, 2, 4, 1, 2, 2].length) (baseStart_3859941 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3859941 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3859941 prefixEnd_3859941 := by exact prefixLift 3859941
  have htrace : WordTrace (prefixWord ++ tailWord_3859941) baseStart_3859941 baseEnd_3859941 := by
    simpa [prefixWord, tailWord_3859941, baseEnd_3859941] using wordTrace_append hprefix tailTrace_3859941
  have hstable : (prefixWord ++ tailWord_3859941).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3859941).length < 2 ^ (prefixWord ++ tailWord_3859941).sum := by decide
  have hdescent : baseEnd_3859941 < baseStart_3859941 := by decide
  rcases family_descends (prefixWord ++ tailWord_3859941) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3860008 : List Nat := [2, 1, 5, 2, 2, 2, 2, 1, 2, 1, 3]
def baseStart_3860008 : Nat := 118140960795 + 3860008 * 2 ^ 59
def prefixEnd_3860008 : Nat := 4983230072969 + 3 ^ 40 * 3860008 * 2
def baseEnd_3860008 : Nat := 1982039434200238934648153

theorem tailTrace_3860008 : CollatzResearch.WordTrace tailWord_3860008 prefixEnd_3860008 1982039434200238934648153 := by
  unfold tailWord_3860008
  simp only [CollatzResearch.WordTrace]
  refine ⟨70393028899928863863490339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93857371866571818484653785 70393028899928863863490339)
  ·
    refine ⟨105589543349893295795235509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70393028899928863863490339 105589543349893295795235509)
    ·
      refine ⟨9899019689052496480803329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 105589543349893295795235509 9899019689052496480803329)
      ·
        refine ⟨7424264766789372360602497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9899019689052496480803329 7424264766789372360602497)
        ·
          refine ⟨5568198575092029270451873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7424264766789372360602497 5568198575092029270451873)
          ·
            refine ⟨4176148931319021952838905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5568198575092029270451873 4176148931319021952838905)
            ·
              refine ⟨3132111698489266464629179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4176148931319021952838905 3132111698489266464629179)
              ·
                refine ⟨4698167547733899696943769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3132111698489266464629179 4698167547733899696943769)
                ·
                  refine ⟨3523625660800424772707827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4698167547733899696943769 3523625660800424772707827)
                  ·
                    refine ⟨5285438491200637159061741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3523625660800424772707827 5285438491200637159061741)
                    ·
                      refine ⟨1982039434200238934648153, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5285438491200637159061741 1982039434200238934648153)
                      ·
                        rfl

theorem cell23_3860008_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 2, 2, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 2, 2, 2, 1, 2, 1, 3].length) (baseStart_3860008 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3860008 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3860008 prefixEnd_3860008 := by exact prefixLift 3860008
  have htrace : WordTrace (prefixWord ++ tailWord_3860008) baseStart_3860008 baseEnd_3860008 := by
    simpa [prefixWord, tailWord_3860008, baseEnd_3860008] using wordTrace_append hprefix tailTrace_3860008
  have hstable : (prefixWord ++ tailWord_3860008).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3860008).length < 2 ^ (prefixWord ++ tailWord_3860008).sum := by decide
  have hdescent : baseEnd_3860008 < baseStart_3860008 := by decide
  rcases family_descends (prefixWord ++ tailWord_3860008) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3860010 : List Nat := [3, 1, 4, 1, 1, 1, 2, 1, 1, 4, 4]
def baseStart_3860010 : Nat := 118140960795 + 3860010 * 2 ^ 59
def prefixEnd_3860010 : Nat := 4983230072969 + 3 ^ 40 * 3860010 * 2
def baseEnd_3860010 : Nat := 1982040461161547926823143

theorem tailTrace_3860010 : CollatzResearch.WordTrace tailWord_3860010 prefixEnd_3860010 1982040461161547926823143 := by
  unfold tailWord_3860010
  simp only [CollatzResearch.WordTrace]
  refine ⟨35196532686462620517138371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 93857420497233654712368989 35196532686462620517138371)
  ·
    refine ⟨52794799029693930775707557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35196532686462620517138371 52794799029693930775707557)
    ·
      refine ⟨9899024818067612020445167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 52794799029693930775707557 9899024818067612020445167)
      ·
        refine ⟨14848537227101418030667751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9899024818067612020445167 14848537227101418030667751)
        ·
          refine ⟨22272805840652127046001627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14848537227101418030667751 22272805840652127046001627)
          ·
            refine ⟨33409208760978190569002441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22272805840652127046001627 33409208760978190569002441)
            ·
              refine ⟨25056906570733642926751831, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33409208760978190569002441 25056906570733642926751831)
              ·
                refine ⟨37585359856100464390127747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25056906570733642926751831 37585359856100464390127747)
                ·
                  refine ⟨56378039784150696585191621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37585359856100464390127747 56378039784150696585191621)
                  ·
                    refine ⟨10570882459528255609723429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 56378039784150696585191621 10570882459528255609723429)
                    ·
                      refine ⟨1982040461161547926823143, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10570882459528255609723429 1982040461161547926823143)
                      ·
                        rfl

theorem cell23_3860010_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 2, 1, 1, 4, 4].length) (baseStart_3860010 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3860010 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3860010 prefixEnd_3860010 := by exact prefixLift 3860010
  have htrace : WordTrace (prefixWord ++ tailWord_3860010) baseStart_3860010 baseEnd_3860010 := by
    simpa [prefixWord, tailWord_3860010, baseEnd_3860010] using wordTrace_append hprefix tailTrace_3860010
  have hstable : (prefixWord ++ tailWord_3860010).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3860010).length < 2 ^ (prefixWord ++ tailWord_3860010).sum := by decide
  have hdescent : baseEnd_3860010 < baseStart_3860010 := by decide
  rcases family_descends (prefixWord ++ tailWord_3860010) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3860063 : List Nat := [1, 1, 2, 3, 1, 1, 1, 1, 4, 8]
def baseStart_3860063 : Nat := 118140960795 + 3860063 * 2 ^ 59
def prefixEnd_3860063 : Nat := 4983230072969 + 3 ^ 40 * 3860063 * 2
def baseEnd_3860063 : Nat := 660689225212078739820133

theorem tailTrace_3860063 : CollatzResearch.WordTrace tailWord_3860063 prefixEnd_3860063 660689225212078739820133 := by
  unfold tailWord_3860063
  simp only [CollatzResearch.WordTrace]
  refine ⟨140788063814658472120232843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93858709209772314746821895 140788063814658472120232843)
  ·
    refine ⟨211182095721987708180349265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140788063814658472120232843 211182095721987708180349265)
    ·
      refine ⟨158386571791490781135261949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 211182095721987708180349265 158386571791490781135261949)
      ·
        refine ⟨59394964421809042925723231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 158386571791490781135261949 59394964421809042925723231)
        ·
          refine ⟨89092446632713564388584847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59394964421809042925723231 89092446632713564388584847)
          ·
            refine ⟨133638669949070346582877271, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 89092446632713564388584847 133638669949070346582877271)
            ·
              refine ⟨200458004923605519874315907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 133638669949070346582877271 200458004923605519874315907)
              ·
                refine ⟨300687007385408279811473861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 200458004923605519874315907 300687007385408279811473861)
                ·
                  refine ⟨56378813884764052464651349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 300687007385408279811473861 56378813884764052464651349)
                  ·
                    refine ⟨660689225212078739820133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 56378813884764052464651349 660689225212078739820133)
                    ·
                      rfl

theorem cell23_3860063_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 1, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 1, 1, 4, 8].length) (baseStart_3860063 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3860063 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3860063 prefixEnd_3860063 := by exact prefixLift 3860063
  have htrace : WordTrace (prefixWord ++ tailWord_3860063) baseStart_3860063 baseEnd_3860063 := by
    simpa [prefixWord, tailWord_3860063, baseEnd_3860063] using wordTrace_append hprefix tailTrace_3860063
  have hstable : (prefixWord ++ tailWord_3860063).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3860063).length < 2 ^ (prefixWord ++ tailWord_3860063).sum := by decide
  have hdescent : baseEnd_3860063 < baseStart_3860063 := by decide
  rcases family_descends (prefixWord ++ tailWord_3860063) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3860147 : List Nat := [1, 1, 1, 2, 3, 3, 1, 3, 1, 5, 2]
def baseStart_3860147 : Nat := 118140960795 + 3860147 * 2 ^ 59
def prefixEnd_3860147 : Nat := 4983230072969 + 3 ^ 40 * 3860147 * 2
def baseEnd_3860147 : Nat := 1982110808011213890810013

theorem tailTrace_3860147 : CollatzResearch.WordTrace tailWord_3860147 prefixEnd_3860147 1982110808011213890810013 := by
  unfold tailWord_3860147
  simp only [CollatzResearch.WordTrace]
  refine ⟨140791127546354154466290695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93860751697569436310860463 140791127546354154466290695)
  ·
    refine ⟨211186691319531231699436043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140791127546354154466290695 211186691319531231699436043)
    ·
      refine ⟨316780036979296847549154065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 211186691319531231699436043 316780036979296847549154065)
      ·
        refine ⟨237585027734472635661865549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 316780036979296847549154065 237585027734472635661865549)
        ·
          refine ⟨89094385400427238373199581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 237585027734472635661865549 89094385400427238373199581)
          ·
            refine ⟨33410394525160214389949843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 89094385400427238373199581 33410394525160214389949843)
            ·
              refine ⟨50115591787740321584924765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33410394525160214389949843 50115591787740321584924765)
              ·
                refine ⟨18793346920402620594346787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 50115591787740321584924765 18793346920402620594346787)
                ·
                  refine ⟨28190020380603930891520181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18793346920402620594346787 28190020380603930891520181)
                  ·
                    refine ⟨2642814410681618521080017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 28190020380603930891520181 2642814410681618521080017)
                    ·
                      refine ⟨1982110808011213890810013, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2642814410681618521080017 1982110808011213890810013)
                      ·
                        rfl

theorem cell23_3860147_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 1, 3, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 1, 3, 1, 5, 2].length) (baseStart_3860147 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3860147 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3860147 prefixEnd_3860147 := by exact prefixLift 3860147
  have htrace : WordTrace (prefixWord ++ tailWord_3860147) baseStart_3860147 baseEnd_3860147 := by
    simpa [prefixWord, tailWord_3860147, baseEnd_3860147] using wordTrace_append hprefix tailTrace_3860147
  have hstable : (prefixWord ++ tailWord_3860147).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3860147).length < 2 ^ (prefixWord ++ tailWord_3860147).sum := by decide
  have hdescent : baseEnd_3860147 < baseStart_3860147 := by decide
  rcases family_descends (prefixWord ++ tailWord_3860147) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3860157 : List Nat := [1, 4, 1, 2, 1, 2, 1, 5, 1, 5]
def baseStart_3860157 : Nat := 118140960795 + 3860157 * 2 ^ 59
def prefixEnd_3860157 : Nat := 4983230072969 + 3 ^ 40 * 3860157 * 2
def baseEnd_3860157 : Nat := 660705314272586283894989

theorem tailTrace_3860157 : CollatzResearch.WordTrace tailWord_3860157 prefixEnd_3860157 660705314272586283894989 := by
  unfold tailWord_3860157
  simp only [CollatzResearch.WordTrace]
  refine ⟨140791492276317926174154725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93860994850878617449436483 140791492276317926174154725)
  ·
    refine ⟨26398404801809611157654011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 140791492276317926174154725 26398404801809611157654011)
    ·
      refine ⟨39597607202714416736481017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26398404801809611157654011 39597607202714416736481017)
      ·
        refine ⟨29698205402035812552360763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39597607202714416736481017 29698205402035812552360763)
        ·
          refine ⟨44547308103053718828541145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29698205402035812552360763 44547308103053718828541145)
          ·
            refine ⟨33410481077290289121405859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44547308103053718828541145 33410481077290289121405859)
            ·
              refine ⟨50115721615935433682108789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33410481077290289121405859 50115721615935433682108789)
              ·
                refine ⟨4698348901493946907697699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 50115721615935433682108789 4698348901493946907697699)
                ·
                  refine ⟨7047523352240920361546549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4698348901493946907697699 7047523352240920361546549)
                  ·
                    refine ⟨660705314272586283894989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7047523352240920361546549 660705314272586283894989)
                    ·
                      rfl

theorem cell23_3860157_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 1, 5, 1, 5].length) (baseStart_3860157 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3860157 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3860157 prefixEnd_3860157 := by exact prefixLift 3860157
  have htrace : WordTrace (prefixWord ++ tailWord_3860157) baseStart_3860157 baseEnd_3860157 := by
    simpa [prefixWord, tailWord_3860157, baseEnd_3860157] using wordTrace_append hprefix tailTrace_3860157
  have hstable : (prefixWord ++ tailWord_3860157).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3860157).length < 2 ^ (prefixWord ++ tailWord_3860157).sum := by decide
  have hdescent : baseEnd_3860157 < baseStart_3860157 := by decide
  rcases family_descends (prefixWord ++ tailWord_3860157) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3860207 : List Nat := [1, 1, 2, 1, 5, 1, 3, 2, 1, 2, 4]
def baseStart_3860207 : Nat := 118140960795 + 3860207 * 2 ^ 59
def prefixEnd_3860207 : Nat := 4983230072969 + 3 ^ 40 * 3860207 * 2
def baseEnd_3860207 : Nat := 1982141616850483656059737

theorem tailTrace_3860207 : CollatzResearch.WordTrace tailWord_3860207 prefixEnd_3860207 1982141616850483656059737 := by
  unfold tailWord_3860207
  simp only [CollatzResearch.WordTrace]
  refine ⟨140793315926136784713474875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93862210617424523142316583 140793315926136784713474875)
  ·
    refine ⟨211189973889205177070212313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140793315926136784713474875 211189973889205177070212313)
    ·
      refine ⟨158392480416903882802659235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 211189973889205177070212313 158392480416903882802659235)
      ·
        refine ⟨237588720625355824203988853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 158392480416903882802659235 237588720625355824203988853)
        ·
          refine ⟨22273942558627108519123955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 237588720625355824203988853 22273942558627108519123955)
          ·
            refine ⟨33410913837940662778685933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22273942558627108519123955 33410913837940662778685933)
            ·
              refine ⟨12529092689227748542007225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33410913837940662778685933 12529092689227748542007225)
              ·
                refine ⟨9396819516920811406505419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12529092689227748542007225 9396819516920811406505419)
                ·
                  refine ⟨14095229275381217109758129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9396819516920811406505419 14095229275381217109758129)
                  ·
                    refine ⟨10571421956535912832318597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14095229275381217109758129 10571421956535912832318597)
                    ·
                      refine ⟨1982141616850483656059737, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10571421956535912832318597 1982141616850483656059737)
                      ·
                        rfl

theorem cell23_3860207_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 3, 2, 1, 2, 4].length) (baseStart_3860207 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3860207 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3860207 prefixEnd_3860207 := by exact prefixLift 3860207
  have htrace : WordTrace (prefixWord ++ tailWord_3860207) baseStart_3860207 baseEnd_3860207 := by
    simpa [prefixWord, tailWord_3860207, baseEnd_3860207] using wordTrace_append hprefix tailTrace_3860207
  have hstable : (prefixWord ++ tailWord_3860207).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3860207).length < 2 ^ (prefixWord ++ tailWord_3860207).sum := by decide
  have hdescent : baseEnd_3860207 < baseStart_3860207 := by decide
  rcases family_descends (prefixWord ++ tailWord_3860207) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3860214 : List Nat := [5, 1, 1, 1, 1, 3, 3, 1, 1, 1, 5]
def baseStart_3860214 : Nat := 118140960795 + 3860214 * 2 ^ 59
def prefixEnd_3860214 : Nat := 4983230072969 + 3 ^ 40 * 3860214 * 2
def baseEnd_3860214 : Nat := 1982145211215065128672205

theorem tailTrace_3860214 : CollatzResearch.WordTrace tailWord_3860214 prefixEnd_3860214 1982145211215065128672205 := by
  unfold tailWord_3860214
  simp only [CollatzResearch.WordTrace]
  refine ⟨8799598202319464056811231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 93862380824740949939319797 8799598202319464056811231)
  ·
    refine ⟨13199397303479196085216847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8799598202319464056811231 13199397303479196085216847)
    ·
      refine ⟨19799095955218794127825271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13199397303479196085216847 19799095955218794127825271)
      ·
        refine ⟨29698643932828191191737907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19799095955218794127825271 29698643932828191191737907)
        ·
          refine ⟨44547965899242286787606861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29698643932828191191737907 44547965899242286787606861)
          ·
            refine ⟨16705487212215857545352573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 44547965899242286787606861 16705487212215857545352573)
            ·
              refine ⟨6264557704580946579507215, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16705487212215857545352573 6264557704580946579507215)
              ·
                refine ⟨9396836556871419869260823, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6264557704580946579507215 9396836556871419869260823)
                ·
                  refine ⟨14095254835307129803891235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9396836556871419869260823 14095254835307129803891235)
                  ·
                    refine ⟨21142882252960694705836853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14095254835307129803891235 21142882252960694705836853)
                    ·
                      refine ⟨1982145211215065128672205, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 21142882252960694705836853 1982145211215065128672205)
                      ·
                        rfl

theorem cell23_3860214_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 3, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 3, 3, 1, 1, 1, 5].length) (baseStart_3860214 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3860214 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3860214 prefixEnd_3860214 := by exact prefixLift 3860214
  have htrace : WordTrace (prefixWord ++ tailWord_3860214) baseStart_3860214 baseEnd_3860214 := by
    simpa [prefixWord, tailWord_3860214, baseEnd_3860214] using wordTrace_append hprefix tailTrace_3860214
  have hstable : (prefixWord ++ tailWord_3860214).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3860214).length < 2 ^ (prefixWord ++ tailWord_3860214).sum := by decide
  have hdescent : baseEnd_3860214 < baseStart_3860214 := by decide
  rcases family_descends (prefixWord ++ tailWord_3860214) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3860222 : List Nat := [4, 2, 2, 1, 3, 2, 2, 2, 1, 1, 3]
def baseStart_3860222 : Nat := 118140960795 + 3860222 * 2 ^ 59
def prefixEnd_3860222 : Nat := 4983230072969 + 3 ^ 40 * 3860222 * 2
def baseEnd_3860222 : Nat := 1982149319060301097372169

theorem tailTrace_3860222 : CollatzResearch.WordTrace tailWord_3860222 prefixEnd_3860222 1982149319060301097372169 := by
  unfold tailWord_3860222
  simp only [CollatzResearch.WordTrace]
  refine ⟨17599232877635305284408865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 93862575347388294850180613 17599232877635305284408865)
  ·
    refine ⟨13199424658226478963306649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17599232877635305284408865 13199424658226478963306649)
    ·
      refine ⟨9899568493669859222479987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13199424658226478963306649 9899568493669859222479987)
      ·
        refine ⟨14849352740504788833719981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9899568493669859222479987 14849352740504788833719981)
        ·
          refine ⟨5568507277689295812644993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14849352740504788833719981 5568507277689295812644993)
          ·
            refine ⟨4176380458266971859483745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5568507277689295812644993 4176380458266971859483745)
            ·
              refine ⟨3132285343700228894612809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4176380458266971859483745 3132285343700228894612809)
              ·
                refine ⟨2349214007775171670959607, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3132285343700228894612809 2349214007775171670959607)
                ·
                  refine ⟨3523821011662757506439411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2349214007775171670959607 3523821011662757506439411)
                  ·
                    refine ⟨5285731517494136259659117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3523821011662757506439411 5285731517494136259659117)
                    ·
                      refine ⟨1982149319060301097372169, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5285731517494136259659117 1982149319060301097372169)
                      ·
                        rfl

theorem cell23_3860222_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 3, 2, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 3, 2, 2, 2, 1, 1, 3].length) (baseStart_3860222 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3860222 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3860222 prefixEnd_3860222 := by exact prefixLift 3860222
  have htrace : WordTrace (prefixWord ++ tailWord_3860222) baseStart_3860222 baseEnd_3860222 := by
    simpa [prefixWord, tailWord_3860222, baseEnd_3860222] using wordTrace_append hprefix tailTrace_3860222
  have hstable : (prefixWord ++ tailWord_3860222).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3860222).length < 2 ^ (prefixWord ++ tailWord_3860222).sum := by decide
  have hdescent : baseEnd_3860222 < baseStart_3860222 := by decide
  rcases family_descends (prefixWord ++ tailWord_3860222) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3860278 : List Nat := [5, 1, 2, 2, 1, 2, 1, 1, 4, 1, 3]
def baseStart_3860278 : Nat := 118140960795 + 3860278 * 2 ^ 59
def prefixEnd_3860278 : Nat := 4983230072969 + 3 ^ 40 * 3860278 * 2
def baseEnd_3860278 : Nat := 1982178073976952878271911

theorem tailTrace_3860278 : CollatzResearch.WordTrace tailWord_3860278 prefixEnd_3860278 1982178073976952878271911 := by
  unfold tailWord_3860278
  simp only [CollatzResearch.WordTrace]
  refine ⟨8799744094304972739956843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 93863937005919709226206325 8799744094304972739956843)
  ·
    refine ⟨13199616141457459109935265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8799744094304972739956843 13199616141457459109935265)
    ·
      refine ⟨9899712106093094332451449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13199616141457459109935265 9899712106093094332451449)
      ·
        refine ⟨7424784079569820749338587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9899712106093094332451449 7424784079569820749338587)
        ·
          refine ⟨11137176119354731124007881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7424784079569820749338587 11137176119354731124007881)
          ·
            refine ⟨8352882089516048343005911, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11137176119354731124007881 8352882089516048343005911)
            ·
              refine ⟨12529323134274072514508867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8352882089516048343005911 12529323134274072514508867)
              ·
                refine ⟨18793984701411108771763301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12529323134274072514508867 18793984701411108771763301)
                ·
                  refine ⟨3523872131514582894705619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 18793984701411108771763301 3523872131514582894705619)
                  ·
                    refine ⟨5285808197271874342058429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3523872131514582894705619 5285808197271874342058429)
                    ·
                      refine ⟨1982178073976952878271911, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5285808197271874342058429 1982178073976952878271911)
                      ·
                        rfl

theorem cell23_3860278_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 2, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 2, 1, 1, 4, 1, 3].length) (baseStart_3860278 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3860278 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3860278 prefixEnd_3860278 := by exact prefixLift 3860278
  have htrace : WordTrace (prefixWord ++ tailWord_3860278) baseStart_3860278 baseEnd_3860278 := by
    simpa [prefixWord, tailWord_3860278, baseEnd_3860278] using wordTrace_append hprefix tailTrace_3860278
  have hstable : (prefixWord ++ tailWord_3860278).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3860278).length < 2 ^ (prefixWord ++ tailWord_3860278).sum := by decide
  have hdescent : baseEnd_3860278 < baseStart_3860278 := by decide
  rcases family_descends (prefixWord ++ tailWord_3860278) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3860284 : List Nat := [2, 2, 2, 2, 1, 1, 2, 2, 3, 4, 2]
def baseStart_3860284 : Nat := 118140960795 + 3860284 * 2 ^ 59
def prefixEnd_3860284 : Nat := 4983230072969 + 3 ^ 40 * 3860284 * 2
def baseEnd_3860284 : Nat := 1982181154860879854796883

theorem tailTrace_3860284 : CollatzResearch.WordTrace tailWord_3860284 prefixEnd_3860284 1982181154860879854796883 := by
  unfold tailWord_3860284
  simp only [CollatzResearch.WordTrace]
  refine ⟨70398062173428913432013953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93864082897905217909351937 70398062173428913432013953)
  ·
    refine ⟨52798546630071685074010465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70398062173428913432013953 52798546630071685074010465)
    ·
      refine ⟨39598909972553763805507849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52798546630071685074010465 39598909972553763805507849)
      ·
        refine ⟨29699182479415322854130887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39598909972553763805507849 29699182479415322854130887)
        ·
          refine ⟨44548773719122984281196331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29699182479415322854130887 44548773719122984281196331)
          ·
            refine ⟨66823160578684476421794497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44548773719122984281196331 66823160578684476421794497)
            ·
              refine ⟨50117370434013357316345873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 66823160578684476421794497 50117370434013357316345873)
              ·
                refine ⟨37588027825510017987259405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 50117370434013357316345873 37588027825510017987259405)
                ·
                  refine ⟨14095510434566256745222277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 37588027825510017987259405 14095510434566256745222277)
                  ·
                    refine ⟨2642908206481173139729177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 14095510434566256745222277 2642908206481173139729177)
                    ·
                      refine ⟨1982181154860879854796883, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2642908206481173139729177 1982181154860879854796883)
                      ·
                        rfl

theorem cell23_3860284_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 2, 2, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 2, 2, 3, 4, 2].length) (baseStart_3860284 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3860284 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3860284 prefixEnd_3860284 := by exact prefixLift 3860284
  have htrace : WordTrace (prefixWord ++ tailWord_3860284) baseStart_3860284 baseEnd_3860284 := by
    simpa [prefixWord, tailWord_3860284, baseEnd_3860284] using wordTrace_append hprefix tailTrace_3860284
  have hstable : (prefixWord ++ tailWord_3860284).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3860284).length < 2 ^ (prefixWord ++ tailWord_3860284).sum := by decide
  have hdescent : baseEnd_3860284 < baseStart_3860284 := by decide
  rcases family_descends (prefixWord ++ tailWord_3860284) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3860297 : List Nat := [1, 2, 1, 1, 2, 4, 1, 3, 2, 2, 4]
def baseStart_3860297 : Nat := 118140960795 + 3860297 * 2 ^ 59
def prefixEnd_3860297 : Nat := 4983230072969 + 3 ^ 40 * 3860297 * 2
def baseEnd_3860297 : Nat := 1982187830109388303934323

theorem tailTrace_3860297 : CollatzResearch.WordTrace tailWord_3860297 prefixEnd_3860297 1982187830109388303934323 := by
  unfold tailWord_3860297
  simp only [CollatzResearch.WordTrace]
  refine ⟨140796598495810730084251145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93864398997207153389500763 140796598495810730084251145)
  ·
    refine ⟨105597448871858047563188359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 140796598495810730084251145 105597448871858047563188359)
    ·
      refine ⟨158396173307787071344782539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105597448871858047563188359 158396173307787071344782539)
      ·
        refine ⟨237594259961680607017173809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 158396173307787071344782539 237594259961680607017173809)
        ·
          refine ⟨178195694971260455262880357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 237594259961680607017173809 178195694971260455262880357)
          ·
            refine ⟨33411692807111335361790067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 178195694971260455262880357 33411692807111335361790067)
            ·
              refine ⟨50117539210667003042685101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33411692807111335361790067 50117539210667003042685101)
              ·
                refine ⟨18794077204000126141006913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 50117539210667003042685101 18794077204000126141006913)
                ·
                  refine ⟨14095557903000094605755185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18794077204000126141006913 14095557903000094605755185)
                  ·
                    refine ⟨10571668427250070954316389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14095557903000094605755185 10571668427250070954316389)
                    ·
                      refine ⟨1982187830109388303934323, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10571668427250070954316389 1982187830109388303934323)
                      ·
                        rfl

theorem cell23_3860297_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 1, 3, 2, 2, 4].length) (baseStart_3860297 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3860297 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3860297 prefixEnd_3860297 := by exact prefixLift 3860297
  have htrace : WordTrace (prefixWord ++ tailWord_3860297) baseStart_3860297 baseEnd_3860297 := by
    simpa [prefixWord, tailWord_3860297, baseEnd_3860297] using wordTrace_append hprefix tailTrace_3860297
  have hstable : (prefixWord ++ tailWord_3860297).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3860297).length < 2 ^ (prefixWord ++ tailWord_3860297).sum := by decide
  have hdescent : baseEnd_3860297 < baseStart_3860297 := by decide
  rcases family_descends (prefixWord ++ tailWord_3860297) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3860387 : List Nat := [1, 1, 1, 4, 1, 2, 1, 3, 2, 1, 6]
def baseStart_3860387 : Nat := 118140960795 + 3860387 * 2 ^ 59
def prefixEnd_3860387 : Nat := 4983230072969 + 3 ^ 40 * 3860387 * 2
def baseEnd_3860387 : Nat := 1982234043368292951808909

theorem tailTrace_3860387 : CollatzResearch.WordTrace tailWord_3860387 prefixEnd_3860387 1982234043368292951808909 := by
  unfold tailWord_3860387
  simp only [CollatzResearch.WordTrace]
  refine ⟨140799881065484675455027415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93866587376989783636684943 140799881065484675455027415)
  ·
    refine ⟨211199821598227013182541123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140799881065484675455027415 211199821598227013182541123)
    ·
      refine ⟨316799732397340519773811685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 211199821598227013182541123 316799732397340519773811685)
      ·
        refine ⟨59399949824501347457589691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 316799732397340519773811685 59399949824501347457589691)
        ·
          refine ⟨89099924736752021186384537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59399949824501347457589691 89099924736752021186384537)
          ·
            refine ⟨66824943552564015889788403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 89099924736752021186384537 66824943552564015889788403)
            ·
              refine ⟨100237415328846023834682605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 66824943552564015889788403 100237415328846023834682605)
              ·
                refine ⟨37589030748317258938005977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 100237415328846023834682605 37589030748317258938005977)
                ·
                  refine ⟨28191773061237944203504483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 37589030748317258938005977 28191773061237944203504483)
                  ·
                    refine ⟨42287659591856916305256725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 28191773061237944203504483 42287659591856916305256725)
                    ·
                      refine ⟨1982234043368292951808909, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 42287659591856916305256725 1982234043368292951808909)
                      ·
                        rfl

theorem cell23_3860387_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 1, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 1, 3, 2, 1, 6].length) (baseStart_3860387 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3860387 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3860387 prefixEnd_3860387 := by exact prefixLift 3860387
  have htrace : WordTrace (prefixWord ++ tailWord_3860387) baseStart_3860387 baseEnd_3860387 := by
    simpa [prefixWord, tailWord_3860387, baseEnd_3860387] using wordTrace_append hprefix tailTrace_3860387
  have hstable : (prefixWord ++ tailWord_3860387).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3860387).length < 2 ^ (prefixWord ++ tailWord_3860387).sum := by decide
  have hdescent : baseEnd_3860387 < baseStart_3860387 := by decide
  rcases family_descends (prefixWord ++ tailWord_3860387) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3860391 : List Nat := [1, 1, 6, 1, 2, 1, 2, 2, 2, 1, 4]
def baseStart_3860391 : Nat := 118140960795 + 3860391 * 2 ^ 59
def prefixEnd_3860391 : Nat := 4983230072969 + 3 ^ 40 * 3860391 * 2
def baseEnd_3860391 : Nat := 1982236097290910936158891

theorem tailTrace_3860391 : CollatzResearch.WordTrace tailWord_3860391 prefixEnd_3860391 1982236097290910936158891 := by
  unfold tailWord_3860391
  simp only [CollatzResearch.WordTrace]
  refine ⟨140800026957470184138173027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93866684638313456092115351 140800026957470184138173027)
  ·
    refine ⟨211200040436205276207259541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140800026957470184138173027 211200040436205276207259541)
    ·
      refine ⟨9900001895447122322215291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 211200040436205276207259541 9900001895447122322215291)
      ·
        refine ⟨14850002843170683483322937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9900001895447122322215291 14850002843170683483322937)
        ·
          refine ⟨11137502132378012612492203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14850002843170683483322937 11137502132378012612492203)
          ·
            refine ⟨16706253198567018918738305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11137502132378012612492203 16706253198567018918738305)
            ·
              refine ⟨12529689898925264189053729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16706253198567018918738305 12529689898925264189053729)
              ·
                refine ⟨9397267424193948141790297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12529689898925264189053729 9397267424193948141790297)
                ·
                  refine ⟨7047950568145461106342723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9397267424193948141790297 7047950568145461106342723)
                  ·
                    refine ⟨10571925852218191659514085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7047950568145461106342723 10571925852218191659514085)
                    ·
                      refine ⟨1982236097290910936158891, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10571925852218191659514085 1982236097290910936158891)
                      ·
                        rfl

theorem cell23_3860391_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 1, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 1, 2, 2, 2, 1, 4].length) (baseStart_3860391 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3860391 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3860391 prefixEnd_3860391 := by exact prefixLift 3860391
  have htrace : WordTrace (prefixWord ++ tailWord_3860391) baseStart_3860391 baseEnd_3860391 := by
    simpa [prefixWord, tailWord_3860391, baseEnd_3860391] using wordTrace_append hprefix tailTrace_3860391
  have hstable : (prefixWord ++ tailWord_3860391).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3860391).length < 2 ^ (prefixWord ++ tailWord_3860391).sum := by decide
  have hdescent : baseEnd_3860391 < baseStart_3860391 := by decide
  rcases family_descends (prefixWord ++ tailWord_3860391) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3860392 : List Nat := [2, 1, 6, 2, 1, 2, 2, 2, 5]
def baseStart_3860392 : Nat := 118140960795 + 3860392 * 2 ^ 59
def prefixEnd_3860392 : Nat := 4983230072969 + 3 ^ 40 * 3860392 * 2
def baseEnd_3860392 : Nat := 220248512307951714694043

theorem tailTrace_3860392 : CollatzResearch.WordTrace tailWord_3860392 prefixEnd_3860392 220248512307951714694043 := by
  unfold tailWord_3860392
  simp only [CollatzResearch.WordTrace]
  refine ⟨70400031715233280654479715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93866708953644374205972953 70400031715233280654479715)
  ·
    refine ⟨105600047572849920981719573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70400031715233280654479715 105600047572849920981719573)
    ·
      refine ⟨4950002229977340046018105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 105600047572849920981719573 4950002229977340046018105)
      ·
        refine ⟨3712501672483005034513579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4950002229977340046018105 3712501672483005034513579)
        ·
          refine ⟨5568752508724507551770369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3712501672483005034513579 5568752508724507551770369)
          ·
            refine ⟨4176564381543380663827777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5568752508724507551770369 4176564381543380663827777)
            ·
              refine ⟨3132423286157535497870833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4176564381543380663827777 3132423286157535497870833)
              ·
                refine ⟨2349317464618151623403125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3132423286157535497870833 2349317464618151623403125)
                ·
                  refine ⟨220248512307951714694043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2349317464618151623403125 220248512307951714694043)
                  ·
                    rfl

theorem cell23_3860392_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 2, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 2, 1, 2, 2, 2, 5].length) (baseStart_3860392 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3860392 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3860392 prefixEnd_3860392 := by exact prefixLift 3860392
  have htrace : WordTrace (prefixWord ++ tailWord_3860392) baseStart_3860392 baseEnd_3860392 := by
    simpa [prefixWord, tailWord_3860392, baseEnd_3860392] using wordTrace_append hprefix tailTrace_3860392
  have hstable : (prefixWord ++ tailWord_3860392).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3860392).length < 2 ^ (prefixWord ++ tailWord_3860392).sum := by decide
  have hdescent : baseEnd_3860392 < baseStart_3860392 := by decide
  rcases family_descends (prefixWord ++ tailWord_3860392) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3860428 : List Nat := [2, 2, 1, 4, 1, 4, 1, 1, 2, 2, 3]
def baseStart_3860428 : Nat := 118140960795 + 3860428 * 2 ^ 59
def prefixEnd_3860428 : Nat := 4983230072969 + 3 ^ 40 * 3860428 * 2
def baseEnd_3860428 : Nat := 1982255096075127291396221

theorem tailTrace_3860428 : CollatzResearch.WordTrace tailWord_3860428 prefixEnd_3860428 1982255096075127291396221 := by
  unfold tailWord_3860428
  simp only [CollatzResearch.WordTrace]
  refine ⟨70400688229168069728634969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93867584305557426304846625 70400688229168069728634969)
  ·
    refine ⟨52800516171876052296476227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70400688229168069728634969 52800516171876052296476227)
    ·
      refine ⟨79200774257814078444714341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52800516171876052296476227 79200774257814078444714341)
      ·
        refine ⟨14850145173340139708383939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 79200774257814078444714341 14850145173340139708383939)
        ·
          refine ⟨22275217760010209562575909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14850145173340139708383939 22275217760010209562575909)
          ·
            refine ⟨4176603330001914292982983, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 22275217760010209562575909 4176603330001914292982983)
            ·
              refine ⟨6264904995002871439474475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4176603330001914292982983 6264904995002871439474475)
              ·
                refine ⟨9397357492504307159211713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6264904995002871439474475 9397357492504307159211713)
                ·
                  refine ⟨7048018119378230369408785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9397357492504307159211713 7048018119378230369408785)
                  ·
                    refine ⟨5286013589533672777056589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7048018119378230369408785 5286013589533672777056589)
                    ·
                      refine ⟨1982255096075127291396221, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5286013589533672777056589 1982255096075127291396221)
                      ·
                        rfl

theorem cell23_3860428_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 4, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 4, 1, 1, 2, 2, 3].length) (baseStart_3860428 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3860428 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3860428 prefixEnd_3860428 := by exact prefixLift 3860428
  have htrace : WordTrace (prefixWord ++ tailWord_3860428) baseStart_3860428 baseEnd_3860428 := by
    simpa [prefixWord, tailWord_3860428, baseEnd_3860428] using wordTrace_append hprefix tailTrace_3860428
  have hstable : (prefixWord ++ tailWord_3860428).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3860428).length < 2 ^ (prefixWord ++ tailWord_3860428).sum := by decide
  have hdescent : baseEnd_3860428 < baseStart_3860428 := by decide
  rcases family_descends (prefixWord ++ tailWord_3860428) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3860457 : List Nat := [1, 2, 1, 1, 1, 2, 1, 1, 1, 12]
def baseStart_3860457 : Nat := 118140960795 + 3860457 * 2 ^ 59
def prefixEnd_3860457 : Nat := 4983230072969 + 3 ^ 40 * 3860457 * 2
def baseEnd_3860457 : Nat := 660756662338035892644529

theorem tailTrace_3860457 : CollatzResearch.WordTrace tailWord_3860457 prefixEnd_3860457 660756662338035892644529 := by
  unfold tailWord_3860457
  simp only [CollatzResearch.WordTrace]
  refine ⟨140802434175231077410075625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93868289450154051606717083 140802434175231077410075625)
  ·
    refine ⟨105601825631423308057556719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 140802434175231077410075625 105601825631423308057556719)
    ·
      refine ⟨158402738447134962086335079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105601825631423308057556719 158402738447134962086335079)
      ·
        refine ⟨237604107670702443129502619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 158402738447134962086335079 237604107670702443129502619)
        ·
          refine ⟨356406161506053664694253929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 237604107670702443129502619 356406161506053664694253929)
          ·
            refine ⟨267304621129540248520690447, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 356406161506053664694253929 267304621129540248520690447)
            ·
              refine ⟨400956931694310372781035671, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 267304621129540248520690447 400956931694310372781035671)
              ·
                refine ⟨601435397541465559171553507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 400956931694310372781035671 601435397541465559171553507)
                ·
                  refine ⟨902153096312198338757330261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 601435397541465559171553507 902153096312198338757330261)
                  ·
                    refine ⟨660756662338035892644529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 12 902153096312198338757330261 660756662338035892644529)
                    ·
                      rfl

theorem cell23_3860457_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 1, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 1, 1, 12].length) (baseStart_3860457 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3860457 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3860457 prefixEnd_3860457 := by exact prefixLift 3860457
  have htrace : WordTrace (prefixWord ++ tailWord_3860457) baseStart_3860457 baseEnd_3860457 := by
    simpa [prefixWord, tailWord_3860457, baseEnd_3860457] using wordTrace_append hprefix tailTrace_3860457
  have hstable : (prefixWord ++ tailWord_3860457).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3860457).length < 2 ^ (prefixWord ++ tailWord_3860457).sum := by decide
  have hdescent : baseEnd_3860457 < baseStart_3860457 := by decide
  rcases family_descends (prefixWord ++ tailWord_3860457) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3860458 : List Nat := [3, 1, 3, 1, 2, 1, 4, 1, 3, 1, 3]
def baseStart_3860458 : Nat := 118140960795 + 3860458 * 2 ^ 59
def prefixEnd_3860458 : Nat := 4983230072969 + 3 ^ 40 * 3860458 * 2
def baseEnd_3860458 : Nat := 1982270500494762174021083

theorem tailTrace_3860458 : CollatzResearch.WordTrace tailWord_3860458 prefixEnd_3860458 1982270500494762174021083 := by
  unfold tailWord_3860458
  simp only [CollatzResearch.WordTrace]
  refine ⟨35200617662056863645215507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 93868313765484969720574685 35200617662056863645215507)
  ·
    refine ⟨52800926493085295467823261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35200617662056863645215507 52800926493085295467823261)
    ·
      refine ⟨19800347434906985800433723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 52800926493085295467823261 19800347434906985800433723)
      ·
        refine ⟨29700521152360478700650585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19800347434906985800433723 29700521152360478700650585)
        ·
          refine ⟨22275390864270359025487939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29700521152360478700650585 22275390864270359025487939)
          ·
            refine ⟨33413086296405538538231909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22275390864270359025487939 33413086296405538538231909)
            ·
              refine ⟨6264953680576038475918483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 33413086296405538538231909 6264953680576038475918483)
              ·
                refine ⟨9397430520864057713877725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6264953680576038475918483 9397430520864057713877725)
                ·
                  refine ⟨3524036445324021642704147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9397430520864057713877725 3524036445324021642704147)
                  ·
                    refine ⟨5286054667986032464056221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3524036445324021642704147 5286054667986032464056221)
                    ·
                      refine ⟨1982270500494762174021083, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5286054667986032464056221 1982270500494762174021083)
                      ·
                        rfl

theorem cell23_3860458_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 4, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 4, 1, 3, 1, 3].length) (baseStart_3860458 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3860458 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3860458 prefixEnd_3860458 := by exact prefixLift 3860458
  have htrace : WordTrace (prefixWord ++ tailWord_3860458) baseStart_3860458 baseEnd_3860458 := by
    simpa [prefixWord, tailWord_3860458, baseEnd_3860458] using wordTrace_append hprefix tailTrace_3860458
  have hstable : (prefixWord ++ tailWord_3860458).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3860458).length < 2 ^ (prefixWord ++ tailWord_3860458).sum := by decide
  have hdescent : baseEnd_3860458 < baseStart_3860458 := by decide
  rcases family_descends (prefixWord ++ tailWord_3860458) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3860464 : List Nat := [2, 1, 1, 1, 3, 2, 2, 1, 5, 1, 4]
def baseStart_3860464 : Nat := 118140960795 + 3860464 * 2 ^ 59
def prefixEnd_3860464 : Nat := 4983230072969 + 3 ^ 40 * 3860464 * 2
def baseEnd_3860464 : Nat := 1982273581378689150546055

theorem tailTrace_3860464 : CollatzResearch.WordTrace tailWord_3860464 prefixEnd_3860464 1982273581378689150546055 := by
  unfold tailWord_3860464
  simp only [CollatzResearch.WordTrace]
  refine ⟨70401344743102858802790223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93868459657470478403720297 70401344743102858802790223)
  ·
    refine ⟨105602017114654288204185335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70401344743102858802790223 105602017114654288204185335)
    ·
      refine ⟨158403025671981432306278003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105602017114654288204185335 158403025671981432306278003)
      ·
        refine ⟨237604538507972148459417005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 158403025671981432306278003 237604538507972148459417005)
        ·
          refine ⟨89101701940489555672281377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 237604538507972148459417005 89101701940489555672281377)
          ·
            refine ⟨66826276455367166754211033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 89101701940489555672281377 66826276455367166754211033)
            ·
              refine ⟨50119707341525375065658275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 66826276455367166754211033 50119707341525375065658275)
              ·
                refine ⟨75179561012288062598487413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50119707341525375065658275 75179561012288062598487413)
                ·
                  refine ⟨7048083844902005868608195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 75179561012288062598487413 7048083844902005868608195)
                  ·
                    refine ⟨10572125767353008802912293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7048083844902005868608195 10572125767353008802912293)
                    ·
                      refine ⟨1982273581378689150546055, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10572125767353008802912293 1982273581378689150546055)
                      ·
                        rfl

theorem cell23_3860464_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 2, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 2, 1, 5, 1, 4].length) (baseStart_3860464 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3860464 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3860464 prefixEnd_3860464 := by exact prefixLift 3860464
  have htrace : WordTrace (prefixWord ++ tailWord_3860464) baseStart_3860464 baseEnd_3860464 := by
    simpa [prefixWord, tailWord_3860464, baseEnd_3860464] using wordTrace_append hprefix tailTrace_3860464
  have hstable : (prefixWord ++ tailWord_3860464).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3860464).length < 2 ^ (prefixWord ++ tailWord_3860464).sum := by decide
  have hdescent : baseEnd_3860464 < baseStart_3860464 := by decide
  rcases family_descends (prefixWord ++ tailWord_3860464) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3860478 : List Nat := [4, 2, 2, 2, 1, 1, 1, 4, 1, 5]
def baseStart_3860478 : Nat := 118140960795 + 3860478 * 2 ^ 59
def prefixEnd_3860478 : Nat := 4983230072969 + 3 ^ 40 * 3860478 * 2
def baseEnd_3860478 : Nat := 660760256702617365256997

theorem tailTrace_3860478 : CollatzResearch.WordTrace tailWord_3860478 prefixEnd_3860478 660760256702617365256997 := by
  unfold tailWord_3860478
  simp only [CollatzResearch.WordTrace]
  refine ⟨17600400013519374749573761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 93868800072103331997726725 17600400013519374749573761)
  ·
    refine ⟨13200300010139531062180321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17600400013519374749573761 13200300010139531062180321)
    ·
      refine ⟨9900225007604648296635241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13200300010139531062180321 9900225007604648296635241)
      ·
        refine ⟨7425168755703486222476431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9900225007604648296635241 7425168755703486222476431)
        ·
          refine ⟨11137753133555229333714647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7425168755703486222476431 11137753133555229333714647)
          ·
            refine ⟨16706629700332844000571971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11137753133555229333714647 16706629700332844000571971)
            ·
              refine ⟨25059944550499266000857957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16706629700332844000571971 25059944550499266000857957)
              ·
                refine ⟨4698739603218612375160867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25059944550499266000857957 4698739603218612375160867)
                ·
                  refine ⟨7048109404827918562741301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4698739603218612375160867 7048109404827918562741301)
                  ·
                    refine ⟨660760256702617365256997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7048109404827918562741301 660760256702617365256997)
                    ·
                      rfl

theorem cell23_3860478_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 1, 1, 4, 1, 5].length) (baseStart_3860478 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3860478 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3860478 prefixEnd_3860478 := by exact prefixLift 3860478
  have htrace : WordTrace (prefixWord ++ tailWord_3860478) baseStart_3860478 baseEnd_3860478 := by
    simpa [prefixWord, tailWord_3860478, baseEnd_3860478] using wordTrace_append hprefix tailTrace_3860478
  have hstable : (prefixWord ++ tailWord_3860478).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3860478).length < 2 ^ (prefixWord ++ tailWord_3860478).sum := by decide
  have hdescent : baseEnd_3860478 < baseStart_3860478 := by decide
  rcases family_descends (prefixWord ++ tailWord_3860478) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3860481 : List Nat := [1, 2, 4, 1, 2, 1, 1, 1, 2, 6, 2]
def baseStart_3860481 : Nat := 118140960795 + 3860481 * 2 ^ 59
def prefixEnd_3860481 : Nat := 4983230072969 + 3 ^ 40 * 3860481 * 2
def baseEnd_3860481 : Nat := 1982282310549815584033477

theorem tailTrace_3860481 : CollatzResearch.WordTrace tailWord_3860481 prefixEnd_3860481 1982282310549815584033477 := by
  unfold tailWord_3860481
  simp only [CollatzResearch.WordTrace]
  refine ⟨140803309527144129508949297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93868873018096086339299531 140803309527144129508949297)
  ·
    refine ⟨105602482145358097131711973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 140803309527144129508949297 105602482145358097131711973)
    ·
      refine ⟨19800465402254643212195995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 105602482145358097131711973 19800465402254643212195995)
      ·
        refine ⟨29700698103381964818293993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19800465402254643212195995 29700698103381964818293993)
        ·
          refine ⟨22275523577536473613720495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29700698103381964818293993 22275523577536473613720495)
          ·
            refine ⟨33413285366304710420580743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22275523577536473613720495 33413285366304710420580743)
            ·
              refine ⟨50119928049457065630871115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33413285366304710420580743 50119928049457065630871115)
              ·
                refine ⟨75179892074185598446306673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50119928049457065630871115 75179892074185598446306673)
                ·
                  refine ⟨56384919055639198834730005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 75179892074185598446306673 56384919055639198834730005)
                  ·
                    refine ⟨2643043080733087445377969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 56384919055639198834730005 2643043080733087445377969)
                    ·
                      refine ⟨1982282310549815584033477, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2643043080733087445377969 1982282310549815584033477)
                      ·
                        rfl

theorem cell23_3860481_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 1, 1, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 1, 1, 2, 6, 2].length) (baseStart_3860481 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3860481 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3860481 prefixEnd_3860481 := by exact prefixLift 3860481
  have htrace : WordTrace (prefixWord ++ tailWord_3860481) baseStart_3860481 baseEnd_3860481 := by
    simpa [prefixWord, tailWord_3860481, baseEnd_3860481] using wordTrace_append hprefix tailTrace_3860481
  have hstable : (prefixWord ++ tailWord_3860481).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3860481).length < 2 ^ (prefixWord ++ tailWord_3860481).sum := by decide
  have hdescent : baseEnd_3860481 < baseStart_3860481 := by decide
  rcases family_descends (prefixWord ++ tailWord_3860481) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3860532 : List Nat := [2, 5, 1, 2, 2, 2, 1, 2, 1, 1, 4]
def baseStart_3860532 : Nat := 118140960795 + 3860532 * 2 ^ 59
def prefixEnd_3860532 : Nat := 4983230072969 + 3 ^ 40 * 3860532 * 2
def baseEnd_3860532 : Nat := 1982308498063194884495743

theorem tailTrace_3860532 : CollatzResearch.WordTrace tailWord_3860532 prefixEnd_3860532 1982308498063194884495743 := by
  unfold tailWord_3860532
  simp only [CollatzResearch.WordTrace]
  refine ⟨70402584824979682609527925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93870113099972910146037233 70402584824979682609527925)
  ·
    refine ⟨6600242327341845244643243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 70402584824979682609527925 6600242327341845244643243)
    ·
      refine ⟨9900363491012767866964865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6600242327341845244643243 9900363491012767866964865)
      ·
        refine ⟨7425272618259575900223649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9900363491012767866964865 7425272618259575900223649)
        ·
          refine ⟨5568954463694681925167737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7425272618259575900223649 5568954463694681925167737)
          ·
            refine ⟨4176715847771011443875803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5568954463694681925167737 4176715847771011443875803)
            ·
              refine ⟨6265073771656517165813705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4176715847771011443875803 6265073771656517165813705)
              ·
                refine ⟨4698805328742387874360279, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6265073771656517165813705 4698805328742387874360279)
                ·
                  refine ⟨7048207993113581811540419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4698805328742387874360279 7048207993113581811540419)
                  ·
                    refine ⟨10572311989670372717310629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7048207993113581811540419 10572311989670372717310629)
                    ·
                      refine ⟨1982308498063194884495743, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10572311989670372717310629 1982308498063194884495743)
                      ·
                        rfl

theorem cell23_3860532_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 2, 2, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 2, 2, 1, 2, 1, 1, 4].length) (baseStart_3860532 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3860532 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3860532 prefixEnd_3860532 := by exact prefixLift 3860532
  have htrace : WordTrace (prefixWord ++ tailWord_3860532) baseStart_3860532 baseEnd_3860532 := by
    simpa [prefixWord, tailWord_3860532, baseEnd_3860532] using wordTrace_append hprefix tailTrace_3860532
  have hstable : (prefixWord ++ tailWord_3860532).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3860532).length < 2 ^ (prefixWord ++ tailWord_3860532).sum := by decide
  have hdescent : baseEnd_3860532 < baseStart_3860532 := by decide
  rcases family_descends (prefixWord ++ tailWord_3860532) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3860565 : List Nat := [1, 3, 2, 2, 1, 4, 2, 2, 2, 1, 3]
def baseStart_3860565 : Nat := 118140960795 + 3860565 * 2 ^ 59
def prefixEnd_3860565 : Nat := 4983230072969 + 3 ^ 40 * 3860565 * 2
def baseEnd_3860565 : Nat := 1982325442924793255383091

theorem tailTrace_3860565 : CollatzResearch.WordTrace tailWord_3860565 prefixEnd_3860565 1982325442924793255383091 := by
  unfold tailWord_3860565
  simp only [CollatzResearch.WordTrace]
  refine ⟨140806373258839811855007149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93870915505893207903338099 140806373258839811855007149)
  ·
    refine ⟨52802389972064929445627681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 140806373258839811855007149 52802389972064929445627681)
    ·
      refine ⟨39601792479048697084220761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52802389972064929445627681 39601792479048697084220761)
      ·
        refine ⟨29701344359286522813165571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39601792479048697084220761 29701344359286522813165571)
        ·
          refine ⟨44552016538929784219748357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29701344359286522813165571 44552016538929784219748357)
          ·
            refine ⟨8353503101049334541202817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 44552016538929784219748357 8353503101049334541202817)
            ·
              refine ⟨6265127325787000905902113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8353503101049334541202817 6265127325787000905902113)
              ·
                refine ⟨4698845494340250679426585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6265127325787000905902113 4698845494340250679426585)
                ·
                  refine ⟨3524134120755188009569939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4698845494340250679426585 3524134120755188009569939)
                  ·
                    refine ⟨5286201181132782014354909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3524134120755188009569939 5286201181132782014354909)
                    ·
                      refine ⟨1982325442924793255383091, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5286201181132782014354909 1982325442924793255383091)
                      ·
                        rfl

theorem cell23_3860565_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 4, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 4, 2, 2, 2, 1, 3].length) (baseStart_3860565 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3860565 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3860565 prefixEnd_3860565 := by exact prefixLift 3860565
  have htrace : WordTrace (prefixWord ++ tailWord_3860565) baseStart_3860565 baseEnd_3860565 := by
    simpa [prefixWord, tailWord_3860565, baseEnd_3860565] using wordTrace_append hprefix tailTrace_3860565
  have hstable : (prefixWord ++ tailWord_3860565).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3860565).length < 2 ^ (prefixWord ++ tailWord_3860565).sum := by decide
  have hdescent : baseEnd_3860565 < baseStart_3860565 := by decide
  rcases family_descends (prefixWord ++ tailWord_3860565) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3860566 : List Nat := [5, 2, 2, 1, 1, 2, 1, 4, 1, 2, 2]
def baseStart_3860566 : Nat := 118140960795 + 3860566 * 2 ^ 59
def prefixEnd_3860566 : Nat := 4983230072969 + 3 ^ 40 * 3860566 * 2
def baseEnd_3860566 : Nat := 1982325956405447751470587

theorem tailTrace_3860566 : CollatzResearch.WordTrace tailWord_3860566 prefixEnd_3860566 1982325956405447751470587 := by
  unfold tailWord_3860566
  simp only [CollatzResearch.WordTrace]
  refine ⟨8800400608239761814112097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 93870939821224126017195701 8800400608239761814112097)
  ·
    refine ⟨6600300456179821360584073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8800400608239761814112097 6600300456179821360584073)
    ·
      refine ⟨4950225342134866020438055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6600300456179821360584073 4950225342134866020438055)
      ·
        refine ⟨7425338013202299030657083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4950225342134866020438055 7425338013202299030657083)
        ·
          refine ⟨11138007019803448545985625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7425338013202299030657083 11138007019803448545985625)
          ·
            refine ⟨8353505264852586409489219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11138007019803448545985625 8353505264852586409489219)
            ·
              refine ⟨12530257897278879614233829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8353505264852586409489219 12530257897278879614233829)
              ·
                refine ⟨2349423355739789927668843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12530257897278879614233829 2349423355739789927668843)
                ·
                  refine ⟨3524135033609684891503265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2349423355739789927668843 3524135033609684891503265)
                  ·
                    refine ⟨2643101275207263668627449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3524135033609684891503265 2643101275207263668627449)
                    ·
                      refine ⟨1982325956405447751470587, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2643101275207263668627449 1982325956405447751470587)
                      ·
                        rfl

theorem cell23_3860566_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 2, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 2, 1, 4, 1, 2, 2].length) (baseStart_3860566 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3860566 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3860566 prefixEnd_3860566 := by exact prefixLift 3860566
  have htrace : WordTrace (prefixWord ++ tailWord_3860566) baseStart_3860566 baseEnd_3860566 := by
    simpa [prefixWord, tailWord_3860566, baseEnd_3860566] using wordTrace_append hprefix tailTrace_3860566
  have hstable : (prefixWord ++ tailWord_3860566).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3860566).length < 2 ^ (prefixWord ++ tailWord_3860566).sum := by decide
  have hdescent : baseEnd_3860566 < baseStart_3860566 := by decide
  rcases family_descends (prefixWord ++ tailWord_3860566) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3860581 : List Nat := [1, 3, 1, 3, 2, 3, 1, 1, 2, 6]
def baseStart_3860581 : Nat := 118140960795 + 3860581 * 2 ^ 59
def prefixEnd_3860581 : Nat := 4983230072969 + 3 ^ 40 * 3860581 * 2
def baseEnd_3860581 : Nat := 660777886205088397594339

theorem tailTrace_3860581 : CollatzResearch.WordTrace tailWord_3860581 prefixEnd_3860581 660777886205088397594339 := by
  unfold tailWord_3860581
  simp only [CollatzResearch.WordTrace]
  refine ⟨140806956826781846587589597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93871304551187897725059731 140806956826781846587589597)
  ·
    refine ⟨52802608810043192470346099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 140806956826781846587589597 52802608810043192470346099)
    ·
      refine ⟨79203913215064788705519149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52802608810043192470346099 79203913215064788705519149)
      ·
        refine ⟨29701467455649295764569681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 79203913215064788705519149 29701467455649295764569681)
        ·
          refine ⟨22276100591736971823427261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29701467455649295764569681 22276100591736971823427261)
          ·
            refine ⟨8353537721901364433785223, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22276100591736971823427261 8353537721901364433785223)
            ·
              refine ⟨12530306582852046650677835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8353537721901364433785223 12530306582852046650677835)
              ·
                refine ⟨18795459874278069976016753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12530306582852046650677835 18795459874278069976016753)
                ·
                  refine ⟨14096594905708552482012565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18795459874278069976016753 14096594905708552482012565)
                  ·
                    refine ⟨660777886205088397594339, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 14096594905708552482012565 660777886205088397594339)
                    ·
                      rfl

theorem cell23_3860581_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 3, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 3, 1, 1, 2, 6].length) (baseStart_3860581 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3860581 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3860581 prefixEnd_3860581 := by exact prefixLift 3860581
  have htrace : WordTrace (prefixWord ++ tailWord_3860581) baseStart_3860581 baseEnd_3860581 := by
    simpa [prefixWord, tailWord_3860581, baseEnd_3860581] using wordTrace_append hprefix tailTrace_3860581
  have hstable : (prefixWord ++ tailWord_3860581).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3860581).length < 2 ^ (prefixWord ++ tailWord_3860581).sum := by decide
  have hdescent : baseEnd_3860581 < baseStart_3860581 := by decide
  rcases family_descends (prefixWord ++ tailWord_3860581) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3860588 : List Nat := [2, 2, 1, 1, 3, 3, 1, 3, 1, 4, 2]
def baseStart_3860588 : Nat := 118140960795 + 3860588 * 2 ^ 59
def prefixEnd_3860588 : Nat := 4983230072969 + 3 ^ 40 * 3860588 * 2
def baseEnd_3860588 : Nat := 1982337252979846665395485

theorem tailTrace_3860588 : CollatzResearch.WordTrace tailWord_3860588 prefixEnd_3860588 1982337252979846665395485 := by
  unfold tailWord_3860588
  simp only [CollatzResearch.WordTrace]
  refine ⟨70403606068878243391547209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93871474758504324522062945 70403606068878243391547209)
  ·
    refine ⟨52802704551658682543660407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70403606068878243391547209 52802704551658682543660407)
    ·
      refine ⟨79204056827488023815490611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52802704551658682543660407 79204056827488023815490611)
      ·
        refine ⟨118806085241232035723235917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79204056827488023815490611 118806085241232035723235917)
        ·
          refine ⟨44552281965462013396213469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 118806085241232035723235917 44552281965462013396213469)
          ·
            refine ⟨16707105737048255023580051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 44552281965462013396213469 16707105737048255023580051)
            ·
              refine ⟨25060658605572382535370077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16707105737048255023580051 25060658605572382535370077)
              ·
                refine ⟨9397746977089643450763779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25060658605572382535370077 9397746977089643450763779)
                ·
                  refine ⟨14096620465634465176145669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9397746977089643450763779 14096620465634465176145669)
                  ·
                    refine ⟨2643116337306462220527313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 14096620465634465176145669 2643116337306462220527313)
                    ·
                      refine ⟨1982337252979846665395485, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2643116337306462220527313 1982337252979846665395485)
                      ·
                        rfl

theorem cell23_3860588_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 4, 2].length) (baseStart_3860588 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3860588 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3860588 prefixEnd_3860588 := by exact prefixLift 3860588
  have htrace : WordTrace (prefixWord ++ tailWord_3860588) baseStart_3860588 baseEnd_3860588 := by
    simpa [prefixWord, tailWord_3860588, baseEnd_3860588] using wordTrace_append hprefix tailTrace_3860588
  have hstable : (prefixWord ++ tailWord_3860588).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3860588).length < 2 ^ (prefixWord ++ tailWord_3860588).sum := by decide
  have hdescent : baseEnd_3860588 < baseStart_3860588 := by decide
  rcases family_descends (prefixWord ++ tailWord_3860588) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3860609 : List Nat := [1, 2, 4, 2, 3, 2, 2, 1, 1, 3, 2]
def baseStart_3860609 : Nat := 118140960795 + 3860609 * 2 ^ 59
def prefixEnd_3860609 : Nat := 4983230072969 + 3 ^ 40 * 3860609 * 2
def baseEnd_3860609 : Nat := 1982348036073591083232889

theorem tailTrace_3860609 : CollatzResearch.WordTrace tailWord_3860609 prefixEnd_3860609 1982348036073591083232889 := by
  unfold tailWord_3860609
  simp only [CollatzResearch.WordTrace]
  refine ⟨140807978070680407369608881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93871985380453604913072587 140807978070680407369608881)
  ·
    refine ⟨105605983553010305527206661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 140807978070680407369608881 105605983553010305527206661)
    ·
      refine ⟨19801121916189432286351249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 105605983553010305527206661 19801121916189432286351249)
      ·
        refine ⟨14850841437142074214763437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19801121916189432286351249 14850841437142074214763437)
        ·
          refine ⟨5569065538928277830536289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14850841437142074214763437 5569065538928277830536289)
          ·
            refine ⟨4176799154196208372902217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5569065538928277830536289 4176799154196208372902217)
            ·
              refine ⟨3132599365647156279676663, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4176799154196208372902217 3132599365647156279676663)
              ·
                refine ⟨4698899048470734419514995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3132599365647156279676663 4698899048470734419514995)
                ·
                  refine ⟨7048348572706101629272493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4698899048470734419514995 7048348572706101629272493)
                  ·
                    refine ⟨2643130714764788110977185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7048348572706101629272493 2643130714764788110977185)
                    ·
                      refine ⟨1982348036073591083232889, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2643130714764788110977185 1982348036073591083232889)
                      ·
                        rfl

theorem cell23_3860609_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 3, 2, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 3, 2, 2, 1, 1, 3, 2].length) (baseStart_3860609 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3860609 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3860609 prefixEnd_3860609 := by exact prefixLift 3860609
  have htrace : WordTrace (prefixWord ++ tailWord_3860609) baseStart_3860609 baseEnd_3860609 := by
    simpa [prefixWord, tailWord_3860609, baseEnd_3860609] using wordTrace_append hprefix tailTrace_3860609
  have hstable : (prefixWord ++ tailWord_3860609).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3860609).length < 2 ^ (prefixWord ++ tailWord_3860609).sum := by decide
  have hdescent : baseEnd_3860609 < baseStart_3860609 := by decide
  rcases family_descends (prefixWord ++ tailWord_3860609) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3860622 : List Nat := [4, 1, 1, 3, 3, 1, 1, 1, 4, 2, 2]
def baseStart_3860622 : Nat := 118140960795 + 3860622 * 2 ^ 59
def prefixEnd_3860622 : Nat := 4983230072969 + 3 ^ 40 * 3860622 * 2
def baseEnd_3860622 : Nat := 1982354711322099532370329

theorem tailTrace_3860622 : CollatzResearch.WordTrace tailWord_3860622 prefixEnd_3860622 1982354711322099532370329 := by
  unfold tailWord_3860622
  simp only [CollatzResearch.WordTrace]
  refine ⟨17601056527454163823729015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 93872301479755540393221413 17601056527454163823729015)
  ·
    refine ⟨26401584791181245735593523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17601056527454163823729015 26401584791181245735593523)
    ·
      refine ⟨39602377186771868603390285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26401584791181245735593523 39602377186771868603390285)
      ·
        refine ⟨14850891445039450726271357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 39602377186771868603390285 14850891445039450726271357)
        ·
          refine ⟨5569084291889794022351759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14850891445039450726271357 5569084291889794022351759)
          ·
            refine ⟨8353626437834691033527639, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5569084291889794022351759 8353626437834691033527639)
            ·
              refine ⟨12530439656752036550291459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8353626437834691033527639 12530439656752036550291459)
              ·
                refine ⟨18795659485128054825437189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12530439656752036550291459 18795659485128054825437189)
                ·
                  refine ⟨3524186153461510279769473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 18795659485128054825437189 3524186153461510279769473)
                  ·
                    refine ⟨2643139615096132709827105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3524186153461510279769473 2643139615096132709827105)
                    ·
                      refine ⟨1982354711322099532370329, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2643139615096132709827105 1982354711322099532370329)
                      ·
                        rfl

theorem cell23_3860622_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 3, 1, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 3, 1, 1, 1, 4, 2, 2].length) (baseStart_3860622 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3860622 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3860622 prefixEnd_3860622 := by exact prefixLift 3860622
  have htrace : WordTrace (prefixWord ++ tailWord_3860622) baseStart_3860622 baseEnd_3860622 := by
    simpa [prefixWord, tailWord_3860622, baseEnd_3860622] using wordTrace_append hprefix tailTrace_3860622
  have hstable : (prefixWord ++ tailWord_3860622).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3860622).length < 2 ^ (prefixWord ++ tailWord_3860622).sum := by decide
  have hdescent : baseEnd_3860622 < baseStart_3860622 := by decide
  rcases family_descends (prefixWord ++ tailWord_3860622) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3860639 : List Nat := [1, 1, 2, 6, 1, 2, 3, 1, 2, 2, 2]
def baseStart_3860639 : Nat := 118140960795 + 3860639 * 2 ^ 59
def prefixEnd_3860639 : Nat := 4983230072969 + 3 ^ 40 * 3860639 * 2
def baseEnd_3860639 : Nat := 1982363440493225965857751

theorem tailTrace_3860639 : CollatzResearch.WordTrace tailWord_3860639 prefixEnd_3860639 1982363440493225965857751 := by
  unfold tailWord_3860639
  simp only [CollatzResearch.WordTrace]
  refine ⟨140809072260571722493200971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93872714840381148328800647 140809072260571722493200971)
  ·
    refine ⟨211213608390857583739801457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140809072260571722493200971 211213608390857583739801457)
    ·
      refine ⟨158410206293143187804851093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 211213608390857583739801457 158410206293143187804851093)
      ·
        refine ⟨7425478419991086928352395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 158410206293143187804851093 7425478419991086928352395)
        ·
          refine ⟨11138217629986630392528593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7425478419991086928352395 11138217629986630392528593)
          ·
            refine ⟨8353663222489972794396445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11138217629986630392528593 8353663222489972794396445)
            ·
              refine ⟨3132623708433739797898667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8353663222489972794396445 3132623708433739797898667)
              ·
                refine ⟨4698935562650609696848001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3132623708433739797898667 4698935562650609696848001)
                ·
                  refine ⟨3524201671987957272636001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4698935562650609696848001 3524201671987957272636001)
                  ·
                    refine ⟨2643151253990967954477001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3524201671987957272636001 2643151253990967954477001)
                    ·
                      refine ⟨1982363440493225965857751, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2643151253990967954477001 1982363440493225965857751)
                      ·
                        rfl

theorem cell23_3860639_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 2, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 2, 3, 1, 2, 2, 2].length) (baseStart_3860639 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3860639 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3860639 prefixEnd_3860639 := by exact prefixLift 3860639
  have htrace : WordTrace (prefixWord ++ tailWord_3860639) baseStart_3860639 baseEnd_3860639 := by
    simpa [prefixWord, tailWord_3860639, baseEnd_3860639] using wordTrace_append hprefix tailTrace_3860639
  have hstable : (prefixWord ++ tailWord_3860639).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3860639).length < 2 ^ (prefixWord ++ tailWord_3860639).sum := by decide
  have hdescent : baseEnd_3860639 < baseStart_3860639 := by decide
  rcases family_descends (prefixWord ++ tailWord_3860639) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3860641 : List Nat := [1, 2, 3, 3, 1, 2, 1, 2, 1, 7]
def baseStart_3860641 : Nat := 118140960795 + 3860641 * 2 ^ 59
def prefixEnd_3860641 : Nat := 4983230072969 + 3 ^ 40 * 3860641 * 2
def baseEnd_3860641 : Nat := 660788155818178319344247

theorem tailTrace_3860641 : CollatzResearch.WordTrace tailWord_3860641 prefixEnd_3860641 660788155818178319344247 := by
  unfold tailWord_3860641
  simp only [CollatzResearch.WordTrace]
  refine ⟨140809145206564476834773777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93872763471042984556515851 140809145206564476834773777)
  ·
    refine ⟨105606858904923357626080333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 140809145206564476834773777 105606858904923357626080333)
    ·
      refine ⟨39602572089346259109780125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 105606858904923357626080333 39602572089346259109780125)
      ·
        refine ⟨14850964533504847166167547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 39602572089346259109780125 14850964533504847166167547)
        ·
          refine ⟨22276446800257270749251321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14850964533504847166167547 22276446800257270749251321)
          ·
            refine ⟨16707335100192953061938491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22276446800257270749251321 16707335100192953061938491)
            ·
              refine ⟨25061002650289429592907737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16707335100192953061938491 25061002650289429592907737)
              ·
                refine ⟨18795751987717072194680803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25061002650289429592907737 18795751987717072194680803)
                ·
                  refine ⟨28193627981575608292021205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18795751987717072194680803 28193627981575608292021205)
                  ·
                    refine ⟨660788155818178319344247, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 28193627981575608292021205 660788155818178319344247)
                    ·
                      rfl

theorem cell23_3860641_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 2, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 2, 1, 2, 1, 7].length) (baseStart_3860641 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3860641 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3860641 prefixEnd_3860641 := by exact prefixLift 3860641
  have htrace : WordTrace (prefixWord ++ tailWord_3860641) baseStart_3860641 baseEnd_3860641 := by
    simpa [prefixWord, tailWord_3860641, baseEnd_3860641] using wordTrace_append hprefix tailTrace_3860641
  have hstable : (prefixWord ++ tailWord_3860641).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3860641).length < 2 ^ (prefixWord ++ tailWord_3860641).sum := by decide
  have hdescent : baseEnd_3860641 < baseStart_3860641 := by decide
  rcases family_descends (prefixWord ++ tailWord_3860641) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3860681 : List Nat := [1, 2, 1, 1, 2, 1, 1, 4, 3, 4, 3]
def baseStart_3860681 : Nat := 118140960795 + 3860681 * 2 ^ 59
def prefixEnd_3860681 : Nat := 4983230072969 + 3 ^ 40 * 3860681 * 2
def baseEnd_3860681 : Nat := 1982385006680714801532557

theorem tailTrace_3860681 : CollatzResearch.WordTrace tailWord_3860681 prefixEnd_3860681 1982385006680714801532557 := by
  unfold tailWord_3860681
  simp only [CollatzResearch.WordTrace]
  refine ⟨140810604126419563666229897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93873736084279709110819931 140810604126419563666229897)
  ·
    refine ⟨105607953094814672749672423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 140810604126419563666229897 105607953094814672749672423)
    ·
      refine ⟨158411929642222009124508635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105607953094814672749672423 158411929642222009124508635)
      ·
        refine ⟨237617894463333013686762953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 158411929642222009124508635 237617894463333013686762953)
        ·
          refine ⟨178213420847499760265072215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 237617894463333013686762953 178213420847499760265072215)
          ·
            refine ⟨267320131271249640397608323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 178213420847499760265072215 267320131271249640397608323)
            ·
              refine ⟨400980196906874460596412485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 267320131271249640397608323 400980196906874460596412485)
              ·
                refine ⟨75183786920038961361827341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 400980196906874460596412485 75183786920038961361827341)
                ·
                  refine ⟨28193920095014610510685253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 75183786920038961361827341 28193920095014610510685253)
                  ·
                    refine ⟨5286360017815239470753485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 28193920095014610510685253 5286360017815239470753485)
                    ·
                      refine ⟨1982385006680714801532557, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5286360017815239470753485 1982385006680714801532557)
                      ·
                        rfl

theorem cell23_3860681_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 4, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 4, 3, 4, 3].length) (baseStart_3860681 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3860681 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3860681 prefixEnd_3860681 := by exact prefixLift 3860681
  have htrace : WordTrace (prefixWord ++ tailWord_3860681) baseStart_3860681 baseEnd_3860681 := by
    simpa [prefixWord, tailWord_3860681, baseEnd_3860681] using wordTrace_append hprefix tailTrace_3860681
  have hstable : (prefixWord ++ tailWord_3860681).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3860681).length < 2 ^ (prefixWord ++ tailWord_3860681).sum := by decide
  have hdescent : baseEnd_3860681 < baseStart_3860681 := by decide
  rcases family_descends (prefixWord ++ tailWord_3860681) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
