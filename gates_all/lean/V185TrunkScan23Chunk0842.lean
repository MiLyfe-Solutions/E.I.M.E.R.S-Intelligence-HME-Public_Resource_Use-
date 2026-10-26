import V185TrunkScan23Chunk0841

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_4982885 : List Nat := [1, 3, 1, 3, 2, 3, 2, 1, 1, 2, 4]
def baseStart_4982885 : Nat := 118140960795 + 4982885 * 2 ^ 59
def prefixEnd_4982885 : Nat := 4983230072969 + 3 ^ 40 * 4982885 * 2
def baseEnd_4982885 : Nat := 2558615051078842173221635

theorem tailTrace_4982885 : CollatzResearch.WordTrace tailWord_4982885 prefixEnd_4982885 2558615051078842173221635 := by
  unfold tailWord_4982885
  simp only [CollatzResearch.WordTrace]
  refine ⟨181740746552866128850822109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121160497701910752567214739 181740746552866128850822109)
  ·
    refine ⟨68152779957324798319058291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 181740746552866128850822109 68152779957324798319058291)
    ·
      refine ⟨102229169935987197478587437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68152779957324798319058291 102229169935987197478587437)
      ·
        refine ⟨38335938725995199054470289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 102229169935987197478587437 38335938725995199054470289)
        ·
          refine ⟨28751954044496399290852717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38335938725995199054470289 28751954044496399290852717)
          ·
            refine ⟨10781982766686149734069769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 28751954044496399290852717 10781982766686149734069769)
            ·
              refine ⟨8086487075014612300552327, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10781982766686149734069769 8086487075014612300552327)
              ·
                refine ⟨12129730612521918450828491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8086487075014612300552327 12129730612521918450828491)
                ·
                  refine ⟨18194595918782877676242737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12129730612521918450828491 18194595918782877676242737)
                  ·
                    refine ⟨13645946939087158257182053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 18194595918782877676242737 13645946939087158257182053)
                    ·
                      refine ⟨2558615051078842173221635, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13645946939087158257182053 2558615051078842173221635)
                      ·
                        rfl

theorem cell23_4982885_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 3, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 3, 2, 1, 1, 2, 4].length) (baseStart_4982885 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4982885 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4982885 prefixEnd_4982885 := by exact prefixLift 4982885
  have htrace : WordTrace (prefixWord ++ tailWord_4982885) baseStart_4982885 baseEnd_4982885 := by
    simpa [prefixWord, tailWord_4982885, baseEnd_4982885] using wordTrace_append hprefix tailTrace_4982885
  have hstable : (prefixWord ++ tailWord_4982885).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4982885).length < 2 ^ (prefixWord ++ tailWord_4982885).sum := by decide
  have hdescent : baseEnd_4982885 < baseStart_4982885 := by decide
  rcases family_descends (prefixWord ++ tailWord_4982885) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4982905 : List Nat := [1, 2, 1, 3, 4, 1, 2, 2, 1, 3, 3]
def baseStart_4982905 : Nat := 118140960795 + 4982905 * 2 ^ 59
def prefixEnd_4982905 : Nat := 4983230072969 + 3 ^ 40 * 4982905 * 2
def baseEnd_4982905 : Nat := 2558625320691932094971543

theorem tailTrace_4982905 : CollatzResearch.WordTrace tailWord_4982905 prefixEnd_4982905 2558625320691932094971543 := by
  unfold tailWord_4982905
  simp only [CollatzResearch.WordTrace]
  refine ⟨181741476012793672266550169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121160984008529114844366779 181741476012793672266550169)
  ·
    refine ⟨136306107009595254199912627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 181741476012793672266550169 136306107009595254199912627)
    ·
      refine ⟨204459160514392881299868941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 136306107009595254199912627 204459160514392881299868941)
      ·
        refine ⟨76672185192897330487450853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 204459160514392881299868941 76672185192897330487450853)
        ·
          refine ⟨14376034723668249466397035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 76672185192897330487450853 14376034723668249466397035)
          ·
            refine ⟨21564052085502374199595553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14376034723668249466397035 21564052085502374199595553)
            ·
              refine ⟨16173039064126780649696665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21564052085502374199595553 16173039064126780649696665)
              ·
                refine ⟨12129779298095085487272499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16173039064126780649696665 12129779298095085487272499)
                ·
                  refine ⟨18194668947142628230908749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12129779298095085487272499 18194668947142628230908749)
                  ·
                    refine ⟨6823000855178485586590781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 18194668947142628230908749 6823000855178485586590781)
                    ·
                      refine ⟨2558625320691932094971543, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6823000855178485586590781 2558625320691932094971543)
                      ·
                        rfl

theorem cell23_4982905_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 1, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 1, 2, 2, 1, 3, 3].length) (baseStart_4982905 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4982905 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4982905 prefixEnd_4982905 := by exact prefixLift 4982905
  have htrace : WordTrace (prefixWord ++ tailWord_4982905) baseStart_4982905 baseEnd_4982905 := by
    simpa [prefixWord, tailWord_4982905, baseEnd_4982905] using wordTrace_append hprefix tailTrace_4982905
  have hstable : (prefixWord ++ tailWord_4982905).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4982905).length < 2 ^ (prefixWord ++ tailWord_4982905).sum := by decide
  have hdescent : baseEnd_4982905 < baseStart_4982905 := by decide
  rcases family_descends (prefixWord ++ tailWord_4982905) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4982909 : List Nat := [1, 4, 1, 1, 3, 4, 2, 1, 1, 2, 3]
def baseStart_4982909 : Nat := 118140960795 + 4982909 * 2 ^ 59
def prefixEnd_4982909 : Nat := 4983230072969 + 3 ^ 40 * 4982909 * 2
def baseEnd_4982909 : Nat := 2558627374614550079321525

theorem tailTrace_4982909 : CollatzResearch.WordTrace tailWord_4982909 prefixEnd_4982909 2558627374614550079321525 := by
  unfold tailWord_4982909
  simp only [CollatzResearch.WordTrace]
  refine ⟨181741621904779180949695781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121161081269852787299797187 181741621904779180949695781)
  ·
    refine ⟨34076554107146096428067959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 181741621904779180949695781 34076554107146096428067959)
    ·
      refine ⟨51114831160719144642101939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34076554107146096428067959 51114831160719144642101939)
      ·
        refine ⟨76672246741078716963152909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51114831160719144642101939 76672246741078716963152909)
        ·
          refine ⟨28752092527904518861182341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 76672246741078716963152909 28752092527904518861182341)
          ·
            refine ⟨5391017348982097286471689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 28752092527904518861182341 5391017348982097286471689)
            ·
              refine ⟨4043263011736572964853767, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5391017348982097286471689 4043263011736572964853767)
              ·
                refine ⟨6064894517604859447280651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4043263011736572964853767 6064894517604859447280651)
                ·
                  refine ⟨9097341776407289170920977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6064894517604859447280651 9097341776407289170920977)
                  ·
                    refine ⟨6823006332305466878190733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9097341776407289170920977 6823006332305466878190733)
                    ·
                      refine ⟨2558627374614550079321525, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6823006332305466878190733 2558627374614550079321525)
                      ·
                        rfl

theorem cell23_4982909_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 4, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 4, 2, 1, 1, 2, 3].length) (baseStart_4982909 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4982909 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4982909 prefixEnd_4982909 := by exact prefixLift 4982909
  have htrace : WordTrace (prefixWord ++ tailWord_4982909) baseStart_4982909 baseEnd_4982909 := by
    simpa [prefixWord, tailWord_4982909, baseEnd_4982909] using wordTrace_append hprefix tailTrace_4982909
  have hstable : (prefixWord ++ tailWord_4982909).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4982909).length < 2 ^ (prefixWord ++ tailWord_4982909).sum := by decide
  have hdescent : baseEnd_4982909 < baseStart_4982909 := by decide
  rcases family_descends (prefixWord ++ tailWord_4982909) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4982922 : List Nat := [3, 1, 2, 3, 1, 3, 1, 1, 4, 1, 3]
def baseStart_4982922 : Nat := 118140960795 + 4982922 * 2 ^ 59
def prefixEnd_4982922 : Nat := 4983230072969 + 3 ^ 40 * 4982922 * 2
def baseEnd_4982922 : Nat := 2558634049863058528458965

theorem tailTrace_4982922 : CollatzResearch.WordTrace tailWord_4982922 prefixEnd_4982922 2558634049863058528458965 := by
  unfold tailWord_4982922
  simp only [CollatzResearch.WordTrace]
  refine ⟨45435524013433021042479755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 121161397369154722779946013 45435524013433021042479755)
  ·
    refine ⟨68153286020149531563719633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45435524013433021042479755 68153286020149531563719633)
    ·
      refine ⟨51114964515112148672789725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 68153286020149531563719633 51114964515112148672789725)
      ·
        refine ⟨19168111693167055752296147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 51114964515112148672789725 19168111693167055752296147)
        ·
          refine ⟨28752167539750583628444221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19168111693167055752296147 28752167539750583628444221)
          ·
            refine ⟨10782062827406468860666583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 28752167539750583628444221 10782062827406468860666583)
            ·
              refine ⟨16173094241109703290999875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10782062827406468860666583 16173094241109703290999875)
              ·
                refine ⟨24259641361664554936499813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16173094241109703290999875 24259641361664554936499813)
                ·
                  refine ⟨4548682755312104050593715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 24259641361664554936499813 4548682755312104050593715)
                  ·
                    refine ⟨6823024132968156075890573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4548682755312104050593715 6823024132968156075890573)
                    ·
                      refine ⟨2558634049863058528458965, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6823024132968156075890573 2558634049863058528458965)
                      ·
                        rfl

theorem cell23_4982922_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 3, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 3, 1, 1, 4, 1, 3].length) (baseStart_4982922 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4982922 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4982922 prefixEnd_4982922 := by exact prefixLift 4982922
  have htrace : WordTrace (prefixWord ++ tailWord_4982922) baseStart_4982922 baseEnd_4982922 := by
    simpa [prefixWord, tailWord_4982922, baseEnd_4982922] using wordTrace_append hprefix tailTrace_4982922
  have hstable : (prefixWord ++ tailWord_4982922).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4982922).length < 2 ^ (prefixWord ++ tailWord_4982922).sum := by decide
  have hdescent : baseEnd_4982922 < baseStart_4982922 := by decide
  rcases family_descends (prefixWord ++ tailWord_4982922) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4982962 : List Nat := [3, 2, 1, 1, 1, 3, 1, 1, 6, 2, 2]
def baseStart_4982962 : Nat := 118140960795 + 4982962 * 2 ^ 59
def prefixEnd_4982962 : Nat := 4983230072969 + 3 ^ 40 * 4982962 * 2
def baseEnd_4982962 : Nat := 2558654589089238371958781

theorem tailTrace_4982962 : CollatzResearch.WordTrace tailWord_4982962 prefixEnd_4982962 2558654589089238371958781 := by
  unfold tailWord_4982962
  simp only [CollatzResearch.WordTrace]
  refine ⟨45435888743396792750343785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 121162369982391447334250093 45435888743396792750343785)
  ·
    refine ⟨34076916557547594562757839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45435888743396792750343785 34076916557547594562757839)
    ·
      refine ⟨51115374836321391844136759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34076916557547594562757839 51115374836321391844136759)
      ·
        refine ⟨76673062254482087766205139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51115374836321391844136759 76673062254482087766205139)
        ·
          refine ⟨115009593381723131649307709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 76673062254482087766205139 115009593381723131649307709)
          ·
            refine ⟨43128597518146174368490391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 115009593381723131649307709 43128597518146174368490391)
            ·
              refine ⟨64692896277219261552735587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 43128597518146174368490391 64692896277219261552735587)
              ·
                refine ⟨97039344415828892329103381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 64692896277219261552735587 97039344415828892329103381)
                ·
                  refine ⟨4548719269491979327926721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 97039344415828892329103381 4548719269491979327926721)
                  ·
                    refine ⟨3411539452118984495945041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4548719269491979327926721 3411539452118984495945041)
                    ·
                      refine ⟨2558654589089238371958781, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3411539452118984495945041 2558654589089238371958781)
                      ·
                        rfl

theorem cell23_4982962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 1, 1, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 1, 1, 6, 2, 2].length) (baseStart_4982962 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4982962 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4982962 prefixEnd_4982962 := by exact prefixLift 4982962
  have htrace : WordTrace (prefixWord ++ tailWord_4982962) baseStart_4982962 baseEnd_4982962 := by
    simpa [prefixWord, tailWord_4982962, baseEnd_4982962] using wordTrace_append hprefix tailTrace_4982962
  have hstable : (prefixWord ++ tailWord_4982962).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4982962).length < 2 ^ (prefixWord ++ tailWord_4982962).sum := by decide
  have hdescent : baseEnd_4982962 < baseStart_4982962 := by decide
  rcases family_descends (prefixWord ++ tailWord_4982962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4983008 : List Nat := [2, 1, 1, 3, 1, 3, 1, 2, 1, 1, 7]
def baseStart_4983008 : Nat := 118140960795 + 4983008 * 2 ^ 59
def prefixEnd_4983008 : Nat := 4983230072969 + 3 ^ 40 * 4983008 * 2
def baseEnd_4983008 : Nat := 2558678209199345191983569

theorem tailTrace_4983008 : CollatzResearch.WordTrace tailWord_4983008 prefixEnd_4983008 2558678209199345191983569 := by
  unfold tailWord_4983008
  simp only [CollatzResearch.WordTrace]
  refine ⟨90872616365710260428774839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 121163488487613680571699785 90872616365710260428774839)
  ·
    refine ⟨136308924548565390643162259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90872616365710260428774839 136308924548565390643162259)
    ·
      refine ⟨204463386822848085964743389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 136308924548565390643162259 204463386822848085964743389)
      ·
        refine ⟨76673770058568032236778771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 204463386822848085964743389 76673770058568032236778771)
        ·
          refine ⟨115010655087852048355168157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 76673770058568032236778771 115010655087852048355168157)
          ·
            refine ⟨43128995657944518133188059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 115010655087852048355168157 43128995657944518133188059)
            ·
              refine ⟨64693493486916777199782089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 43128995657944518133188059 64693493486916777199782089)
              ·
                refine ⟨48520120115187582899836567, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 64693493486916777199782089 48520120115187582899836567)
                ·
                  refine ⟨72780180172781374349754851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 48520120115187582899836567 72780180172781374349754851)
                  ·
                    refine ⟨109170270259172061524632277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 72780180172781374349754851 109170270259172061524632277)
                    ·
                      refine ⟨2558678209199345191983569, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 109170270259172061524632277 2558678209199345191983569)
                      ·
                        rfl

theorem cell23_4983008_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 1, 2, 1, 1, 7].length) (baseStart_4983008 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4983008 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4983008 prefixEnd_4983008 := by exact prefixLift 4983008
  have htrace : WordTrace (prefixWord ++ tailWord_4983008) baseStart_4983008 baseEnd_4983008 := by
    simpa [prefixWord, tailWord_4983008, baseEnd_4983008] using wordTrace_append hprefix tailTrace_4983008
  have hstable : (prefixWord ++ tailWord_4983008).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4983008).length < 2 ^ (prefixWord ++ tailWord_4983008).sum := by decide
  have hdescent : baseEnd_4983008 < baseStart_4983008 := by decide
  rcases family_descends (prefixWord ++ tailWord_4983008) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4983035 : List Nat := [1, 1, 1, 1, 1, 3, 1, 1, 5, 6, 2]
def baseStart_4983035 : Nat := 118140960795 + 4983035 * 2 ^ 59
def prefixEnd_4983035 : Nat := 4983230072969 + 3 ^ 40 * 4983035 * 2
def baseEnd_4983035 : Nat := 2558692073177016586345945

theorem tailTrace_4983035 : CollatzResearch.WordTrace tailWord_4983035 prefixEnd_4983035 2558692073177016586345945 := by
  unfold tailWord_4983035
  simp only [CollatzResearch.WordTrace]
  refine ⟨181746217502322704468782559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121164145001548469645855039 181746217502322704468782559)
  ·
    refine ⟨272619326253484056703173839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 181746217502322704468782559 272619326253484056703173839)
    ·
      refine ⟨408928989380226085054760759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 272619326253484056703173839 408928989380226085054760759)
      ·
        refine ⟨613393484070339127582141139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 408928989380226085054760759 613393484070339127582141139)
        ·
          refine ⟨920090226105508691373211709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 613393484070339127582141139 920090226105508691373211709)
          ·
            refine ⟨345033834789565759264954391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 920090226105508691373211709 345033834789565759264954391)
            ·
              refine ⟨517550752184348638897431587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 345033834789565759264954391 517550752184348638897431587)
              ·
                refine ⟨776326128276522958346147381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 517550752184348638897431587 776326128276522958346147381)
                ·
                  refine ⟨72780574525924027344951317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 776326128276522958346147381 72780574525924027344951317)
                  ·
                    refine ⟨3411589430902688781794593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 72780574525924027344951317 3411589430902688781794593)
                    ·
                      refine ⟨2558692073177016586345945, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3411589430902688781794593 2558692073177016586345945)
                      ·
                        rfl

theorem cell23_4983035_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 1, 5, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 1, 5, 6, 2].length) (baseStart_4983035 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4983035 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4983035 prefixEnd_4983035 := by exact prefixLift 4983035
  have htrace : WordTrace (prefixWord ++ tailWord_4983035) baseStart_4983035 baseEnd_4983035 := by
    simpa [prefixWord, tailWord_4983035, baseEnd_4983035] using wordTrace_append hprefix tailTrace_4983035
  have hstable : (prefixWord ++ tailWord_4983035).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4983035).length < 2 ^ (prefixWord ++ tailWord_4983035).sum := by decide
  have hdescent : baseEnd_4983035 < baseStart_4983035 := by decide
  rcases family_descends (prefixWord ++ tailWord_4983035) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4983042 : List Nat := [3, 4, 1, 1, 2, 1, 2, 1, 1, 2, 5]
def baseStart_4983042 : Nat := 118140960795 + 4983042 * 2 ^ 59
def prefixEnd_4983042 : Nat := 4983230072969 + 3 ^ 40 * 4983042 * 2
def baseEnd_4983042 : Nat := 2558695667541598058958413

theorem tailTrace_4983042 : CollatzResearch.WordTrace tailWord_4983042 prefixEnd_4983042 2558695667541598058958413 := by
  unfold tailWord_4983042
  simp only [CollatzResearch.WordTrace]
  refine ⟨45436618203324336166071845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 121164315208864896442858253 45436618203324336166071845)
  ·
    refine ⟨8519365913123313031138471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 45436618203324336166071845 8519365913123313031138471)
    ·
      refine ⟨12779048869684969546707707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8519365913123313031138471 12779048869684969546707707)
      ·
        refine ⟨19168573304527454320061561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12779048869684969546707707 19168573304527454320061561)
        ·
          refine ⟨14376429978395590740046171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19168573304527454320061561 14376429978395590740046171)
          ·
            refine ⟨21564644967593386110069257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14376429978395590740046171 21564644967593386110069257)
            ·
              refine ⟨16173483725695039582551943, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21564644967593386110069257 16173483725695039582551943)
              ·
                refine ⟨24260225588542559373827915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16173483725695039582551943 24260225588542559373827915)
                ·
                  refine ⟨36390338382813839060741873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24260225588542559373827915 36390338382813839060741873)
                  ·
                    refine ⟨27292753787110379295556405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 36390338382813839060741873 27292753787110379295556405)
                    ·
                      refine ⟨2558695667541598058958413, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 27292753787110379295556405 2558695667541598058958413)
                      ·
                        rfl

theorem cell23_4983042_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 1, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 1, 2, 1, 1, 2, 5].length) (baseStart_4983042 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4983042 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4983042 prefixEnd_4983042 := by exact prefixLift 4983042
  have htrace : WordTrace (prefixWord ++ tailWord_4983042) baseStart_4983042 baseEnd_4983042 := by
    simpa [prefixWord, tailWord_4983042, baseEnd_4983042] using wordTrace_append hprefix tailTrace_4983042
  have hstable : (prefixWord ++ tailWord_4983042).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4983042).length < 2 ^ (prefixWord ++ tailWord_4983042).sum := by decide
  have hdescent : baseEnd_4983042 < baseStart_4983042 := by decide
  rcases family_descends (prefixWord ++ tailWord_4983042) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4983052 : List Nat := [2, 2, 1, 2, 2, 2, 3, 1, 2, 4, 2]
def baseStart_4983052 : Nat := 118140960795 + 4983052 * 2 ^ 59
def prefixEnd_4983052 : Nat := 4983230072969 + 3 ^ 40 * 4983052 * 2
def baseEnd_4983052 : Nat := 2558700802348143019833367

theorem tailTrace_4983052 : CollatzResearch.WordTrace tailWord_4983052 prefixEnd_4983052 2558700802348143019833367 := by
  unfold tailWord_4983052
  simp only [CollatzResearch.WordTrace]
  refine ⟨90873418771630558186075705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 121164558362174077581434273 90873418771630558186075705)
  ·
    refine ⟨68155064078722918639556779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 90873418771630558186075705 68155064078722918639556779)
    ·
      refine ⟨102232596118084377959335169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68155064078722918639556779 102232596118084377959335169)
      ·
        refine ⟨76674447088563283469501377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 102232596118084377959335169 76674447088563283469501377)
        ·
          refine ⟨57505835316422462602126033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 76674447088563283469501377 57505835316422462602126033)
          ·
            refine ⟨43129376487316846951594525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 57505835316422462602126033 43129376487316846951594525)
            ·
              refine ⟨16173516182743817606847947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 43129376487316846951594525 16173516182743817606847947)
              ·
                refine ⟨24260274274115726410271921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16173516182743817606847947 24260274274115726410271921)
                ·
                  refine ⟨18195205705586794807703941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 24260274274115726410271921 18195205705586794807703941)
                  ·
                    refine ⟨3411601069797524026444489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 18195205705586794807703941 3411601069797524026444489)
                    ·
                      refine ⟨2558700802348143019833367, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3411601069797524026444489 2558700802348143019833367)
                      ·
                        rfl

theorem cell23_4983052_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 3, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 3, 1, 2, 4, 2].length) (baseStart_4983052 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4983052 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4983052 prefixEnd_4983052 := by exact prefixLift 4983052
  have htrace : WordTrace (prefixWord ++ tailWord_4983052) baseStart_4983052 baseEnd_4983052 := by
    simpa [prefixWord, tailWord_4983052, baseEnd_4983052] using wordTrace_append hprefix tailTrace_4983052
  have hstable : (prefixWord ++ tailWord_4983052).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4983052).length < 2 ^ (prefixWord ++ tailWord_4983052).sum := by decide
  have hdescent : baseEnd_4983052 < baseStart_4983052 := by decide
  rcases family_descends (prefixWord ++ tailWord_4983052) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4983055 : List Nat := [1, 1, 2, 1, 1, 1, 3, 4, 4, 2, 3]
def baseStart_4983055 : Nat := 118140960795 + 4983055 * 2 ^ 59
def prefixEnd_4983055 : Nat := 4983230072969 + 3 ^ 40 * 4983055 * 2
def baseEnd_4983055 : Nat := 2558702342790106508095853

theorem tailTrace_4983055 : CollatzResearch.WordTrace tailWord_4983055 prefixEnd_4983055 2558702342790106508095853 := by
  unfold tailWord_4983055
  simp only [CollatzResearch.WordTrace]
  refine ⟨181746946962250247884510619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121164631308166831923007079 181746946962250247884510619)
  ·
    refine ⟨272620420443375371826765929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 181746946962250247884510619 272620420443375371826765929)
    ·
      refine ⟨204465315332531528870074447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 272620420443375371826765929 204465315332531528870074447)
      ·
        refine ⟨306697972998797293305111671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 204465315332531528870074447 306697972998797293305111671)
        ·
          refine ⟨460046959498195939957667507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 306697972998797293305111671 460046959498195939957667507)
          ·
            refine ⟨690070439247293909936501261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 460046959498195939957667507 690070439247293909936501261)
            ·
              refine ⟨258776414717735216226187973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 690070439247293909936501261 258776414717735216226187973)
              ·
                refine ⟨48520577759575353042410245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 258776414717735216226187973 48520577759575353042410245)
                ·
                  refine ⟨9097608329920378695451921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 48520577759575353042410245 9097608329920378695451921)
                  ·
                    refine ⟨6823206247440284021588941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9097608329920378695451921 6823206247440284021588941)
                    ·
                      refine ⟨2558702342790106508095853, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6823206247440284021588941 2558702342790106508095853)
                      ·
                        rfl

theorem cell23_4983055_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 3, 4, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 3, 4, 4, 2, 3].length) (baseStart_4983055 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4983055 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4983055 prefixEnd_4983055 := by exact prefixLift 4983055
  have htrace : WordTrace (prefixWord ++ tailWord_4983055) baseStart_4983055 baseEnd_4983055 := by
    simpa [prefixWord, tailWord_4983055, baseEnd_4983055] using wordTrace_append hprefix tailTrace_4983055
  have hstable : (prefixWord ++ tailWord_4983055).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4983055).length < 2 ^ (prefixWord ++ tailWord_4983055).sum := by decide
  have hdescent : baseEnd_4983055 < baseStart_4983055 := by decide
  rcases family_descends (prefixWord ++ tailWord_4983055) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4983072 : List Nat := [2, 1, 1, 5, 2, 2, 1, 1, 1, 4, 3]
def baseStart_4983072 : Nat := 118140960795 + 4983072 * 2 ^ 59
def prefixEnd_4983072 : Nat := 4983230072969 + 3 ^ 40 * 4983072 * 2
def baseEnd_4983072 : Nat := 2558711071961232941583275

theorem tailTrace_4983072 : CollatzResearch.WordTrace tailWord_4983072 prefixEnd_4983072 2558711071961232941583275 := by
  unfold tailWord_4983072
  simp only [CollatzResearch.WordTrace]
  refine ⟨90873783501594329893939735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 121165044668792439858586313 90873783501594329893939735)
  ·
    refine ⟨136310675252391494840909603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90873783501594329893939735 136310675252391494840909603)
    ·
      refine ⟨204466012878587242261364405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 136310675252391494840909603 204466012878587242261364405)
      ·
        refine ⟨19168688707367553962002913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 204466012878587242261364405 19168688707367553962002913)
        ·
          refine ⟨14376516530525665471502185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19168688707367553962002913 14376516530525665471502185)
          ·
            refine ⟨10782387397894249103626639, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14376516530525665471502185 10782387397894249103626639)
            ·
              refine ⟨16173581096841373655439959, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10782387397894249103626639 16173581096841373655439959)
              ·
                refine ⟨24260371645262060483159939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16173581096841373655439959 24260371645262060483159939)
                ·
                  refine ⟨36390557467893090724739909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24260371645262060483159939 36390557467893090724739909)
                  ·
                    refine ⟨6823229525229954510888733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 36390557467893090724739909 6823229525229954510888733)
                    ·
                      refine ⟨2558711071961232941583275, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6823229525229954510888733 2558711071961232941583275)
                      ·
                        rfl

theorem cell23_4983072_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 2, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 2, 1, 1, 1, 4, 3].length) (baseStart_4983072 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4983072 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4983072 prefixEnd_4983072 := by exact prefixLift 4983072
  have htrace : WordTrace (prefixWord ++ tailWord_4983072) baseStart_4983072 baseEnd_4983072 := by
    simpa [prefixWord, tailWord_4983072, baseEnd_4983072] using wordTrace_append hprefix tailTrace_4983072
  have hstable : (prefixWord ++ tailWord_4983072).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4983072).length < 2 ^ (prefixWord ++ tailWord_4983072).sum := by decide
  have hdescent : baseEnd_4983072 < baseStart_4983072 := by decide
  rcases family_descends (prefixWord ++ tailWord_4983072) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4983092 : List Nat := [2, 5, 1, 1, 1, 3, 1, 1, 8]
def baseStart_4983092 : Nat := 118140960795 + 4983092 * 2 ^ 59
def prefixEnd_4983092 : Nat := 4983230072969 + 3 ^ 40 * 4983092 * 2
def baseEnd_4983092 : Nat := 284302371286035873703687

theorem tailTrace_4983092 : CollatzResearch.WordTrace tailWord_4983092 prefixEnd_4983092 284302371286035873703687 := by
  unfold tailWord_4983092
  simp only [CollatzResearch.WordTrace]
  refine ⟨90874148231558101601803765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 121165530975410802135738353 90874148231558101601803765)
  ·
    refine ⟨8519451396708572025169103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 90874148231558101601803765 8519451396708572025169103)
    ·
      refine ⟨12779177095062858037753655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8519451396708572025169103 12779177095062858037753655)
      ·
        refine ⟨19168765642594287056630483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12779177095062858037753655 19168765642594287056630483)
        ·
          refine ⟨28753148463891430584945725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19168765642594287056630483 28753148463891430584945725)
          ·
            refine ⟨10782430673959286469354647, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 28753148463891430584945725 10782430673959286469354647)
            ·
              refine ⟨16173646010938929704031971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10782430673959286469354647 16173646010938929704031971)
              ·
                refine ⟨24260469016408394556047957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16173646010938929704031971 24260469016408394556047957)
                ·
                  refine ⟨284302371286035873703687, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 24260469016408394556047957 284302371286035873703687)
                  ·
                    rfl

theorem cell23_4983092_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 3, 1, 1, 8].length) (baseStart_4983092 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4983092 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4983092 prefixEnd_4983092 := by exact prefixLift 4983092
  have htrace : WordTrace (prefixWord ++ tailWord_4983092) baseStart_4983092 baseEnd_4983092 := by
    simpa [prefixWord, tailWord_4983092, baseEnd_4983092] using wordTrace_append hprefix tailTrace_4983092
  have hstable : (prefixWord ++ tailWord_4983092).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4983092).length < 2 ^ (prefixWord ++ tailWord_4983092).sum := by decide
  have hdescent : baseEnd_4983092 < baseStart_4983092 := by decide
  rcases family_descends (prefixWord ++ tailWord_4983092) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4983112 : List Nat := [2, 1, 3, 1, 1, 2, 3, 2, 1, 5, 2]
def baseStart_4983112 : Nat := 118140960795 + 4983112 * 2 ^ 59
def prefixEnd_4983112 : Nat := 4983230072969 + 3 ^ 40 * 4983112 * 2
def baseEnd_4983112 : Nat := 2558731611187412785083091

theorem tailTrace_4983112 : CollatzResearch.WordTrace tailWord_4983112 prefixEnd_4983112 2558731611187412785083091 := by
  unfold tailWord_4983112
  simp only [CollatzResearch.WordTrace]
  refine ⟨90874512961521873309667795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 121166017282029164412890393 90874512961521873309667795)
  ·
    refine ⟨136311769442282809964501693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90874512961521873309667795 136311769442282809964501693)
    ·
      refine ⟨51116913540856053736688135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 136311769442282809964501693 51116913540856053736688135)
      ·
        refine ⟨76675370311284080605032203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51116913540856053736688135 76675370311284080605032203)
        ·
          refine ⟨115013055466926120907548305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 76675370311284080605032203 115013055466926120907548305)
          ·
            refine ⟨86259791600194590680661229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 115013055466926120907548305 86259791600194590680661229)
            ·
              refine ⟨32347421850072971505247961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 86259791600194590680661229 32347421850072971505247961)
              ·
                refine ⟨24260566387554728628935971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 32347421850072971505247961 24260566387554728628935971)
                ·
                  refine ⟨36390849581332092943403957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24260566387554728628935971 36390849581332092943403957)
                  ·
                    refine ⟨3411642148249883713444121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 36390849581332092943403957 3411642148249883713444121)
                    ·
                      refine ⟨2558731611187412785083091, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3411642148249883713444121 2558731611187412785083091)
                      ·
                        rfl

theorem cell23_4983112_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 3, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 3, 2, 1, 5, 2].length) (baseStart_4983112 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4983112 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4983112 prefixEnd_4983112 := by exact prefixLift 4983112
  have htrace : WordTrace (prefixWord ++ tailWord_4983112) baseStart_4983112 baseEnd_4983112 := by
    simpa [prefixWord, tailWord_4983112, baseEnd_4983112] using wordTrace_append hprefix tailTrace_4983112
  have hstable : (prefixWord ++ tailWord_4983112).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4983112).length < 2 ^ (prefixWord ++ tailWord_4983112).sum := by decide
  have hdescent : baseEnd_4983112 < baseStart_4983112 := by decide
  rcases family_descends (prefixWord ++ tailWord_4983112) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4983122 : List Nat := [3, 2, 2, 1, 1, 1, 3, 4, 1, 5]
def baseStart_4983122 : Nat := 118140960795 + 4983122 * 2 ^ 59
def prefixEnd_4983122 : Nat := 4983230072969 + 3 ^ 40 * 4983122 * 2
def baseEnd_4983122 : Nat := 852912248664652581986015

theorem tailTrace_4983122 : CollatzResearch.WordTrace tailWord_4983122 prefixEnd_4983122 852912248664652581986015 := by
  unfold tailWord_4983122
  simp only [CollatzResearch.WordTrace]
  refine ⟨45437347663251879581799905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 121166260435338345551466413 45437347663251879581799905)
  ·
    refine ⟨34078010747438909686349929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45437347663251879581799905 34078010747438909686349929)
    ·
      refine ⟨25558508060579182264762447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34078010747438909686349929 25558508060579182264762447)
      ·
        refine ⟨38337762090868773397143671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25558508060579182264762447 38337762090868773397143671)
        ·
          refine ⟨57506643136303160095715507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38337762090868773397143671 57506643136303160095715507)
          ·
            refine ⟨86259964704454740143573261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 57506643136303160095715507 86259964704454740143573261)
            ·
              refine ⟨32347486764170527553839973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 86259964704454740143573261 32347486764170527553839973)
              ·
                refine ⟨6065153768281973916344995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 32347486764170527553839973 6065153768281973916344995)
                ·
                  refine ⟨9097730652422960874517493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6065153768281973916344995 9097730652422960874517493)
                  ·
                    refine ⟨852912248664652581986015, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9097730652422960874517493 852912248664652581986015)
                    ·
                      rfl

theorem cell23_4983122_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 3, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 3, 4, 1, 5].length) (baseStart_4983122 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4983122 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4983122 prefixEnd_4983122 := by exact prefixLift 4983122
  have htrace : WordTrace (prefixWord ++ tailWord_4983122) baseStart_4983122 baseEnd_4983122 := by
    simpa [prefixWord, tailWord_4983122, baseEnd_4983122] using wordTrace_append hprefix tailTrace_4983122
  have hstable : (prefixWord ++ tailWord_4983122).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4983122).length < 2 ^ (prefixWord ++ tailWord_4983122).sum := by decide
  have hdescent : baseEnd_4983122 < baseStart_4983122 := by decide
  rcases family_descends (prefixWord ++ tailWord_4983122) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4983135 : List Nat := [1, 1, 2, 3, 1, 2, 2, 4, 1, 6]
def baseStart_4983135 : Nat := 118140960795 + 4983135 * 2 ^ 59
def prefixEnd_4983135 : Nat := 4983230072969 + 3 ^ 40 * 4983135 * 2
def baseEnd_4983135 : Nat := 852914473747488731698495

theorem tailTrace_4983135 : CollatzResearch.WordTrace tailWord_4983135 prefixEnd_4983135 852914473747488731698495 := by
  unfold tailWord_4983135
  simp only [CollatzResearch.WordTrace]
  refine ⟨181749864801960421547422859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121166576534640281031615239 181749864801960421547422859)
  ·
    refine ⟨272624797202940632321134289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 181749864801960421547422859 272624797202940632321134289)
    ·
      refine ⟨204468597902205474240850717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 272624797202940632321134289 204468597902205474240850717)
      ·
        refine ⟨76675724213327052840319019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 204468597902205474240850717 76675724213327052840319019)
        ·
          refine ⟨115013586319990579260478529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 76675724213327052840319019 115013586319990579260478529)
          ·
            refine ⟨86260189739992934445358897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 115013586319990579260478529 86260189739992934445358897)
            ·
              refine ⟨64695142304994700834019173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 86260189739992934445358897 64695142304994700834019173)
              ·
                refine ⟨12130339182186506406378595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 64695142304994700834019173 12130339182186506406378595)
                ·
                  refine ⟨18195508773279759609567893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12130339182186506406378595 18195508773279759609567893)
                  ·
                    refine ⟨852914473747488731698495, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 18195508773279759609567893 852914473747488731698495)
                    ·
                      rfl

theorem cell23_4983135_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 2, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 2, 4, 1, 6].length) (baseStart_4983135 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4983135 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4983135 prefixEnd_4983135 := by exact prefixLift 4983135
  have htrace : WordTrace (prefixWord ++ tailWord_4983135) baseStart_4983135 baseEnd_4983135 := by
    simpa [prefixWord, tailWord_4983135, baseEnd_4983135] using wordTrace_append hprefix tailTrace_4983135
  have hstable : (prefixWord ++ tailWord_4983135).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4983135).length < 2 ^ (prefixWord ++ tailWord_4983135).sum := by decide
  have hdescent : baseEnd_4983135 < baseStart_4983135 := by decide
  rcases family_descends (prefixWord ++ tailWord_4983135) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4983146 : List Nat := [3, 1, 3, 3, 1, 2, 1, 2, 2, 3, 2]
def baseStart_4983146 : Nat := 118140960795 + 4983146 * 2 ^ 59
def prefixEnd_4983146 : Nat := 4983230072969 + 3 ^ 40 * 4983146 * 2
def baseEnd_4983146 : Nat := 2558749069529665652057935

theorem tailTrace_4983146 : CollatzResearch.WordTrace tailWord_4983146 prefixEnd_4983146 2558749069529665652057935 := by
  unfold tailWord_4983146
  simp only [CollatzResearch.WordTrace]
  refine ⟨45437566501230142606518323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 121166844003280380284048861 45437566501230142606518323)
  ·
    refine ⟨68156349751845213909777485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45437566501230142606518323 68156349751845213909777485)
    ·
      refine ⟨25558631156941955216166557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 68156349751845213909777485 25558631156941955216166557)
      ·
        refine ⟨9584486683853233206062459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 25558631156941955216166557 9584486683853233206062459)
        ·
          refine ⟨14376730025779849809093689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9584486683853233206062459 14376730025779849809093689)
          ·
            refine ⟨10782547519334887356820267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14376730025779849809093689 10782547519334887356820267)
            ·
              refine ⟨16173821279002331035230401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10782547519334887356820267 16173821279002331035230401)
              ·
                refine ⟨12130365959251748276422801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16173821279002331035230401 12130365959251748276422801)
                ·
                  refine ⟨9097774469438811207317101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12130365959251748276422801 9097774469438811207317101)
                  ·
                    refine ⟨3411665426039554202743913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9097774469438811207317101 3411665426039554202743913)
                    ·
                      refine ⟨2558749069529665652057935, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3411665426039554202743913 2558749069529665652057935)
                      ·
                        rfl

theorem cell23_4983146_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 2, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 2, 1, 2, 2, 3, 2].length) (baseStart_4983146 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4983146 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4983146 prefixEnd_4983146 := by exact prefixLift 4983146
  have htrace : WordTrace (prefixWord ++ tailWord_4983146) baseStart_4983146 baseEnd_4983146 := by
    simpa [prefixWord, tailWord_4983146, baseEnd_4983146] using wordTrace_append hprefix tailTrace_4983146
  have hstable : (prefixWord ++ tailWord_4983146).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4983146).length < 2 ^ (prefixWord ++ tailWord_4983146).sum := by decide
  have hdescent : baseEnd_4983146 < baseStart_4983146 := by decide
  rcases family_descends (prefixWord ++ tailWord_4983146) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4983152 : List Nat := [2, 1, 1, 1, 4, 3, 2, 1, 4, 4]
def baseStart_4983152 : Nat := 118140960795 + 4983152 * 2 ^ 59
def prefixEnd_4983152 : Nat := 4983230072969 + 3 ^ 40 * 4983152 * 2
def baseEnd_4983152 : Nat := 852917383471197542860969

theorem tailTrace_4983152 : CollatzResearch.WordTrace tailWord_4983152 prefixEnd_4983152 852917383471197542860969 := by
  unfold tailWord_4983152
  simp only [CollatzResearch.WordTrace]
  refine ⟨90875242421449416725395855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 121166989895265888967194473 90875242421449416725395855)
  ·
    refine ⟨136312863632174125088093783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90875242421449416725395855 136312863632174125088093783)
    ·
      refine ⟨204469295448261187632140675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 136312863632174125088093783 204469295448261187632140675)
      ·
        refine ⟨306703943172391781448211013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 204469295448261187632140675 306703943172391781448211013)
        ·
          refine ⟨57506989344823459021539565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 306703943172391781448211013 57506989344823459021539565)
          ·
            refine ⟨21565121004308797133077337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 57506989344823459021539565 21565121004308797133077337)
            ·
              refine ⟨16173840753231597849808003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21565121004308797133077337 16173840753231597849808003)
              ·
                refine ⟨24260761129847396774712005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16173840753231597849808003 24260761129847396774712005)
                ·
                  refine ⟨4548892711846386895258501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 24260761129847396774712005 4548892711846386895258501)
                  ·
                    refine ⟨852917383471197542860969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4548892711846386895258501 852917383471197542860969)
                    ·
                      rfl

theorem cell23_4983152_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 3, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 3, 2, 1, 4, 4].length) (baseStart_4983152 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4983152 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4983152 prefixEnd_4983152 := by exact prefixLift 4983152
  have htrace : WordTrace (prefixWord ++ tailWord_4983152) baseStart_4983152 baseEnd_4983152 := by
    simpa [prefixWord, tailWord_4983152, baseEnd_4983152] using wordTrace_append hprefix tailTrace_4983152
  have hstable : (prefixWord ++ tailWord_4983152).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4983152).length < 2 ^ (prefixWord ++ tailWord_4983152).sum := by decide
  have hdescent : baseEnd_4983152 < baseStart_4983152 := by decide
  rcases family_descends (prefixWord ++ tailWord_4983152) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4983155 : List Nat := [1, 1, 1, 2, 2, 1, 2, 4, 3, 2, 4]
def baseStart_4983155 : Nat := 118140960795 + 4983155 * 2 ^ 59
def prefixEnd_4983155 : Nat := 4983230072969 + 3 ^ 40 * 4983155 * 2
def baseEnd_4983155 : Nat := 2558753690855556116845393

theorem tailTrace_4983155 : CollatzResearch.WordTrace tailWord_4983155 prefixEnd_4983155 2558753690855556116845393 := by
  unfold tailWord_4983155
  simp only [CollatzResearch.WordTrace]
  refine ⟨181750594261887964963150919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121167062841258643308767279 181750594261887964963150919)
  ·
    refine ⟨272625891392831947444726379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 181750594261887964963150919 272625891392831947444726379)
    ·
      refine ⟨408938837089247921167089569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 272625891392831947444726379 408938837089247921167089569)
      ·
        refine ⟨306704127816935940875317177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 408938837089247921167089569 306704127816935940875317177)
        ·
          refine ⟨230028095862701955656487883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 306704127816935940875317177 230028095862701955656487883)
          ·
            refine ⟨345042143794052933484731825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 230028095862701955656487883 345042143794052933484731825)
            ·
              refine ⟨258781607845539700113548869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 345042143794052933484731825 258781607845539700113548869)
              ·
                refine ⟨48521551471038693771290413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 258781607845539700113548869 48521551471038693771290413)
                ·
                  refine ⟨18195581801639510164233905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 48521551471038693771290413 18195581801639510164233905)
                  ·
                    refine ⟨13646686351229632623175429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 18195581801639510164233905 13646686351229632623175429)
                    ·
                      refine ⟨2558753690855556116845393, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13646686351229632623175429 2558753690855556116845393)
                      ·
                        rfl

theorem cell23_4983155_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 2, 4, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 2, 4, 3, 2, 4].length) (baseStart_4983155 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4983155 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4983155 prefixEnd_4983155 := by exact prefixLift 4983155
  have htrace : WordTrace (prefixWord ++ tailWord_4983155) baseStart_4983155 baseEnd_4983155 := by
    simpa [prefixWord, tailWord_4983155, baseEnd_4983155] using wordTrace_append hprefix tailTrace_4983155
  have hstable : (prefixWord ++ tailWord_4983155).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4983155).length < 2 ^ (prefixWord ++ tailWord_4983155).sum := by decide
  have hdescent : baseEnd_4983155 < baseStart_4983155 := by decide
  rcases family_descends (prefixWord ++ tailWord_4983155) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4983159 : List Nat := [1, 1, 3, 1, 1, 2, 2, 5, 3, 2, 2]
def baseStart_4983159 : Nat := 118140960795 + 4983159 * 2 ^ 59
def prefixEnd_4983159 : Nat := 4983230072969 + 3 ^ 40 * 4983159 * 2
def baseEnd_4983159 : Nat := 2558755744778174101195375

theorem tailTrace_4983159 : CollatzResearch.WordTrace tailWord_4983159 prefixEnd_4983159 2558755744778174101195375 := by
  unfold tailWord_4983159
  simp only [CollatzResearch.WordTrace]
  refine ⟨181750740153873473646296531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121167160102582315764197687 181750740153873473646296531)
  ·
    refine ⟨272626110230810210469444797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 181750740153873473646296531 272626110230810210469444797)
    ·
      refine ⟨102234791336553828926041799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 272626110230810210469444797 102234791336553828926041799)
      ·
        refine ⟨153352187004830743389062699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 102234791336553828926041799 153352187004830743389062699)
        ·
          refine ⟨230028280507246115083594049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 153352187004830743389062699 230028280507246115083594049)
          ·
            refine ⟨172521210380434586312695537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 230028280507246115083594049 172521210380434586312695537)
            ·
              refine ⟨129390907785325939734521653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 172521210380434586312695537 129390907785325939734521653)
              ·
                refine ⟨12130397604874306850111405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 129390907785325939734521653 12130397604874306850111405)
                ·
                  refine ⟨4548899101827865068791777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12130397604874306850111405 4548899101827865068791777)
                  ·
                    refine ⟨3411674326370898801593833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4548899101827865068791777 3411674326370898801593833)
                    ·
                      refine ⟨2558755744778174101195375, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3411674326370898801593833 2558755744778174101195375)
                      ·
                        rfl

theorem cell23_4983159_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 2, 5, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 2, 5, 3, 2, 2].length) (baseStart_4983159 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4983159 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4983159 prefixEnd_4983159 := by exact prefixLift 4983159
  have htrace : WordTrace (prefixWord ++ tailWord_4983159) baseStart_4983159 baseEnd_4983159 := by
    simpa [prefixWord, tailWord_4983159, baseEnd_4983159] using wordTrace_append hprefix tailTrace_4983159
  have hstable : (prefixWord ++ tailWord_4983159).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4983159).length < 2 ^ (prefixWord ++ tailWord_4983159).sum := by decide
  have hdescent : baseEnd_4983159 < baseStart_4983159 := by decide
  rcases family_descends (prefixWord ++ tailWord_4983159) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4983165 : List Nat := [1, 4, 1, 1, 2, 3, 1, 10]
def baseStart_4983165 : Nat := 118140960795 + 4983165 * 2 ^ 59
def prefixEnd_4983165 : Nat := 4983230072969 + 3 ^ 40 * 4983165 * 2
def baseEnd_4983165 : Nat := 94768845394892632508161

theorem tailTrace_4983165 : CollatzResearch.WordTrace tailWord_4983165 prefixEnd_4983165 94768845394892632508161 := by
  unfold tailWord_4983165
  simp only [CollatzResearch.WordTrace]
  refine ⟨181750958991851736671014949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121167305994567824447343299 181750958991851736671014949)
  ·
    refine ⟨34078304810972200625815303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 181750958991851736671014949 34078304810972200625815303)
    ·
      refine ⟨51117457216458300938722955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34078304810972200625815303 51117457216458300938722955)
      ·
        refine ⟨76676185824687451408084433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51117457216458300938722955 76676185824687451408084433)
        ·
          refine ⟨57507139368515588556063325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 76676185824687451408084433 57507139368515588556063325)
          ·
            refine ⟨21565177263193345708523747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 57507139368515588556063325 21565177263193345708523747)
            ·
              refine ⟨32347765894790018562785621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21565177263193345708523747 32347765894790018562785621)
              ·
                refine ⟨94768845394892632508161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 32347765894790018562785621 94768845394892632508161)
                ·
                  rfl

theorem cell23_4983165_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 3, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 3, 1, 10].length) (baseStart_4983165 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4983165 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4983165 prefixEnd_4983165 := by exact prefixLift 4983165
  have htrace : WordTrace (prefixWord ++ tailWord_4983165) baseStart_4983165 baseEnd_4983165 := by
    simpa [prefixWord, tailWord_4983165, baseEnd_4983165] using wordTrace_append hprefix tailTrace_4983165
  have hstable : (prefixWord ++ tailWord_4983165).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4983165).length < 2 ^ (prefixWord ++ tailWord_4983165).sum := by decide
  have hdescent : baseEnd_4983165 < baseStart_4983165 := by decide
  rcases family_descends (prefixWord ++ tailWord_4983165) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4983172 : List Nat := [2, 3, 2, 1, 1, 2, 2, 3, 1, 2, 4]
def baseStart_4983172 : Nat := 118140960795 + 4983172 * 2 ^ 59
def prefixEnd_4983172 : Nat := 4983230072969 + 3 ^ 40 * 4983172 * 2
def baseEnd_4983172 : Nat := 2558762420026682550332815

theorem tailTrace_4983172 : CollatzResearch.WordTrace tailWord_4983172 prefixEnd_4983172 2558762420026682550332815 := by
  unfold tailWord_4983172
  simp only [CollatzResearch.WordTrace]
  refine ⟨90875607151413188433259885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 121167476201884251244346513 90875607151413188433259885)
  ·
    refine ⟨34078352681779945662472457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 90875607151413188433259885 34078352681779945662472457)
    ·
      refine ⟨25558764511334959246854343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34078352681779945662472457 25558764511334959246854343)
      ·
        refine ⟨38338146767002438870281515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25558764511334959246854343 38338146767002438870281515)
        ·
          refine ⟨57507220150503658305422273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38338146767002438870281515 57507220150503658305422273)
          ·
            refine ⟨43130415112877743729066705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 57507220150503658305422273 43130415112877743729066705)
            ·
              refine ⟨32347811334658307796800029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 43130415112877743729066705 32347811334658307796800029)
              ·
                refine ⟨12130429250496865423800011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 32347811334658307796800029 12130429250496865423800011)
                ·
                  refine ⟨18195643875745298135700017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12130429250496865423800011 18195643875745298135700017)
                  ·
                    refine ⟨13646732906808973601775013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 18195643875745298135700017 13646732906808973601775013)
                    ·
                      refine ⟨2558762420026682550332815, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13646732906808973601775013 2558762420026682550332815)
                      ·
                        rfl

theorem cell23_4983172_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 2, 3, 1, 2, 4].length) (baseStart_4983172 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4983172 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4983172 prefixEnd_4983172 := by exact prefixLift 4983172
  have htrace : WordTrace (prefixWord ++ tailWord_4983172) baseStart_4983172 baseEnd_4983172 := by
    simpa [prefixWord, tailWord_4983172, baseEnd_4983172] using wordTrace_append hprefix tailTrace_4983172
  have hstable : (prefixWord ++ tailWord_4983172).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4983172).length < 2 ^ (prefixWord ++ tailWord_4983172).sum := by decide
  have hdescent : baseEnd_4983172 < baseStart_4983172 := by decide
  rcases family_descends (prefixWord ++ tailWord_4983172) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4983179 : List Nat := [1, 1, 1, 1, 4, 4, 3, 2, 1, 2, 3]
def baseStart_4983179 : Nat := 118140960795 + 4983179 * 2 ^ 59
def prefixEnd_4983179 : Nat := 4983230072969 + 3 ^ 40 * 4983179 * 2
def baseEnd_4983179 : Nat := 2558766014391264022945283

theorem tailTrace_4983179 : CollatzResearch.WordTrace tailWord_4983179 prefixEnd_4983179 2558766014391264022945283 := by
  unfold tailWord_4983179
  simp only [CollatzResearch.WordTrace]
  refine ⟨181751469613801017062024591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121167646409200678041349727 181751469613801017062024591)
  ·
    refine ⟨272627204420701525593036887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 181751469613801017062024591 272627204420701525593036887)
    ·
      refine ⟨408940806631052288389555331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 272627204420701525593036887 408940806631052288389555331)
      ·
        refine ⟨613411209946578432584332997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 408940806631052288389555331 613411209946578432584332997)
        ·
          refine ⟨115014601864983456109562437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 613411209946578432584332997 115014601864983456109562437)
          ·
            refine ⟨21565237849684398020542957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 115014601864983456109562437 21565237849684398020542957)
            ·
              refine ⟨8086964193631649257703609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21565237849684398020542957 8086964193631649257703609)
              ·
                refine ⟨6065223145223736943277707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8086964193631649257703609 6065223145223736943277707)
                ·
                  refine ⟨9097834717835605414916561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6065223145223736943277707 9097834717835605414916561)
                  ·
                    refine ⟨6823376038376704061187421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9097834717835605414916561 6823376038376704061187421)
                    ·
                      refine ⟨2558766014391264022945283, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6823376038376704061187421 2558766014391264022945283)
                      ·
                        rfl

theorem cell23_4983179_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 4, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 4, 3, 2, 1, 2, 3].length) (baseStart_4983179 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4983179 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4983179 prefixEnd_4983179 := by exact prefixLift 4983179
  have htrace : WordTrace (prefixWord ++ tailWord_4983179) baseStart_4983179 baseEnd_4983179 := by
    simpa [prefixWord, tailWord_4983179, baseEnd_4983179] using wordTrace_append hprefix tailTrace_4983179
  have hstable : (prefixWord ++ tailWord_4983179).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4983179).length < 2 ^ (prefixWord ++ tailWord_4983179).sum := by decide
  have hdescent : baseEnd_4983179 < baseStart_4983179 := by decide
  rcases family_descends (prefixWord ++ tailWord_4983179) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4983182 : List Nat := [4, 1, 1, 4, 1, 1, 2, 9]
def baseStart_4983182 : Nat := 118140960795 + 4983182 * 2 ^ 59
def prefixEnd_4983182 : Nat := 4983230072969 + 3 ^ 40 * 4983182 * 2
def baseEnd_4983182 : Nat := 94769168697526944859547

theorem tailTrace_4983182 : CollatzResearch.WordTrace tailWord_4983182 prefixEnd_4983182 94769168697526944859547 := by
  unfold tailWord_4983182
  simp only [CollatzResearch.WordTrace]
  refine ⟨22718947379098768571797975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 121167719355193432382922533 22718947379098768571797975)
  ·
    refine ⟨34078421068648152857696963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22718947379098768571797975 34078421068648152857696963)
    ·
      refine ⟨51117631602972229286545445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34078421068648152857696963 51117631602972229286545445)
      ·
        refine ⟨9584555925557292991227271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 51117631602972229286545445 9584555925557292991227271)
        ·
          refine ⟨14376833888335939486840907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9584555925557292991227271 14376833888335939486840907)
          ·
            refine ⟨21565250832503909230261361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14376833888335939486840907 21565250832503909230261361)
            ·
              refine ⟨16173938124377931922696021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21565250832503909230261361 16173938124377931922696021)
              ·
                refine ⟨94769168697526944859547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 16173938124377931922696021 94769168697526944859547)
                ·
                  rfl

theorem cell23_4983182_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 1, 2, 9].length) (baseStart_4983182 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4983182 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4983182 prefixEnd_4983182 := by exact prefixLift 4983182
  have htrace : WordTrace (prefixWord ++ tailWord_4983182) baseStart_4983182 baseEnd_4983182 := by
    simpa [prefixWord, tailWord_4983182, baseEnd_4983182] using wordTrace_append hprefix tailTrace_4983182
  have hstable : (prefixWord ++ tailWord_4983182).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4983182).length < 2 ^ (prefixWord ++ tailWord_4983182).sum := by decide
  have hdescent : baseEnd_4983182 < baseStart_4983182 := by decide
  rcases family_descends (prefixWord ++ tailWord_4983182) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4983233 : List Nat := [1, 2, 7, 1, 1, 1, 3, 7]
def baseStart_4983233 : Nat := 118140960795 + 4983233 * 2 ^ 59
def prefixEnd_4983233 : Nat := 4983230072969 + 3 ^ 40 * 4983233 * 2
def baseEnd_4983233 : Nat := 94770138605429881913705

theorem tailTrace_4983233 : CollatzResearch.WordTrace tailWord_4983233 prefixEnd_4983233 94770138605429881913705 := by
  unfold tailWord_4983233
  simp only [CollatzResearch.WordTrace]
  refine ⟨181753439155605384284490353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121168959437070256189660235 181753439155605384284490353)
  ·
    refine ⟨136315079366704038213367765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 181753439155605384284490353 136315079366704038213367765)
    ·
      refine ⟨3194884672657125895625807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 136315079366704038213367765 3194884672657125895625807)
      ·
        refine ⟨4792327008985688843438711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3194884672657125895625807 4792327008985688843438711)
        ·
          refine ⟨7188490513478533265158067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4792327008985688843438711 7188490513478533265158067)
          ·
            refine ⟨10782735770217799897737101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7188490513478533265158067 10782735770217799897737101)
            ·
              refine ⟨4043525913831674961651413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10782735770217799897737101 4043525913831674961651413)
              ·
                refine ⟨94770138605429881913705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4043525913831674961651413 94770138605429881913705)
                ·
                  rfl

theorem cell23_4983233_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 7, 1, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 7, 1, 1, 1, 3, 7].length) (baseStart_4983233 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4983233 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4983233 prefixEnd_4983233 := by exact prefixLift 4983233
  have htrace : WordTrace (prefixWord ++ tailWord_4983233) baseStart_4983233 baseEnd_4983233 := by
    simpa [prefixWord, tailWord_4983233, baseEnd_4983233] using wordTrace_append hprefix tailTrace_4983233
  have hstable : (prefixWord ++ tailWord_4983233).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4983233).length < 2 ^ (prefixWord ++ tailWord_4983233).sum := by decide
  have hdescent : baseEnd_4983233 < baseStart_4983233 := by decide
  rcases family_descends (prefixWord ++ tailWord_4983233) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4983253 : List Nat := [1, 3, 2, 3, 1, 2, 4, 1, 1, 3, 2]
def baseStart_4983253 : Nat := 118140960795 + 4983253 * 2 ^ 59
def prefixEnd_4983253 : Nat := 4983230072969 + 3 ^ 40 * 4983253 * 2
def baseEnd_4983253 : Nat := 2558804011959696733419943

theorem tailTrace_4983253 : CollatzResearch.WordTrace tailWord_4983253 prefixEnd_4983253 2558804011959696733419943 := by
  unfold tailWord_4983253
  simp only [CollatzResearch.WordTrace]
  refine ⟨181754168615532927700218413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121169445743688618466812275 181754168615532927700218413)
  ·
    refine ⟨68157813230824847887581905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 181754168615532927700218413 68157813230824847887581905)
    ·
      refine ⟨51118359923118635915686429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 68157813230824847887581905 51118359923118635915686429)
      ·
        refine ⟨19169384971169488468382411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 51118359923118635915686429 19169384971169488468382411)
        ·
          refine ⟨28754077456754232702573617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19169384971169488468382411 28754077456754232702573617)
          ·
            refine ⟨21565558092565674526930213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28754077456754232702573617 21565558092565674526930213)
            ·
              refine ⟨4043542142356063973799415, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 21565558092565674526930213 4043542142356063973799415)
              ·
                refine ⟨6065313213534095960699123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4043542142356063973799415 6065313213534095960699123)
                ·
                  refine ⟨9097969820301143941048685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6065313213534095960699123 9097969820301143941048685)
                  ·
                    refine ⟨3411738682612928977893257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9097969820301143941048685 3411738682612928977893257)
                    ·
                      refine ⟨2558804011959696733419943, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3411738682612928977893257 2558804011959696733419943)
                      ·
                        rfl

theorem cell23_4983253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 2, 4, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 2, 4, 1, 1, 3, 2].length) (baseStart_4983253 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4983253 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4983253 prefixEnd_4983253 := by exact prefixLift 4983253
  have htrace : WordTrace (prefixWord ++ tailWord_4983253) baseStart_4983253 baseEnd_4983253 := by
    simpa [prefixWord, tailWord_4983253, baseEnd_4983253] using wordTrace_append hprefix tailTrace_4983253
  have hstable : (prefixWord ++ tailWord_4983253).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4983253).length < 2 ^ (prefixWord ++ tailWord_4983253).sum := by decide
  have hdescent : baseEnd_4983253 < baseStart_4983253 := by decide
  rcases family_descends (prefixWord ++ tailWord_4983253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4983272 : List Nat := [2, 1, 4, 1, 1, 3, 1, 3, 7]
def baseStart_4983272 : Nat := 118140960795 + 4983272 * 2 ^ 59
def prefixEnd_4983272 : Nat := 4983230072969 + 3 ^ 40 * 4983272 * 2
def baseEnd_4983272 : Nat := 284312640899125795453595

theorem tailTrace_4983272 : CollatzResearch.WordTrace tailWord_4983272 prefixEnd_4983272 284312640899125795453595 := by
  unfold tailWord_4983272
  simp only [CollatzResearch.WordTrace]
  refine ⟨90877430801232046972580035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 121169907734976062630106713 90877430801232046972580035)
  ·
    refine ⟨136316146201848070458870053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90877430801232046972580035 136316146201848070458870053)
    ·
      refine ⟨25559277412846513211038135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 136316146201848070458870053 25559277412846513211038135)
      ·
        refine ⟨38338916119269769816557203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25559277412846513211038135 38338916119269769816557203)
        ·
          refine ⟨57508374178904654724835805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38338916119269769816557203 57508374178904654724835805)
          ·
            refine ⟨21565640317089245521813427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 57508374178904654724835805 21565640317089245521813427)
            ·
              refine ⟨32348460475633868282720141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21565640317089245521813427 32348460475633868282720141)
              ·
                refine ⟨12130672678362700606020053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 32348460475633868282720141 12130672678362700606020053)
                ·
                  refine ⟨284312640899125795453595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 12130672678362700606020053 284312640899125795453595)
                  ·
                    rfl

theorem cell23_4983272_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 3, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 3, 1, 3, 7].length) (baseStart_4983272 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4983272 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4983272 prefixEnd_4983272 := by exact prefixLift 4983272
  have htrace : WordTrace (prefixWord ++ tailWord_4983272) baseStart_4983272 baseEnd_4983272 := by
    simpa [prefixWord, tailWord_4983272, baseEnd_4983272] using wordTrace_append hprefix tailTrace_4983272
  have hstable : (prefixWord ++ tailWord_4983272).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4983272).length < 2 ^ (prefixWord ++ tailWord_4983272).sum := by decide
  have hdescent : baseEnd_4983272 < baseStart_4983272 := by decide
  rcases family_descends (prefixWord ++ tailWord_4983272) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4983283 : List Nat := [1, 1, 1, 2, 2, 2, 7, 1, 2, 2, 2]
def baseStart_4983283 : Nat := 118140960795 + 4983283 * 2 ^ 59
def prefixEnd_4983283 : Nat := 4983230072969 + 3 ^ 40 * 4983283 * 2
def baseEnd_4983283 : Nat := 2558819416379331616044805

theorem tailTrace_4983283 : CollatzResearch.WordTrace tailWord_4983283 prefixEnd_4983283 2558819416379331616044805 := by
  unfold tailWord_4983283
  simp only [CollatzResearch.WordTrace]
  refine ⟨181755262805424242823810503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121170175203616161882540335 181755262805424242823810503)
  ·
    refine ⟨272632894208136364235715755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 181755262805424242823810503 272632894208136364235715755)
    ·
      refine ⟨408949341312204546353573633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 272632894208136364235715755 408949341312204546353573633)
      ·
        refine ⟨306712005984153409765180225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 408949341312204546353573633 306712005984153409765180225)
        ·
          refine ⟨230034004488115057323885169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 306712005984153409765180225 230034004488115057323885169)
          ·
            refine ⟨172525503366086292992913877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 230034004488115057323885169 172525503366086292992913877)
            ·
              refine ⟨4043566485142647492021419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 172525503366086292992913877 4043566485142647492021419)
              ·
                refine ⟨6065349727713971238032129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4043566485142647492021419 6065349727713971238032129)
                ·
                  refine ⟨4549012295785478428524097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6065349727713971238032129 4549012295785478428524097)
                  ·
                    refine ⟨3411759221839108821393073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4549012295785478428524097 3411759221839108821393073)
                    ·
                      refine ⟨2558819416379331616044805, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3411759221839108821393073 2558819416379331616044805)
                      ·
                        rfl

theorem cell23_4983283_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 7, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 7, 1, 2, 2, 2].length) (baseStart_4983283 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4983283 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4983283 prefixEnd_4983283 := by exact prefixLift 4983283
  have htrace : WordTrace (prefixWord ++ tailWord_4983283) baseStart_4983283 baseEnd_4983283 := by
    simpa [prefixWord, tailWord_4983283, baseEnd_4983283] using wordTrace_append hprefix tailTrace_4983283
  have hstable : (prefixWord ++ tailWord_4983283).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4983283).length < 2 ^ (prefixWord ++ tailWord_4983283).sum := by decide
  have hdescent : baseEnd_4983283 < baseStart_4983283 := by decide
  rcases family_descends (prefixWord ++ tailWord_4983283) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4983339 : List Nat := [1, 1, 1, 1, 2, 1, 3, 5, 2, 4, 2]
def baseStart_4983339 : Nat := 118140960795 + 4983339 * 2 ^ 59
def prefixEnd_4983339 : Nat := 4983230072969 + 3 ^ 40 * 4983339 * 2
def baseEnd_4983339 : Nat := 2558848171295983396944547

theorem tailTrace_4983339 : CollatzResearch.WordTrace tailWord_4983339 prefixEnd_4983339 2558848171295983396944547 := by
  unfold tailWord_4983339
  simp only [CollatzResearch.WordTrace]
  refine ⟨181757305293221364387849071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121171536862147576258566047 181757305293221364387849071)
  ·
    refine ⟨272635957939832046581773607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 181757305293221364387849071 272635957939832046581773607)
    ·
      refine ⟨408953936909748069872660411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 272635957939832046581773607 408953936909748069872660411)
      ·
        refine ⟨613430905364622104808990617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 408953936909748069872660411 613430905364622104808990617)
        ·
          refine ⟨460073179023466578606742963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 613430905364622104808990617 460073179023466578606742963)
          ·
            refine ⟨690109768535199867910114445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 460073179023466578606742963 690109768535199867910114445)
            ·
              refine ⟨258791163200699950466292917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 690109768535199867910114445 258791163200699950466292917)
              ·
                refine ⟨24261671550065620356214961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 258791163200699950466292917 24261671550065620356214961)
                ·
                  refine ⟨18196253662549215267161221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 24261671550065620356214961 18196253662549215267161221)
                  ·
                    refine ⟨3411797561727977862592729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 18196253662549215267161221 3411797561727977862592729)
                    ·
                      refine ⟨2558848171295983396944547, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3411797561727977862592729 2558848171295983396944547)
                      ·
                        rfl

theorem cell23_4983339_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 3, 5, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 3, 5, 2, 4, 2].length) (baseStart_4983339 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4983339 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4983339 prefixEnd_4983339 := by exact prefixLift 4983339
  have htrace : WordTrace (prefixWord ++ tailWord_4983339) baseStart_4983339 baseEnd_4983339 := by
    simpa [prefixWord, tailWord_4983339, baseEnd_4983339] using wordTrace_append hprefix tailTrace_4983339
  have hstable : (prefixWord ++ tailWord_4983339).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4983339).length < 2 ^ (prefixWord ++ tailWord_4983339).sum := by decide
  have hdescent : baseEnd_4983339 < baseStart_4983339 := by decide
  rcases family_descends (prefixWord ++ tailWord_4983339) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4983349 : List Nat := [1, 3, 3, 1, 1, 2, 2, 1, 5, 4]
def baseStart_4983349 : Nat := 118140960795 + 4983349 * 2 ^ 59
def prefixEnd_4983349 : Nat := 4983230072969 + 3 ^ 40 * 4983349 * 2
def baseEnd_4983349 : Nat := 852951102034176119273167

theorem tailTrace_4983349 : CollatzResearch.WordTrace tailWord_4983349 prefixEnd_4983349 852951102034176119273167 := by
  unfold tailWord_4983349
  simp only [CollatzResearch.WordTrace]
  refine ⟨181757670023185136095713101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121171780015456757397142067 181757670023185136095713101)
  ·
    refine ⟨68159126258694426035892413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 181757670023185136095713101 68159126258694426035892413)
    ·
      refine ⟨25559672347010409763459655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 68159126258694426035892413 25559672347010409763459655)
      ·
        refine ⟨38339508520515614645189483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25559672347010409763459655 38339508520515614645189483)
        ·
          refine ⟨57509262780773421967784225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38339508520515614645189483 57509262780773421967784225)
          ·
            refine ⟨43131947085580066475838169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 57509262780773421967784225 43131947085580066475838169)
            ·
              refine ⟨32348960314185049856878627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 43131947085580066475838169 32348960314185049856878627)
              ·
                refine ⟨48523440471277574785317941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32348960314185049856878627 48523440471277574785317941)
                ·
                  refine ⟨4549072544182272636123557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 48523440471277574785317941 4549072544182272636123557)
                  ·
                    refine ⟨852951102034176119273167, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4549072544182272636123557 852951102034176119273167)
                    ·
                      rfl

theorem cell23_4983349_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 2, 1, 5, 4].length) (baseStart_4983349 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4983349 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4983349 prefixEnd_4983349 := by exact prefixLift 4983349
  have htrace : WordTrace (prefixWord ++ tailWord_4983349) baseStart_4983349 baseEnd_4983349 := by
    simpa [prefixWord, tailWord_4983349, baseEnd_4983349] using wordTrace_append hprefix tailTrace_4983349
  have hstable : (prefixWord ++ tailWord_4983349).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4983349).length < 2 ^ (prefixWord ++ tailWord_4983349).sum := by decide
  have hdescent : baseEnd_4983349 < baseStart_4983349 := by decide
  rcases family_descends (prefixWord ++ tailWord_4983349) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4983356 : List Nat := [2, 2, 2, 2, 3, 2, 2, 1, 2, 1, 4]
def baseStart_4983356 : Nat := 118140960795 + 4983356 * 2 ^ 59
def prefixEnd_4983356 : Nat := 4983230072969 + 3 ^ 40 * 4983356 * 2
def baseEnd_4983356 : Nat := 2558856900467109830431969

theorem tailTrace_4983356 : CollatzResearch.WordTrace tailWord_4983356 prefixEnd_4983356 2558856900467109830431969 := by
  unfold tailWord_4983356
  simp only [CollatzResearch.WordTrace]
  refine ⟨90878962667079888145608961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 121171950222773184194145281 90878962667079888145608961)
  ·
    refine ⟨68159222000309916109206721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 90878962667079888145608961 68159222000309916109206721)
    ·
      refine ⟨51119416500232437081905041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 68159222000309916109206721 51119416500232437081905041)
      ·
        refine ⟨38339562375174327811428781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 51119416500232437081905041 38339562375174327811428781)
        ·
          refine ⟨14377335890690372929285793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 38339562375174327811428781 14377335890690372929285793)
          ·
            refine ⟨10783001918017779696964345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14377335890690372929285793 10783001918017779696964345)
            ·
              refine ⟨8087251438513334772723259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10783001918017779696964345 8087251438513334772723259)
              ·
                refine ⟨12130877157770002159084889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8087251438513334772723259 12130877157770002159084889)
                ·
                  refine ⟨9098157868327501619313667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12130877157770002159084889 9098157868327501619313667)
                  ·
                    refine ⟨13647236802491252428970501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9098157868327501619313667 13647236802491252428970501)
                    ·
                      refine ⟨2558856900467109830431969, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13647236802491252428970501 2558856900467109830431969)
                      ·
                        rfl

theorem cell23_4983356_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 2, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 2, 2, 1, 2, 1, 4].length) (baseStart_4983356 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4983356 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4983356 prefixEnd_4983356 := by exact prefixLift 4983356
  have htrace : WordTrace (prefixWord ++ tailWord_4983356) baseStart_4983356 baseEnd_4983356 := by
    simpa [prefixWord, tailWord_4983356, baseEnd_4983356] using wordTrace_append hprefix tailTrace_4983356
  have hstable : (prefixWord ++ tailWord_4983356).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4983356).length < 2 ^ (prefixWord ++ tailWord_4983356).sum := by decide
  have hdescent : baseEnd_4983356 < baseStart_4983356 := by decide
  rcases family_descends (prefixWord ++ tailWord_4983356) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4983410 : List Nat := [3, 2, 1, 2, 5, 1, 1, 1, 2, 2, 3]
def baseStart_4983410 : Nat := 118140960795 + 4983410 * 2 ^ 59
def prefixEnd_4983410 : Nat := 4983230072969 + 3 ^ 40 * 4983410 * 2
def baseEnd_4983410 : Nat := 2558884628422452619156721

theorem tailTrace_4983410 : CollatzResearch.WordTrace tailWord_4983410 prefixEnd_4983410 2558884628422452619156721 := by
  unfold tailWord_4983410
  simp only [CollatzResearch.WordTrace]
  refine ⟨45439973718991035878420921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 121173263250642762342455789 45439973718991035878420921)
  ·
    refine ⟨34079980289243276908815691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45439973718991035878420921 34079980289243276908815691)
    ·
      refine ⟨51119970433864915363223537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34079980289243276908815691 51119970433864915363223537)
      ·
        refine ⟨38339977825398686522417653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 51119970433864915363223537 38339977825398686522417653)
        ·
          refine ⟨3594372921131126861476655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 38339977825398686522417653 3594372921131126861476655)
          ·
            refine ⟨5391559381696690292214983, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3594372921131126861476655 5391559381696690292214983)
            ·
              refine ⟨8087339072545035438322475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5391559381696690292214983 8087339072545035438322475)
              ·
                refine ⟨12131008608817553157483713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8087339072545035438322475 12131008608817553157483713)
                ·
                  refine ⟨9098256456613164868112785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12131008608817553157483713 9098256456613164868112785)
                  ·
                    refine ⟨6823692342459873651084589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9098256456613164868112785 6823692342459873651084589)
                    ·
                      refine ⟨2558884628422452619156721, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6823692342459873651084589 2558884628422452619156721)
                      ·
                        rfl

theorem cell23_4983410_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 5, 1, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 5, 1, 1, 1, 2, 2, 3].length) (baseStart_4983410 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4983410 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4983410 prefixEnd_4983410 := by exact prefixLift 4983410
  have htrace : WordTrace (prefixWord ++ tailWord_4983410) baseStart_4983410 baseEnd_4983410 := by
    simpa [prefixWord, tailWord_4983410, baseEnd_4983410] using wordTrace_append hprefix tailTrace_4983410
  have hstable : (prefixWord ++ tailWord_4983410).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4983410).length < 2 ^ (prefixWord ++ tailWord_4983410).sum := by decide
  have hdescent : baseEnd_4983410 < baseStart_4983410 := by decide
  rcases family_descends (prefixWord ++ tailWord_4983410) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4983439 : List Nat := [1, 1, 2, 1, 1, 1, 1, 7, 4, 4]
def baseStart_4983439 : Nat := 118140960795 + 4983439 * 2 ^ 59
def prefixEnd_4983439 : Nat := 4983230072969 + 3 ^ 40 * 4983439 * 2
def baseEnd_4983439 : Nat := 852966506453811001898029

theorem tailTrace_4983439 : CollatzResearch.WordTrace tailWord_4983439 prefixEnd_4983439 852966506453811001898029 := by
  unfold tailWord_4983439
  simp only [CollatzResearch.WordTrace]
  refine ⟨181760952592859081466489371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121173968395239387644326247 181760952592859081466489371)
  ·
    refine ⟨272641428889288622199734057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 181760952592859081466489371 272641428889288622199734057)
    ·
      refine ⟨204481071666966466649800543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 272641428889288622199734057 204481071666966466649800543)
      ·
        refine ⟨306721607500449699974700815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 204481071666966466649800543 306721607500449699974700815)
        ·
          refine ⟨460082411250674549962051223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 306721607500449699974700815 460082411250674549962051223)
          ·
            refine ⟨690123616876011824943076835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 460082411250674549962051223 690123616876011824943076835)
            ·
              refine ⟨1035185425314017737414615253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 690123616876011824943076835 1035185425314017737414615253)
              ·
                refine ⟨24262158405797290720655045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1035185425314017737414615253 24262158405797290720655045)
                ·
                  refine ⟨4549154701086992010122821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 24262158405797290720655045 4549154701086992010122821)
                  ·
                    refine ⟨852966506453811001898029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4549154701086992010122821 852966506453811001898029)
                    ·
                      rfl

theorem cell23_4983439_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 7, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 7, 4, 4].length) (baseStart_4983439 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4983439 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4983439 prefixEnd_4983439 := by exact prefixLift 4983439
  have htrace : WordTrace (prefixWord ++ tailWord_4983439) baseStart_4983439 baseEnd_4983439 := by
    simpa [prefixWord, tailWord_4983439, baseEnd_4983439] using wordTrace_append hprefix tailTrace_4983439
  have hstable : (prefixWord ++ tailWord_4983439).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4983439).length < 2 ^ (prefixWord ++ tailWord_4983439).sum := by decide
  have hdescent : baseEnd_4983439 < baseStart_4983439 := by decide
  rcases family_descends (prefixWord ++ tailWord_4983439) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4983449 : List Nat := [1, 2, 1, 2, 1, 2, 5, 2, 1, 1, 5]
def baseStart_4983449 : Nat := 118140960795 + 4983449 * 2 ^ 59
def prefixEnd_4983449 : Nat := 4983230072969 + 3 ^ 40 * 4983449 * 2
def baseEnd_4983449 : Nat := 2558904654167977966569041

theorem tailTrace_4983449 : CollatzResearch.WordTrace tailWord_4983449 prefixEnd_4983449 2558904654167977966569041 := by
  unfold tailWord_4983449
  simp only [CollatzResearch.WordTrace]
  refine ⟨181761317322822853174353401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121174211548548568782902267 181761317322822853174353401)
  ·
    refine ⟨136320987992117139880765051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 181761317322822853174353401 136320987992117139880765051)
    ·
      refine ⟨204481481988175709821147577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 136320987992117139880765051 204481481988175709821147577)
      ·
        refine ⟨153361111491131782365860683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 204481481988175709821147577 153361111491131782365860683)
        ·
          refine ⟨230041667236697673548791025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 153361111491131782365860683 230041667236697673548791025)
          ·
            refine ⟨172531250427523255161593269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 230041667236697673548791025 172531250427523255161593269)
            ·
              refine ⟨16174804727580305171399369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 172531250427523255161593269 16174804727580305171399369)
              ·
                refine ⟨12131103545685228878549527, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16174804727580305171399369 12131103545685228878549527)
                ·
                  refine ⟨18196655318527843317824291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12131103545685228878549527 18196655318527843317824291)
                  ·
                    refine ⟨27294982977791764976736437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 18196655318527843317824291 27294982977791764976736437)
                    ·
                      refine ⟨2558904654167977966569041, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 27294982977791764976736437 2558904654167977966569041)
                      ·
                        rfl

theorem cell23_4983449_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 5, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 5, 2, 1, 1, 5].length) (baseStart_4983449 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4983449 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4983449 prefixEnd_4983449 := by exact prefixLift 4983449
  have htrace : WordTrace (prefixWord ++ tailWord_4983449) baseStart_4983449 baseEnd_4983449 := by
    simpa [prefixWord, tailWord_4983449, baseEnd_4983449] using wordTrace_append hprefix tailTrace_4983449
  have hstable : (prefixWord ++ tailWord_4983449).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4983449).length < 2 ^ (prefixWord ++ tailWord_4983449).sum := by decide
  have hdescent : baseEnd_4983449 < baseStart_4983449 := by decide
  rcases family_descends (prefixWord ++ tailWord_4983449) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4983459 : List Nat := [1, 1, 1, 4, 1, 1, 2, 5, 1, 2, 4]
def baseStart_4983459 : Nat := 118140960795 + 4983459 * 2 ^ 59
def prefixEnd_4983459 : Nat := 4983230072969 + 3 ^ 40 * 4983459 * 2
def baseEnd_4983459 : Nat := 2558909788974522927443995

theorem tailTrace_4983459 : CollatzResearch.WordTrace tailWord_4983459 prefixEnd_4983459 2558909788974522927443995 := by
  unfold tailWord_4983459
  simp only [CollatzResearch.WordTrace]
  refine ⟨181761682052786624882217431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121174454701857749921478287 181761682052786624882217431)
  ·
    refine ⟨272642523079179937323326147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 181761682052786624882217431 272642523079179937323326147)
    ·
      refine ⟨408963784618769905984989221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 272642523079179937323326147 408963784618769905984989221)
      ·
        refine ⟨76680709616019357372185479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 408963784618769905984989221 76680709616019357372185479)
        ·
          refine ⟨115021064424029036058278219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 76680709616019357372185479 115021064424029036058278219)
          ·
            refine ⟨172531596636043554087417329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 115021064424029036058278219 172531596636043554087417329)
            ·
              refine ⟨129398697477032665565562997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 172531596636043554087417329 129398697477032665565562997)
              ·
                refine ⟨12131127888471812396771531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 129398697477032665565562997 12131127888471812396771531)
                ·
                  refine ⟨18196691832707718595157297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12131127888471812396771531 18196691832707718595157297)
                  ·
                    refine ⟨13647518874530788946367973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 18196691832707718595157297 13647518874530788946367973)
                    ·
                      refine ⟨2558909788974522927443995, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13647518874530788946367973 2558909788974522927443995)
                      ·
                        rfl

theorem cell23_4983459_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 2, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 2, 5, 1, 2, 4].length) (baseStart_4983459 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4983459 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4983459 prefixEnd_4983459 := by exact prefixLift 4983459
  have htrace : WordTrace (prefixWord ++ tailWord_4983459) baseStart_4983459 baseEnd_4983459 := by
    simpa [prefixWord, tailWord_4983459, baseEnd_4983459] using wordTrace_append hprefix tailTrace_4983459
  have hstable : (prefixWord ++ tailWord_4983459).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4983459).length < 2 ^ (prefixWord ++ tailWord_4983459).sum := by decide
  have hdescent : baseEnd_4983459 < baseStart_4983459 := by decide
  rcases family_descends (prefixWord ++ tailWord_4983459) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4983513 : List Nat := [1, 2, 1, 2, 3, 2, 3, 3, 2, 1, 3]
def baseStart_4983513 : Nat := 118140960795 + 4983513 * 2 ^ 59
def prefixEnd_4983513 : Nat := 4983230072969 + 3 ^ 40 * 4983513 * 2
def baseEnd_4983513 : Nat := 2558937516929865716168747

theorem tailTrace_4983513 : CollatzResearch.WordTrace tailWord_4983513 prefixEnd_4983513 2558937516929865716168747 := by
  unfold tailWord_4983513
  simp only [CollatzResearch.WordTrace]
  refine ⟨181763651594590992104683193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121175767729727328069788795 181763651594590992104683193)
  ·
    refine ⟨136322738695943244078512395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 181763651594590992104683193 136322738695943244078512395)
    ·
      refine ⟨204484108043914866117768593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 136322738695943244078512395 204484108043914866117768593)
      ·
        refine ⟨153363081032936149588326445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 204484108043914866117768593 153363081032936149588326445)
        ·
          refine ⟨57511155387351056095622417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 153363081032936149588326445 57511155387351056095622417)
          ·
            refine ⟨43133366540513292071716813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 57511155387351056095622417 43133366540513292071716813)
            ·
              refine ⟨16175012452692484526893805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 43133366540513292071716813 16175012452692484526893805)
              ·
                refine ⟨6065629669759681697585177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16175012452692484526893805 6065629669759681697585177)
                ·
                  refine ⟨4549222252319761273188883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6065629669759681697585177 4549222252319761273188883)
                  ·
                    refine ⟨6823833378479641909783325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4549222252319761273188883 6823833378479641909783325)
                    ·
                      refine ⟨2558937516929865716168747, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6823833378479641909783325 2558937516929865716168747)
                      ·
                        rfl

theorem cell23_4983513_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 3, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 3, 3, 2, 1, 3].length) (baseStart_4983513 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4983513 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4983513 prefixEnd_4983513 := by exact prefixLift 4983513
  have htrace : WordTrace (prefixWord ++ tailWord_4983513) baseStart_4983513 baseEnd_4983513 := by
    simpa [prefixWord, tailWord_4983513, baseEnd_4983513] using wordTrace_append hprefix tailTrace_4983513
  have hstable : (prefixWord ++ tailWord_4983513).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4983513).length < 2 ^ (prefixWord ++ tailWord_4983513).sum := by decide
  have hdescent : baseEnd_4983513 < baseStart_4983513 := by decide
  rcases family_descends (prefixWord ++ tailWord_4983513) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4983556 : List Nat := [2, 3, 2, 2, 1, 1, 1, 1, 1, 6, 3]
def baseStart_4983556 : Nat := 118140960795 + 4983556 * 2 ^ 59
def prefixEnd_4983556 : Nat := 4983230072969 + 3 ^ 40 * 4983556 * 2
def baseEnd_4983556 : Nat := 2558959596598009047931049

theorem tailTrace_4983556 : CollatzResearch.WordTrace tailWord_4983556 prefixEnd_4983556 2558959596598009047931049 := by
  unfold tailWord_4983556
  simp only [CollatzResearch.WordTrace]
  refine ⟨90882609966717605224249261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 121176813288956806965665681 90882609966717605224249261)
  ·
    refine ⟨34080978737519101959093473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 90882609966717605224249261 34080978737519101959093473)
    ·
      refine ⟨25560734053139326469320105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34080978737519101959093473 25560734053139326469320105)
      ·
        refine ⟨19170550539854494851990079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25560734053139326469320105 19170550539854494851990079)
        ·
          refine ⟨28755825809781742277985119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19170550539854494851990079 28755825809781742277985119)
          ·
            refine ⟨43133738714672613416977679, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28755825809781742277985119 43133738714672613416977679)
            ·
              refine ⟨64700608072008920125466519, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 43133738714672613416977679 64700608072008920125466519)
              ·
                refine ⟨97050912108013380188199779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 64700608072008920125466519 97050912108013380188199779)
                ·
                  refine ⟨145576368162020070282299669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 97050912108013380188199779 145576368162020070282299669)
                  ·
                    refine ⟨6823892257594690794482797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 145576368162020070282299669 6823892257594690794482797)
                    ·
                      refine ⟨2558959596598009047931049, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6823892257594690794482797 2558959596598009047931049)
                      ·
                        rfl

theorem cell23_4983556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 1, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 1, 1, 1, 6, 3].length) (baseStart_4983556 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4983556 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4983556 prefixEnd_4983556 := by exact prefixLift 4983556
  have htrace : WordTrace (prefixWord ++ tailWord_4983556) baseStart_4983556 baseEnd_4983556 := by
    simpa [prefixWord, tailWord_4983556, baseEnd_4983556] using wordTrace_append hprefix tailTrace_4983556
  have hstable : (prefixWord ++ tailWord_4983556).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4983556).length < 2 ^ (prefixWord ++ tailWord_4983556).sum := by decide
  have hdescent : baseEnd_4983556 < baseStart_4983556 := by decide
  rcases family_descends (prefixWord ++ tailWord_4983556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4983626 : List Nat := [3, 1, 2, 1, 1, 1, 2, 1, 6, 1, 4]
def baseStart_4983626 : Nat := 118140960795 + 4983626 * 2 ^ 59
def prefixEnd_4983626 : Nat := 4983230072969 + 3 ^ 40 * 4983626 * 2
def baseEnd_4983626 : Nat := 2558995540243823774055727

theorem tailTrace_4983626 : CollatzResearch.WordTrace tailWord_4983626 prefixEnd_4983626 2558995540243823774055727 := by
  unfold tailWord_4983626
  simp only [CollatzResearch.WordTrace]
  refine ⟨45441943260795403100886683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 121178515362121074935697821 45441943260795403100886683)
  ·
    refine ⟨68162914891193104651330025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45441943260795403100886683 68162914891193104651330025)
    ·
      refine ⟨51122186168394828488497519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 68162914891193104651330025 51122186168394828488497519)
      ·
        refine ⟨76683279252592242732746279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51122186168394828488497519 76683279252592242732746279)
        ·
          refine ⟨115024918878888364099119419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 76683279252592242732746279 115024918878888364099119419)
          ·
            refine ⟨172537378318332546148679129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 115024918878888364099119419 172537378318332546148679129)
            ·
              refine ⟨129403033738749409611509347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 172537378318332546148679129 129403033738749409611509347)
              ·
                refine ⟨194104550608124114417264021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 129403033738749409611509347 194104550608124114417264021)
                ·
                  refine ⟨9098650809755817863309251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 194104550608124114417264021 9098650809755817863309251)
                  ·
                    refine ⟨13647976214633726794963877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9098650809755817863309251 13647976214633726794963877)
                    ·
                      refine ⟨2558995540243823774055727, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13647976214633726794963877 2558995540243823774055727)
                      ·
                        rfl

theorem cell23_4983626_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 2, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 2, 1, 6, 1, 4].length) (baseStart_4983626 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4983626 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4983626 prefixEnd_4983626 := by exact prefixLift 4983626
  have htrace : WordTrace (prefixWord ++ tailWord_4983626) baseStart_4983626 baseEnd_4983626 := by
    simpa [prefixWord, tailWord_4983626, baseEnd_4983626] using wordTrace_append hprefix tailTrace_4983626
  have hstable : (prefixWord ++ tailWord_4983626).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4983626).length < 2 ^ (prefixWord ++ tailWord_4983626).sum := by decide
  have hdescent : baseEnd_4983626 < baseStart_4983626 := by decide
  rcases family_descends (prefixWord ++ tailWord_4983626) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4983666 : List Nat := [3, 2, 1, 2, 1, 1, 4, 1, 8]
def baseStart_4983666 : Nat := 118140960795 + 4983666 * 2 ^ 59
def prefixEnd_4983666 : Nat := 4983230072969 + 3 ^ 40 * 4983666 * 2
def baseEnd_4983666 : Nat := 284335119941111513061727

theorem tailTrace_4983666 : CollatzResearch.WordTrace tailWord_4983666 prefixEnd_4983666 284335119941111513061727 := by
  unfold tailWord_4983666
  simp only [CollatzResearch.WordTrace]
  refine ⟨45442307990759174808750713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 121179487975357799490001901 45442307990759174808750713)
  ·
    refine ⟨34081730993069381106563035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45442307990759174808750713 34081730993069381106563035)
    ·
      refine ⟨51122596489604071659844553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34081730993069381106563035 51122596489604071659844553)
      ·
        refine ⟨38341947367203053744883415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 51122596489604071659844553 38341947367203053744883415)
        ·
          refine ⟨57512921050804580617325123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38341947367203053744883415 57512921050804580617325123)
          ·
            refine ⟨86269381576206870925987685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 57512921050804580617325123 86269381576206870925987685)
            ·
              refine ⟨16175509045538788298622691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 86269381576206870925987685 16175509045538788298622691)
              ·
                refine ⟨24263263568308182447934037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16175509045538788298622691 24263263568308182447934037)
                ·
                  refine ⟨284335119941111513061727, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 24263263568308182447934037 284335119941111513061727)
                  ·
                    rfl

theorem cell23_4983666_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 4, 1, 8].length) (baseStart_4983666 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4983666 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4983666 prefixEnd_4983666 := by exact prefixLift 4983666
  have htrace : WordTrace (prefixWord ++ tailWord_4983666) baseStart_4983666 baseEnd_4983666 := by
    simpa [prefixWord, tailWord_4983666, baseEnd_4983666] using wordTrace_append hprefix tailTrace_4983666
  have hstable : (prefixWord ++ tailWord_4983666).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4983666).length < 2 ^ (prefixWord ++ tailWord_4983666).sum := by decide
  have hdescent : baseEnd_4983666 < baseStart_4983666 := by decide
  rcases family_descends (prefixWord ++ tailWord_4983666) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4983733 : List Nat := [1, 3, 3, 2, 1, 1, 1, 1, 5, 1, 4]
def baseStart_4983733 : Nat := 118140960795 + 4983733 * 2 ^ 59
def prefixEnd_4983733 : Nat := 4983230072969 + 3 ^ 40 * 4983733 * 2
def baseEnd_4983733 : Nat := 2559050482673854855417735

theorem tailTrace_4983733 : CollatzResearch.WordTrace tailWord_4983733 prefixEnd_4983733 2559050482673854855417735 := by
  unfold tailWord_4983733
  simp only [CollatzResearch.WordTrace]
  refine ⟨181771675653793969677691853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121181117102529313118461235 181771675653793969677691853)
  ·
    refine ⟨68164378370172738629134445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 181771675653793969677691853 68164378370172738629134445)
    ·
      refine ⟨25561641888814776985925417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 68164378370172738629134445 25561641888814776985925417)
      ·
        refine ⟨19171231416611082739444063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25561641888814776985925417 19171231416611082739444063)
        ·
          refine ⟨28756847124916624109166095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19171231416611082739444063 28756847124916624109166095)
          ·
            refine ⟨43135270687374936163749143, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28756847124916624109166095 43135270687374936163749143)
            ·
              refine ⟨64702906031062404245623715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 43135270687374936163749143 64702906031062404245623715)
              ·
                refine ⟨97054359046593606368435573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 64702906031062404245623715 97054359046593606368435573)
                ·
                  refine ⟨9098846160618150597040835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 97054359046593606368435573 9098846160618150597040835)
                  ·
                    refine ⟨13648269240927225895561253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9098846160618150597040835 13648269240927225895561253)
                    ·
                      refine ⟨2559050482673854855417735, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13648269240927225895561253 2559050482673854855417735)
                      ·
                        rfl

theorem cell23_4983733_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 1, 1, 5, 1, 4].length) (baseStart_4983733 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4983733 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4983733 prefixEnd_4983733 := by exact prefixLift 4983733
  have htrace : WordTrace (prefixWord ++ tailWord_4983733) baseStart_4983733 baseEnd_4983733 := by
    simpa [prefixWord, tailWord_4983733, baseEnd_4983733] using wordTrace_append hprefix tailTrace_4983733
  have hstable : (prefixWord ++ tailWord_4983733).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4983733).length < 2 ^ (prefixWord ++ tailWord_4983733).sum := by decide
  have hdescent : baseEnd_4983733 < baseStart_4983733 := by decide
  rcases family_descends (prefixWord ++ tailWord_4983733) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4983773 : List Nat := [1, 4, 3, 1, 2, 2, 10]
def baseStart_4983773 : Nat := 118140960795 + 4983773 * 2 ^ 59
def prefixEnd_4983773 : Nat := 4983230072969 + 3 ^ 40 * 4983773 * 2
def baseEnd_4983773 : Nat := 31593469406173267887871

theorem tailTrace_4983773 : CollatzResearch.WordTrace tailWord_4983773 prefixEnd_4983773 31593469406173267887871 := by
  unfold tailWord_4983773
  simp only [CollatzResearch.WordTrace]
  refine ⟨181773134573649056509147973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121182089715766037672765315 181773134573649056509147973)
  ·
    refine ⟨34082462732559198095465245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 181773134573649056509147973 34082462732559198095465245)
    ·
      refine ⟨12780923524709699285799467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 34082462732559198095465245 12780923524709699285799467)
      ·
        refine ⟨19171385287064548928699201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12780923524709699285799467 19171385287064548928699201)
        ·
          refine ⟨14378538965298411696524401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19171385287064548928699201 14378538965298411696524401)
          ·
            refine ⟨10783904223973808772393301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14378538965298411696524401 10783904223973808772393301)
            ·
              refine ⟨31593469406173267887871, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 10783904223973808772393301 31593469406173267887871)
              ·
                rfl

theorem cell23_4983773_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 2, 10].length) (baseStart_4983773 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4983773 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4983773 prefixEnd_4983773 := by exact prefixLift 4983773
  have htrace : WordTrace (prefixWord ++ tailWord_4983773) baseStart_4983773 baseEnd_4983773 := by
    simpa [prefixWord, tailWord_4983773, baseEnd_4983773] using wordTrace_append hprefix tailTrace_4983773
  have hstable : (prefixWord ++ tailWord_4983773).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4983773).length < 2 ^ (prefixWord ++ tailWord_4983773).sum := by decide
  have hdescent : baseEnd_4983773 < baseStart_4983773 := by decide
  rcases family_descends (prefixWord ++ tailWord_4983773) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4983776 : List Nat := [2, 1, 1, 3, 1, 1, 1, 1, 4, 2, 6]
def baseStart_4983776 : Nat := 118140960795 + 4983776 * 2 ^ 59
def prefixEnd_4983776 : Nat := 4983230072969 + 3 ^ 40 * 4983776 * 2
def baseEnd_4983776 : Nat := 2559072562341998187180037

theorem tailTrace_4983776 : CollatzResearch.WordTrace tailWord_4983776 prefixEnd_4983776 2559072562341998187180037 := by
  unfold tailWord_4983776
  simp only [CollatzResearch.WordTrace]
  refine ⟨90886621996319094010753591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 121182162661758792014338121 90886621996319094010753591)
  ·
    refine ⟨136329932994478641016130387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90886621996319094010753591 136329932994478641016130387)
    ·
      refine ⟨204494899491717961524195581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 136329932994478641016130387 204494899491717961524195581)
      ·
        refine ⟨76685587309394235571573343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 204494899491717961524195581 76685587309394235571573343)
        ·
          refine ⟨115028380964091353357360015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 76685587309394235571573343 115028380964091353357360015)
          ·
            refine ⟨172542571446137030036040023, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 115028380964091353357360015 172542571446137030036040023)
            ·
              refine ⟨258813857169205545054060035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 172542571446137030036040023 258813857169205545054060035)
              ·
                refine ⟨388220785753808317581090053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 258813857169205545054060035 388220785753808317581090053)
                ·
                  refine ⟨72791397328839059546454385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 388220785753808317581090053 72791397328839059546454385)
                  ·
                    refine ⟨54593547996629294659840789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 72791397328839059546454385 54593547996629294659840789)
                    ·
                      refine ⟨2559072562341998187180037, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 54593547996629294659840789 2559072562341998187180037)
                      ·
                        rfl

theorem cell23_4983776_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 1, 1, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 1, 1, 4, 2, 6].length) (baseStart_4983776 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4983776 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4983776 prefixEnd_4983776 := by exact prefixLift 4983776
  have htrace : WordTrace (prefixWord ++ tailWord_4983776) baseStart_4983776 baseEnd_4983776 := by
    simpa [prefixWord, tailWord_4983776, baseEnd_4983776] using wordTrace_append hprefix tailTrace_4983776
  have hstable : (prefixWord ++ tailWord_4983776).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4983776).length < 2 ^ (prefixWord ++ tailWord_4983776).sum := by decide
  have hdescent : baseEnd_4983776 < baseStart_4983776 := by decide
  rcases family_descends (prefixWord ++ tailWord_4983776) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4983784 : List Nat := [2, 1, 4, 1, 1, 1, 4, 4, 1, 2, 2]
def baseStart_4983784 : Nat := 118140960795 + 4983784 * 2 ^ 59
def prefixEnd_4983784 : Nat := 4983230072969 + 3 ^ 40 * 4983784 * 2
def baseEnd_4983784 : Nat := 2559076670187234155880001

theorem tailTrace_4983784 : CollatzResearch.WordTrace tailWord_4983784 prefixEnd_4983784 2559076670187234155880001 := by
  unfold tailWord_4983784
  simp only [CollatzResearch.WordTrace]
  refine ⟨90886767888304602693899203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 121182357184406136925198937 90886767888304602693899203)
  ·
    refine ⟨136330151832456904040848805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90886767888304602693899203 136330151832456904040848805)
    ·
      refine ⟨25561903468585669507659151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 136330151832456904040848805 25561903468585669507659151)
      ·
        refine ⟨38342855202878504261488727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25561903468585669507659151 38342855202878504261488727)
        ·
          refine ⟨57514282804317756392233091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38342855202878504261488727 57514282804317756392233091)
          ·
            refine ⟨86271424206476634588349637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 57514282804317756392233091 86271424206476634588349637)
            ·
              refine ⟨16175892038714368985315557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 86271424206476634588349637 16175892038714368985315557)
              ·
                refine ⟨3032979757258944184746667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 16175892038714368985315557 3032979757258944184746667)
                ·
                  refine ⟨4549469635888416277120001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3032979757258944184746667 4549469635888416277120001)
                  ·
                    refine ⟨3412102226916312207840001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4549469635888416277120001 3412102226916312207840001)
                    ·
                      refine ⟨2559076670187234155880001, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3412102226916312207840001 2559076670187234155880001)
                      ·
                        rfl

theorem cell23_4983784_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 4, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 4, 4, 1, 2, 2].length) (baseStart_4983784 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4983784 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4983784 prefixEnd_4983784 := by exact prefixLift 4983784
  have htrace : WordTrace (prefixWord ++ tailWord_4983784) baseStart_4983784 baseEnd_4983784 := by
    simpa [prefixWord, tailWord_4983784, baseEnd_4983784] using wordTrace_append hprefix tailTrace_4983784
  have hstable : (prefixWord ++ tailWord_4983784).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4983784).length < 2 ^ (prefixWord ++ tailWord_4983784).sum := by decide
  have hdescent : baseEnd_4983784 < baseStart_4983784 := by decide
  rcases family_descends (prefixWord ++ tailWord_4983784) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4983794 : List Nat := [3, 2, 1, 5, 2, 1, 1, 1, 1, 6]
def baseStart_4983794 : Nat := 118140960795 + 4983794 * 2 ^ 59
def prefixEnd_4983794 : Nat := 4983230072969 + 3 ^ 40 * 4983794 * 2
def baseEnd_4983794 : Nat := 853027268331259705584985

theorem tailTrace_4983794 : CollatzResearch.WordTrace tailWord_4983794 prefixEnd_4983794 853027268331259705584985 := by
  unfold tailWord_4983794
  simp only [CollatzResearch.WordTrace]
  refine ⟨45443475126643244273915609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 121182600337715318063774957 45443475126643244273915609)
  ·
    refine ⟨34082606344982433205436707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45443475126643244273915609 34082606344982433205436707)
    ·
      refine ⟨51123909517473649808155061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34082606344982433205436707 51123909517473649808155061)
      ·
        refine ⟨4792866517263154669514537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 51123909517473649808155061 4792866517263154669514537)
        ·
          refine ⟨3594649887947366002135903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4792866517263154669514537 3594649887947366002135903)
          ·
            refine ⟨5391974831921049003203855, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3594649887947366002135903 5391974831921049003203855)
            ·
              refine ⟨8087962247881573504805783, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5391974831921049003203855 8087962247881573504805783)
              ·
                refine ⟨12131943371822360257208675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8087962247881573504805783 12131943371822360257208675)
                ·
                  refine ⟨18197915057733540385813013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12131943371822360257208675 18197915057733540385813013)
                  ·
                    refine ⟨853027268331259705584985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 18197915057733540385813013 853027268331259705584985)
                    ·
                      rfl

theorem cell23_4983794_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 5, 2, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 5, 2, 1, 1, 1, 1, 6].length) (baseStart_4983794 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4983794 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4983794 prefixEnd_4983794 := by exact prefixLift 4983794
  have htrace : WordTrace (prefixWord ++ tailWord_4983794) baseStart_4983794 baseEnd_4983794 := by
    simpa [prefixWord, tailWord_4983794, baseEnd_4983794] using wordTrace_append hprefix tailTrace_4983794
  have hstable : (prefixWord ++ tailWord_4983794).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4983794).length < 2 ^ (prefixWord ++ tailWord_4983794).sum := by decide
  have hdescent : baseEnd_4983794 < baseStart_4983794 := by decide
  rcases family_descends (prefixWord ++ tailWord_4983794) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4983797 : List Nat := [1, 3, 5, 2, 1, 1, 1, 1, 1, 1, 6]
def baseStart_4983797 : Nat := 118140960795 + 4983797 * 2 ^ 59
def prefixEnd_4983797 : Nat := 4983230072969 + 3 ^ 40 * 4983797 * 2
def baseEnd_4983797 : Nat := 2559083345435742605017441

theorem tailTrace_4983797 : CollatzResearch.WordTrace tailWord_4983797 prefixEnd_4983797 2559083345435742605017441 := by
  unfold tailWord_4983797
  simp only [CollatzResearch.WordTrace]
  refine ⟨181774009925562108608021645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121182673283708072405347763 181774009925562108608021645)
  ·
    refine ⟨68165253722085790728008117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 181774009925562108608021645 68165253722085790728008117)
    ·
      refine ⟨6390492536445542880750761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 68165253722085790728008117 6390492536445542880750761)
      ·
        refine ⟨4792869402334157160563071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6390492536445542880750761 4792869402334157160563071)
        ·
          refine ⟨7189304103501235740844607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4792869402334157160563071 7189304103501235740844607)
          ·
            refine ⟨10783956155251853611266911, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7189304103501235740844607 10783956155251853611266911)
            ·
              refine ⟨16175934232877780416900367, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10783956155251853611266911 16175934232877780416900367)
              ·
                refine ⟨24263901349316670625350551, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16175934232877780416900367 24263901349316670625350551)
                ·
                  refine ⟨36395852023975005938025827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24263901349316670625350551 36395852023975005938025827)
                  ·
                    refine ⟨54593778035962508907038741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 36395852023975005938025827 54593778035962508907038741)
                    ·
                      refine ⟨2559083345435742605017441, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 54593778035962508907038741 2559083345435742605017441)
                      ·
                        rfl

theorem cell23_4983797_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 2, 1, 1, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 2, 1, 1, 1, 1, 1, 1, 6].length) (baseStart_4983797 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4983797 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4983797 prefixEnd_4983797 := by exact prefixLift 4983797
  have htrace : WordTrace (prefixWord ++ tailWord_4983797) baseStart_4983797 baseEnd_4983797 := by
    simpa [prefixWord, tailWord_4983797, baseEnd_4983797] using wordTrace_append hprefix tailTrace_4983797
  have hstable : (prefixWord ++ tailWord_4983797).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4983797).length < 2 ^ (prefixWord ++ tailWord_4983797).sum := by decide
  have hdescent : baseEnd_4983797 < baseStart_4983797 := by decide
  rcases family_descends (prefixWord ++ tailWord_4983797) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4983878 : List Nat := [6, 1, 1, 1, 1, 3, 3, 1, 1, 3, 2]
def baseStart_4983878 : Nat := 118140960795 + 4983878 * 2 ^ 59
def prefixEnd_4983878 : Nat := 4983230072969 + 3 ^ 40 * 4983878 * 2
def baseEnd_4983878 : Nat := 2559124937368756788104569

theorem tailTrace_4983878 : CollatzResearch.WordTrace tailWord_4983878 prefixEnd_4983878 2559124937368756788104569 := by
  unfold tailWord_4983878
  simp only [CollatzResearch.WordTrace]
  refine ⟨5680530132445895607553759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 121184642825512439627813525 5680530132445895607553759)
  ·
    refine ⟨8520795198668843411330639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5680530132445895607553759 8520795198668843411330639)
    ·
      refine ⟨12781192798003265116995959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8520795198668843411330639 12781192798003265116995959)
      ·
        refine ⟨19171789197004897675493939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12781192798003265116995959 19171789197004897675493939)
        ·
          refine ⟨28757683795507346513240909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19171789197004897675493939 28757683795507346513240909)
          ·
            refine ⟨10784131423315254942465341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 28757683795507346513240909 10784131423315254942465341)
            ·
              refine ⟨4044049283743220603424503, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10784131423315254942465341 4044049283743220603424503)
              ·
                refine ⟨6066073925614830905136755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4044049283743220603424503 6066073925614830905136755)
                ·
                  refine ⟨9099110888422246357705133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6066073925614830905136755 9099110888422246357705133)
                  ·
                    refine ⟨3412166583158342384139425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9099110888422246357705133 3412166583158342384139425)
                    ·
                      refine ⟨2559124937368756788104569, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3412166583158342384139425 2559124937368756788104569)
                      ·
                        rfl

theorem cell23_4983878_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 3, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 3, 3, 1, 1, 3, 2].length) (baseStart_4983878 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4983878 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4983878 prefixEnd_4983878 := by exact prefixLift 4983878
  have htrace : WordTrace (prefixWord ++ tailWord_4983878) baseStart_4983878 baseEnd_4983878 := by
    simpa [prefixWord, tailWord_4983878, baseEnd_4983878] using wordTrace_append hprefix tailTrace_4983878
  have hstable : (prefixWord ++ tailWord_4983878).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4983878).length < 2 ^ (prefixWord ++ tailWord_4983878).sum := by decide
  have hdescent : baseEnd_4983878 < baseStart_4983878 := by decide
  rcases family_descends (prefixWord ++ tailWord_4983878) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4983880 : List Nat := [2, 1, 3, 1, 1, 1, 4, 5, 5]
def baseStart_4983880 : Nat := 118140960795 + 4983880 * 2 ^ 59
def prefixEnd_4983880 : Nat := 4983230072969 + 3 ^ 40 * 4983880 * 2
def baseEnd_4983880 : Nat := 284347329370007308919951

theorem tailTrace_4983880 : CollatzResearch.WordTrace tailWord_4983880 prefixEnd_4983880 284347329370007308919951 := by
  unfold tailWord_4983880
  simp only [CollatzResearch.WordTrace]
  refine ⟨90888518592130706891646547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 121184691456174275855528729 90888518592130706891646547)
  ·
    refine ⟨136332777888196060337469821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90888518592130706891646547 136332777888196060337469821)
    ·
      refine ⟨51124791708073522626551183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 136332777888196060337469821 51124791708073522626551183)
      ·
        refine ⟨76687187562110283939826775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51124791708073522626551183 76687187562110283939826775)
        ·
          refine ⟨115030781343165425909740163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 76687187562110283939826775 115030781343165425909740163)
          ·
            refine ⟨172546172014748138864610245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 115030781343165425909740163 172546172014748138864610245)
            ·
              refine ⟨32352407252765276037114421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 172546172014748138864610245 32352407252765276037114421)
              ·
                refine ⟨3033038179946744628479477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 32352407252765276037114421 3033038179946744628479477)
                ·
                  refine ⟨284347329370007308919951, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3033038179946744628479477 284347329370007308919951)
                  ·
                    rfl

theorem cell23_4983880_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 4, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 4, 5, 5].length) (baseStart_4983880 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4983880 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4983880 prefixEnd_4983880 := by exact prefixLift 4983880
  have htrace : WordTrace (prefixWord ++ tailWord_4983880) baseStart_4983880 baseEnd_4983880 := by
    simpa [prefixWord, tailWord_4983880, baseEnd_4983880] using wordTrace_append hprefix tailTrace_4983880
  have hstable : (prefixWord ++ tailWord_4983880).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4983880).length < 2 ^ (prefixWord ++ tailWord_4983880).sum := by decide
  have hdescent : baseEnd_4983880 < baseStart_4983880 := by decide
  rcases family_descends (prefixWord ++ tailWord_4983880) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4983903 : List Nat := [1, 1, 2, 3, 1, 1, 3, 3, 1, 2, 5]
def baseStart_4983903 : Nat := 118140960795 + 4983903 * 2 ^ 59
def prefixEnd_4983903 : Nat := 4983230072969 + 3 ^ 40 * 4983903 * 2
def baseEnd_4983903 : Nat := 2559137774385119190291953

theorem tailTrace_4983903 : CollatzResearch.WordTrace tailWord_4983903 prefixEnd_4983903 2559137774385119190291953 := by
  unfold tailWord_4983903
  simp only [CollatzResearch.WordTrace]
  refine ⟨181777876063178088711380363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121185250708785392474253575 181777876063178088711380363)
  ·
    refine ⟨272666814094767133067070545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 181777876063178088711380363 272666814094767133067070545)
    ·
      refine ⟨204500110571075349800302909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 272666814094767133067070545 204500110571075349800302909)
      ·
        refine ⟨76687541464153256175113591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 204500110571075349800302909 76687541464153256175113591)
        ·
          refine ⟨115031312196229884262670387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 76687541464153256175113591 115031312196229884262670387)
          ·
            refine ⟨172546968294344826394005581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 115031312196229884262670387 172546968294344826394005581)
            ·
              refine ⟨64705113110379309897752093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 172546968294344826394005581 64705113110379309897752093)
              ·
                refine ⟨24264417416392241211657035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 64705113110379309897752093 24264417416392241211657035)
                ·
                  refine ⟨36396626124588361817485553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24264417416392241211657035 36396626124588361817485553)
                  ·
                    refine ⟨27297469593441271363114165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 36396626124588361817485553 27297469593441271363114165)
                    ·
                      refine ⟨2559137774385119190291953, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 27297469593441271363114165 2559137774385119190291953)
                      ·
                        rfl

theorem cell23_4983903_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 3, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 3, 3, 1, 2, 5].length) (baseStart_4983903 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4983903 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4983903 prefixEnd_4983903 := by exact prefixLift 4983903
  have htrace : WordTrace (prefixWord ++ tailWord_4983903) baseStart_4983903 baseEnd_4983903 := by
    simpa [prefixWord, tailWord_4983903, baseEnd_4983903] using wordTrace_append hprefix tailTrace_4983903
  have hstable : (prefixWord ++ tailWord_4983903).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4983903).length < 2 ^ (prefixWord ++ tailWord_4983903).sum := by decide
  have hdescent : baseEnd_4983903 < baseStart_4983903 := by decide
  rcases family_descends (prefixWord ++ tailWord_4983903) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4983997 : List Nat := [1, 4, 1, 2, 1, 1, 2, 2, 5, 1, 3]
def baseStart_4983997 : Nat := 118140960795 + 4983997 * 2 ^ 59
def prefixEnd_4983997 : Nat := 4983230072969 + 3 ^ 40 * 4983997 * 2
def baseEnd_4983997 : Nat := 2559186041566641822516521

theorem tailTrace_4983997 : CollatzResearch.WordTrace tailWord_4983997 prefixEnd_4983997 2559186041566641822516521 := by
  unfold tailWord_4983997
  simp only [CollatzResearch.WordTrace]
  refine ⟨181781304524837542765302245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121187536349891695176868163 181781304524837542765302245)
  ·
    refine ⟨34083994598407039268494171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 181781304524837542765302245 34083994598407039268494171)
    ·
      refine ⟨51125991897610558902741257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34083994598407039268494171 51125991897610558902741257)
      ·
        refine ⟨38344493923207919177055943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 51125991897610558902741257 38344493923207919177055943)
        ·
          refine ⟨57516740884811878765583915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38344493923207919177055943 57516740884811878765583915)
          ·
            refine ⟨86275111327217818148375873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 57516740884811878765583915 86275111327217818148375873)
            ·
              refine ⟨64706333495413363611281905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 86275111327217818148375873 64706333495413363611281905)
              ·
                refine ⟨48529750121560022708461429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 64706333495413363611281905 48529750121560022708461429)
                ·
                  refine ⟨4549664073896252128918259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 48529750121560022708461429 4549664073896252128918259)
                  ·
                    refine ⟨6824496110844378193377389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4549664073896252128918259 6824496110844378193377389)
                    ·
                      refine ⟨2559186041566641822516521, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6824496110844378193377389 2559186041566641822516521)
                      ·
                        rfl

theorem cell23_4983997_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 2, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 2, 2, 5, 1, 3].length) (baseStart_4983997 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4983997 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4983997 prefixEnd_4983997 := by exact prefixLift 4983997
  have htrace : WordTrace (prefixWord ++ tailWord_4983997) baseStart_4983997 baseEnd_4983997 := by
    simpa [prefixWord, tailWord_4983997, baseEnd_4983997] using wordTrace_append hprefix tailTrace_4983997
  have hstable : (prefixWord ++ tailWord_4983997).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4983997).length < 2 ^ (prefixWord ++ tailWord_4983997).sum := by decide
  have hdescent : baseEnd_4983997 < baseStart_4983997 := by decide
  rcases family_descends (prefixWord ++ tailWord_4983997) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4984047 : List Nat := [1, 1, 2, 1, 7, 1, 1, 2, 1, 6]
def baseStart_4984047 : Nat := 118140960795 + 4984047 * 2 ^ 59
def prefixEnd_4984047 : Nat := 4983230072969 + 3 ^ 40 * 4984047 * 2
def baseEnd_4984047 : Nat := 853070571866455542297097

theorem tailTrace_4984047 : CollatzResearch.WordTrace tailWord_4984047 prefixEnd_4984047 853070571866455542297097 := by
  unfold tailWord_4984047
  simp only [CollatzResearch.WordTrace]
  refine ⟨181783128174656401304622395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121188752116437600869748263 181783128174656401304622395)
  ·
    refine ⟨272674692261984601956933593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 181783128174656401304622395 272674692261984601956933593)
    ·
      refine ⟨204506019196488451467700195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 272674692261984601956933593 204506019196488451467700195)
      ·
        refine ⟨306759028794732677201550293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 204506019196488451467700195 306759028794732677201550293)
        ·
          refine ⟨7189664737376547121911335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 306759028794732677201550293 7189664737376547121911335)
          ·
            refine ⟨10784497106064820682867003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7189664737376547121911335 10784497106064820682867003)
            ·
              refine ⟨16176745659097231024300505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10784497106064820682867003 16176745659097231024300505)
              ·
                refine ⟨12132559244322923268225379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16176745659097231024300505 12132559244322923268225379)
                ·
                  refine ⟨18198838866484384902338069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12132559244322923268225379 18198838866484384902338069)
                  ·
                    refine ⟨853070571866455542297097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 18198838866484384902338069 853070571866455542297097)
                    ·
                      rfl

theorem cell23_4984047_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 7, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 7, 1, 1, 2, 1, 6].length) (baseStart_4984047 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4984047 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4984047 prefixEnd_4984047 := by exact prefixLift 4984047
  have htrace : WordTrace (prefixWord ++ tailWord_4984047) baseStart_4984047 baseEnd_4984047 := by
    simpa [prefixWord, tailWord_4984047, baseEnd_4984047] using wordTrace_append hprefix tailTrace_4984047
  have hstable : (prefixWord ++ tailWord_4984047).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4984047).length < 2 ^ (prefixWord ++ tailWord_4984047).sum := by decide
  have hdescent : baseEnd_4984047 < baseStart_4984047 := by decide
  rcases family_descends (prefixWord ++ tailWord_4984047) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4984060 : List Nat := [2, 2, 2, 1, 5, 11]
def baseStart_4984060 : Nat := 118140960795 + 4984060 * 2 ^ 59
def prefixEnd_4984060 : Nat := 4983230072969 + 3 ^ 40 * 4984060 * 2
def baseEnd_4984060 : Nat := 10531762925299897432217

theorem tailTrace_4984060 : CollatzResearch.WordTrace tailWord_4984060 prefixEnd_4984060 10531762925299897432217 := by
  unfold tailWord_4984060
  simp only [CollatzResearch.WordTrace]
  refine ⟨90891801161804652262422817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 121189068215739536349897089 90891801161804652262422817)
  ·
    refine ⟨68168850871353489196817113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 90891801161804652262422817 68168850871353489196817113)
    ·
      refine ⟨51126638153515116897612835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 68168850871353489196817113 51126638153515116897612835)
      ·
        refine ⟨76689957230272675346419253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51126638153515116897612835 76689957230272675346419253)
        ·
          refine ⟨7189683490338063313726805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 76689957230272675346419253 7189683490338063313726805)
          ·
            refine ⟨10531762925299897432217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 7189683490338063313726805 10531762925299897432217)
            ·
              rfl

theorem cell23_4984060_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 5, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 5, 11].length) (baseStart_4984060 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4984060 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4984060 prefixEnd_4984060 := by exact prefixLift 4984060
  have htrace : WordTrace (prefixWord ++ tailWord_4984060) baseStart_4984060 baseEnd_4984060 := by
    simpa [prefixWord, tailWord_4984060, baseEnd_4984060] using wordTrace_append hprefix tailTrace_4984060
  have hstable : (prefixWord ++ tailWord_4984060).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4984060).length < 2 ^ (prefixWord ++ tailWord_4984060).sum := by decide
  have hdescent : baseEnd_4984060 < baseStart_4984060 := by decide
  rcases family_descends (prefixWord ++ tailWord_4984060) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4984104 : List Nat := [2, 1, 5, 1, 2, 1, 2, 2, 1, 3, 3]
def baseStart_4984104 : Nat := 118140960795 + 4984104 * 2 ^ 59
def prefixEnd_4984104 : Nat := 4983230072969 + 3 ^ 40 * 4984104 * 2
def baseEnd_4984104 : Nat := 2559240983996672903878529

theorem tailTrace_4984104 : CollatzResearch.WordTrace tailWord_4984104 prefixEnd_4984104 2559240983996672903878529 := by
  unfold tailWord_4984104
  simp only [CollatzResearch.WordTrace]
  refine ⟨90892603567724950019723683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 121190138090299933359631577 90892603567724950019723683)
  ·
    refine ⟨136338905351587425029585525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90892603567724950019723683 136338905351587425029585525)
    ·
      refine ⟨12781772376711321096523643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 136338905351587425029585525 12781772376711321096523643)
      ·
        refine ⟨19172658565066981644785465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12781772376711321096523643 19172658565066981644785465)
        ·
          refine ⟨14379493923800236233589099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19172658565066981644785465 14379493923800236233589099)
          ·
            refine ⟨21569240885700354350383649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14379493923800236233589099 21569240885700354350383649)
            ·
              refine ⟨16176930664275265762787737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21569240885700354350383649 16176930664275265762787737)
              ·
                refine ⟨12132697998206449322090803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16176930664275265762787737 12132697998206449322090803)
                ·
                  refine ⟨18199046997309673983136205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12132697998206449322090803 18199046997309673983136205)
                  ·
                    refine ⟨6824642623991127743676077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 18199046997309673983136205 6824642623991127743676077)
                    ·
                      refine ⟨2559240983996672903878529, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6824642623991127743676077 2559240983996672903878529)
                      ·
                        rfl

theorem cell23_4984104_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 1, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 1, 2, 2, 1, 3, 3].length) (baseStart_4984104 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4984104 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4984104 prefixEnd_4984104 := by exact prefixLift 4984104
  have htrace : WordTrace (prefixWord ++ tailWord_4984104) baseStart_4984104 baseEnd_4984104 := by
    simpa [prefixWord, tailWord_4984104, baseEnd_4984104] using wordTrace_append hprefix tailTrace_4984104
  have hstable : (prefixWord ++ tailWord_4984104).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4984104).length < 2 ^ (prefixWord ++ tailWord_4984104).sum := by decide
  have hdescent : baseEnd_4984104 < baseStart_4984104 := by decide
  rcases family_descends (prefixWord ++ tailWord_4984104) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4984121 : List Nat := [1, 2, 1, 6, 2, 1, 1, 1, 4, 1, 3]
def baseStart_4984121 : Nat := 118140960795 + 4984121 * 2 ^ 59
def prefixEnd_4984121 : Nat := 4983230072969 + 3 ^ 40 * 4984121 * 2
def baseEnd_4984121 : Nat := 2559249713167799337365951

theorem tailTrace_4984121 : CollatzResearch.WordTrace tailWord_4984121 prefixEnd_4984121 2559249713167799337365951 := by
  unfold tailWord_4984121
  simp only [CollatzResearch.WordTrace]
  refine ⟨181785827176388311942816217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121190551450925541295210811 181785827176388311942816217)
  ·
    refine ⟨136339370382291233957112163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 181785827176388311942816217 136339370382291233957112163)
    ·
      refine ⟨204509055573436850935668245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 136339370382291233957112163 204509055573436850935668245)
      ·
        refine ⟨9586361980004852387609449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 204509055573436850935668245 9586361980004852387609449)
        ·
          refine ⟨7189771485003639290707087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9586361980004852387609449 7189771485003639290707087)
          ·
            refine ⟨10784657227505458936060631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7189771485003639290707087 10784657227505458936060631)
            ·
              refine ⟨16176985841258188404090947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10784657227505458936060631 16176985841258188404090947)
              ·
                refine ⟨24265478761887282606136421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16176985841258188404090947 24265478761887282606136421)
                ·
                  refine ⟨4549777267853865488650579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 24265478761887282606136421 4549777267853865488650579)
                  ·
                    refine ⟨6824665901780798232975869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4549777267853865488650579 6824665901780798232975869)
                    ·
                      refine ⟨2559249713167799337365951, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6824665901780798232975869 2559249713167799337365951)
                      ·
                        rfl

theorem cell23_4984121_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 2, 1, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 2, 1, 1, 1, 4, 1, 3].length) (baseStart_4984121 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4984121 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4984121 prefixEnd_4984121 := by exact prefixLift 4984121
  have htrace : WordTrace (prefixWord ++ tailWord_4984121) baseStart_4984121 baseEnd_4984121 := by
    simpa [prefixWord, tailWord_4984121, baseEnd_4984121] using wordTrace_append hprefix tailTrace_4984121
  have hstable : (prefixWord ++ tailWord_4984121).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4984121).length < 2 ^ (prefixWord ++ tailWord_4984121).sum := by decide
  have hdescent : baseEnd_4984121 < baseStart_4984121 := by decide
  rcases family_descends (prefixWord ++ tailWord_4984121) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4984177 : List Nat := [1, 2, 2, 2, 1, 2, 2, 1, 4, 3, 3]
def baseStart_4984177 : Nat := 118140960795 + 4984177 * 2 ^ 59
def prefixEnd_4984177 : Nat := 4983230072969 + 3 ^ 40 * 4984177 * 2
def baseEnd_4984177 : Nat := 2559278468084451118265693

theorem tailTrace_4984177 : CollatzResearch.WordTrace tailWord_4984177 prefixEnd_4984177 2559278468084451118265693 := by
  unfold tailWord_4984177
  simp only [CollatzResearch.WordTrace]
  refine ⟨181787869664185433506854785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121191913109456955671236523 181787869664185433506854785)
  ·
    refine ⟨136340902248139075130141089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 181787869664185433506854785 136340902248139075130141089)
    ·
      refine ⟨102255676686104306347605817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 136340902248139075130141089 102255676686104306347605817)
      ·
        refine ⟨76691757514578229760704363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 102255676686104306347605817 76691757514578229760704363)
        ·
          refine ⟨115037636271867344641056545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 76691757514578229760704363 115037636271867344641056545)
          ·
            refine ⟨86278227203900508480792409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 115037636271867344641056545 86278227203900508480792409)
            ·
              refine ⟨64708670402925381360594307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 86278227203900508480792409 64708670402925381360594307)
              ·
                refine ⟨97063005604388072040891461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 64708670402925381360594307 97063005604388072040891461)
                ·
                  refine ⟨18199313550822763507667149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 97063005604388072040891461 18199313550822763507667149)
                  ·
                    refine ⟨6824742581558536315375181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 18199313550822763507667149 6824742581558536315375181)
                    ·
                      refine ⟨2559278468084451118265693, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6824742581558536315375181 2559278468084451118265693)
                      ·
                        rfl

theorem cell23_4984177_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 2, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 2, 1, 4, 3, 3].length) (baseStart_4984177 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4984177 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4984177 prefixEnd_4984177 := by exact prefixLift 4984177
  have htrace : WordTrace (prefixWord ++ tailWord_4984177) baseStart_4984177 baseEnd_4984177 := by
    simpa [prefixWord, tailWord_4984177, baseEnd_4984177] using wordTrace_append hprefix tailTrace_4984177
  have hstable : (prefixWord ++ tailWord_4984177).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4984177).length < 2 ^ (prefixWord ++ tailWord_4984177).sum := by decide
  have hdescent : baseEnd_4984177 < baseStart_4984177 := by decide
  rcases family_descends (prefixWord ++ tailWord_4984177) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4984195 : List Nat := [1, 1, 1, 3, 5, 3, 2, 1, 2, 2, 2]
def baseStart_4984195 : Nat := 118140960795 + 4984195 * 2 ^ 59
def prefixEnd_4984195 : Nat := 4983230072969 + 3 ^ 40 * 4984195 * 2
def baseEnd_4984195 : Nat := 2559287710736232047840611

theorem tailTrace_4984195 : CollatzResearch.WordTrace tailWord_4984195 prefixEnd_4984195 2559287710736232047840611 := by
  unfold tailWord_4984195
  simp only [CollatzResearch.WordTrace]
  refine ⟨181788526178120222581010039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121192350785413481720673359 181788526178120222581010039)
  ·
    refine ⟨272682789267180333871515059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 181788526178120222581010039 272682789267180333871515059)
    ·
      refine ⟨409024183900770500807272589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 272682789267180333871515059 409024183900770500807272589)
      ·
        refine ⟨153384068962788937802727221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 409024183900770500807272589 153384068962788937802727221)
        ·
          refine ⟨14379756465261462919005677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 153384068962788937802727221 14379756465261462919005677)
          ·
            refine ⟨5392408674473048594627129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14379756465261462919005677 5392408674473048594627129)
            ·
              refine ⟨4044306505854786445970347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5392408674473048594627129 4044306505854786445970347)
              ·
                refine ⟨6066459758782179668955521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4044306505854786445970347 6066459758782179668955521)
                ·
                  refine ⟨4549844819086634751716641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6066459758782179668955521 4549844819086634751716641)
                  ·
                    refine ⟨3412383614314976063787481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4549844819086634751716641 3412383614314976063787481)
                    ·
                      refine ⟨2559287710736232047840611, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3412383614314976063787481 2559287710736232047840611)
                      ·
                        rfl

theorem cell23_4984195_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 3, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 3, 2, 1, 2, 2, 2].length) (baseStart_4984195 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4984195 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4984195 prefixEnd_4984195 := by exact prefixLift 4984195
  have htrace : WordTrace (prefixWord ++ tailWord_4984195) baseStart_4984195 baseEnd_4984195 := by
    simpa [prefixWord, tailWord_4984195, baseEnd_4984195] using wordTrace_append hprefix tailTrace_4984195
  have hstable : (prefixWord ++ tailWord_4984195).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4984195).length < 2 ^ (prefixWord ++ tailWord_4984195).sum := by decide
  have hdescent : baseEnd_4984195 < baseStart_4984195 := by decide
  rcases family_descends (prefixWord ++ tailWord_4984195) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4984254 : List Nat := [4, 2, 1, 1, 1, 1, 1, 4, 1, 4, 3]
def baseStart_4984254 : Nat := 118140960795 + 4984254 * 2 ^ 59
def prefixEnd_4984254 : Nat := 4983230072969 + 3 ^ 40 * 4984254 * 2
def baseEnd_4984254 : Nat := 2559318006094847317002839

theorem tailTrace_4984254 : CollatzResearch.WordTrace tailWord_4984254 prefixEnd_4984254 2559318006094847317002839 := by
  unfold tailWord_4984254
  simp only [CollatzResearch.WordTrace]
  refine ⟨22723834760613309457175977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 121193785389937650438271877 22723834760613309457175977)
  ·
    refine ⟨17042876070459982092881983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22723834760613309457175977 17042876070459982092881983)
    ·
      refine ⟨25564314105689973139322975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17042876070459982092881983 25564314105689973139322975)
      ·
        refine ⟨38346471158534959708984463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25564314105689973139322975 38346471158534959708984463)
        ·
          refine ⟨57519706737802439563476695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38346471158534959708984463 57519706737802439563476695)
          ·
            refine ⟨86279560106703659345215043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 57519706737802439563476695 86279560106703659345215043)
            ·
              refine ⟨129419340160055489017822565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 86279560106703659345215043 129419340160055489017822565)
              ·
                refine ⟨24266126280010404190841731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 129419340160055489017822565 24266126280010404190841731)
                ·
                  refine ⟨36399189420015606286262597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24266126280010404190841731 36399189420015606286262597)
                  ·
                    refine ⟨6824848016252926178674237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 36399189420015606286262597 6824848016252926178674237)
                    ·
                      refine ⟨2559318006094847317002839, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6824848016252926178674237 2559318006094847317002839)
                      ·
                        rfl

theorem cell23_4984254_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 1, 4, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 1, 4, 1, 4, 3].length) (baseStart_4984254 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4984254 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4984254 prefixEnd_4984254 := by exact prefixLift 4984254
  have htrace : WordTrace (prefixWord ++ tailWord_4984254) baseStart_4984254 baseEnd_4984254 := by
    simpa [prefixWord, tailWord_4984254, baseEnd_4984254] using wordTrace_append hprefix tailTrace_4984254
  have hstable : (prefixWord ++ tailWord_4984254).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4984254).length < 2 ^ (prefixWord ++ tailWord_4984254).sum := by decide
  have hdescent : baseEnd_4984254 < baseStart_4984254 := by decide
  rcases family_descends (prefixWord ++ tailWord_4984254) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4984291 : List Nat := [1, 1, 1, 6, 2, 3, 1, 2, 6]
def baseStart_4984291 : Nat := 118140960795 + 4984291 * 2 ^ 59
def prefixEnd_4984291 : Nat := 4983230072969 + 3 ^ 40 * 4984291 * 2
def baseEnd_4984291 : Nat := 284370778319895963582241

theorem tailTrace_4984291 : CollatzResearch.WordTrace tailWord_4984291 prefixEnd_4984291 284370778319895963582241 := by
  unfold tailWord_4984291
  simp only [CollatzResearch.WordTrace]
  refine ⟨181792027585772430976504727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121194685057181620651003151 181792027585772430976504727)
  ·
    refine ⟨272688041378658646464757091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 181792027585772430976504727 272688041378658646464757091)
    ·
      refine ⟨409032062067987969697135637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 272688041378658646464757091 409032062067987969697135637)
      ·
        refine ⟨19173377909436936079553233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 409032062067987969697135637 19173377909436936079553233)
        ·
          refine ⟨14380033432077702059664925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19173377909436936079553233 14380033432077702059664925)
          ·
            refine ⟨5392512537029138272374347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14380033432077702059664925 5392512537029138272374347)
            ·
              refine ⟨8088768805543707408561521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5392512537029138272374347 8088768805543707408561521)
              ·
                refine ⟨6066576604157780556421141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8088768805543707408561521 6066576604157780556421141)
                ·
                  refine ⟨284370778319895963582241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6066576604157780556421141 284370778319895963582241)
                  ·
                    rfl

theorem cell23_4984291_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 3, 1, 2, 6].length) (baseStart_4984291 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4984291 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4984291 prefixEnd_4984291 := by exact prefixLift 4984291
  have htrace : WordTrace (prefixWord ++ tailWord_4984291) baseStart_4984291 baseEnd_4984291 := by
    simpa [prefixWord, tailWord_4984291, baseEnd_4984291] using wordTrace_append hprefix tailTrace_4984291
  have hstable : (prefixWord ++ tailWord_4984291).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4984291).length < 2 ^ (prefixWord ++ tailWord_4984291).sum := by decide
  have hdescent : baseEnd_4984291 < baseStart_4984291 := by decide
  rcases family_descends (prefixWord ++ tailWord_4984291) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4984307 : List Nat := [1, 1, 1, 2, 2, 2, 2, 1, 2, 5, 4]
def baseStart_4984307 : Nat := 118140960795 + 4984307 * 2 ^ 59
def prefixEnd_4984307 : Nat := 4983230072969 + 3 ^ 40 * 4984307 * 2
def baseEnd_4984307 : Nat := 2559345220569535609640095

theorem tailTrace_4984307 : CollatzResearch.WordTrace tailWord_4984307 prefixEnd_4984307 2559345220569535609640095 := by
  unfold tailWord_4984307
  simp only [CollatzResearch.WordTrace]
  refine ⟨181792611153714465709087175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121195074102476310472724783 181792611153714465709087175)
  ·
    refine ⟨272688916730571698563630763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 181792611153714465709087175 272688916730571698563630763)
    ·
      refine ⟨409033375095857547845446145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 272688916730571698563630763 409033375095857547845446145)
      ·
        refine ⟨306775031321893160884084609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 409033375095857547845446145 306775031321893160884084609)
        ·
          refine ⟨230081273491419870663063457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 306775031321893160884084609 230081273491419870663063457)
          ·
            refine ⟨172560955118564902997297593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 230081273491419870663063457 172560955118564902997297593)
            ·
              refine ⟨129420716338923677247973195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 172560955118564902997297593 129420716338923677247973195)
              ·
                refine ⟨194131074508385515871959793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 129420716338923677247973195 194131074508385515871959793)
                ·
                  refine ⟨145598305881289136903969845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 194131074508385515871959793 145598305881289136903969845)
                  ·
                    refine ⟨13649841176370856584747173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 145598305881289136903969845 13649841176370856584747173)
                    ·
                      refine ⟨2559345220569535609640095, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13649841176370856584747173 2559345220569535609640095)
                      ·
                        rfl

theorem cell23_4984307_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 2, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 2, 1, 2, 5, 4].length) (baseStart_4984307 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4984307 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4984307 prefixEnd_4984307 := by exact prefixLift 4984307
  have htrace : WordTrace (prefixWord ++ tailWord_4984307) baseStart_4984307 baseEnd_4984307 := by
    simpa [prefixWord, tailWord_4984307, baseEnd_4984307] using wordTrace_append hprefix tailTrace_4984307
  have hstable : (prefixWord ++ tailWord_4984307).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4984307).length < 2 ^ (prefixWord ++ tailWord_4984307).sum := by decide
  have hdescent : baseEnd_4984307 < baseStart_4984307 := by decide
  rcases family_descends (prefixWord ++ tailWord_4984307) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4984341 : List Nat := [1, 3, 2, 1, 3, 2, 2, 3, 1, 1, 4]
def baseStart_4984341 : Nat := 118140960795 + 4984341 * 2 ^ 59
def prefixEnd_4984341 : Nat := 4983230072969 + 3 ^ 40 * 4984341 * 2
def baseEnd_4984341 : Nat := 2559362678911788476614939

theorem tailTrace_4984341 : CollatzResearch.WordTrace tailWord_4984341 prefixEnd_4984341 2559362678911788476614939 := by
  unfold tailWord_4984341
  simp only [CollatzResearch.WordTrace]
  refine ⟨181793851235591289515824877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121195900823727526343883251 181793851235591289515824877)
  ·
    refine ⟨68172694213346733568434329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 181793851235591289515824877 68172694213346733568434329)
    ·
      refine ⟨51129520660010050176325747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 68172694213346733568434329 51129520660010050176325747)
      ·
        refine ⟨76694280990015075264488621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51129520660010050176325747 76694280990015075264488621)
        ·
          refine ⟨28760355371255653224183233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 76694280990015075264488621 28760355371255653224183233)
          ·
            refine ⟨21570266528441739918137425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28760355371255653224183233 21570266528441739918137425)
            ·
              refine ⟨16177699896331304938603069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21570266528441739918137425 16177699896331304938603069)
              ·
                refine ⟨6066637461124239351976151, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16177699896331304938603069 6066637461124239351976151)
                ·
                  refine ⟨9099956191686359027964227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6066637461124239351976151 9099956191686359027964227)
                  ·
                    refine ⟨13649934287529538541946341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9099956191686359027964227 13649934287529538541946341)
                    ·
                      refine ⟨2559362678911788476614939, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13649934287529538541946341 2559362678911788476614939)
                      ·
                        rfl

theorem cell23_4984341_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 2, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 2, 2, 3, 1, 1, 4].length) (baseStart_4984341 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4984341 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4984341 prefixEnd_4984341 := by exact prefixLift 4984341
  have htrace : WordTrace (prefixWord ++ tailWord_4984341) baseStart_4984341 baseEnd_4984341 := by
    simpa [prefixWord, tailWord_4984341, baseEnd_4984341] using wordTrace_append hprefix tailTrace_4984341
  have hstable : (prefixWord ++ tailWord_4984341).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4984341).length < 2 ^ (prefixWord ++ tailWord_4984341).sum := by decide
  have hdescent : baseEnd_4984341 < baseStart_4984341 := by decide
  rcases family_descends (prefixWord ++ tailWord_4984341) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4984352 : List Nat := [2, 1, 1, 6, 1, 2, 3, 2, 1, 1, 3]
def baseStart_4984352 : Nat := 118140960795 + 4984352 * 2 ^ 59
def prefixEnd_4984352 : Nat := 4983230072969 + 3 ^ 40 * 4984352 * 2
def baseEnd_4984352 : Nat := 2559368327198987933577389

theorem tailTrace_4984352 : CollatzResearch.WordTrace tailWord_4984352 prefixEnd_4984352 2559368327198987933577389 := by
  unfold tailWord_4984352
  simp only [CollatzResearch.WordTrace]
  refine ⟨90897126219275719197237655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 121196168292367625596316873 90897126219275719197237655)
  ·
    refine ⟨136345689328913578795856483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90897126219275719197237655 136345689328913578795856483)
    ·
      refine ⟨204518533993370368193784725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 136345689328913578795856483 204518533993370368193784725)
      ·
        refine ⟨9586806280939236009083659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 204518533993370368193784725 9586806280939236009083659)
        ·
          refine ⟨14380209421408854013625489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9586806280939236009083659 14380209421408854013625489)
          ·
            refine ⟨10785157066056640510219117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14380209421408854013625489 10785157066056640510219117)
            ·
              refine ⟨4044433899771240191332169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10785157066056640510219117 4044433899771240191332169)
              ·
                refine ⟨3033325424828430143499127, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4044433899771240191332169 3033325424828430143499127)
                ·
                  refine ⟨4549988137242645215248691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3033325424828430143499127 4549988137242645215248691)
                  ·
                    refine ⟨6824982205863967822873037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4549988137242645215248691 6824982205863967822873037)
                    ·
                      refine ⟨2559368327198987933577389, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6824982205863967822873037 2559368327198987933577389)
                      ·
                        rfl

theorem cell23_4984352_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 2, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 2, 3, 2, 1, 1, 3].length) (baseStart_4984352 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4984352 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4984352 prefixEnd_4984352 := by exact prefixLift 4984352
  have htrace : WordTrace (prefixWord ++ tailWord_4984352) baseStart_4984352 baseEnd_4984352 := by
    simpa [prefixWord, tailWord_4984352, baseEnd_4984352] using wordTrace_append hprefix tailTrace_4984352
  have hstable : (prefixWord ++ tailWord_4984352).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4984352).length < 2 ^ (prefixWord ++ tailWord_4984352).sum := by decide
  have hdescent : baseEnd_4984352 < baseStart_4984352 := by decide
  rcases family_descends (prefixWord ++ tailWord_4984352) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4984354 : List Nat := [3, 3, 1, 1, 1, 1, 3, 2, 1, 1, 6]
def baseStart_4984354 : Nat := 118140960795 + 4984354 * 2 ^ 59
def prefixEnd_4984354 : Nat := 4983230072969 + 3 ^ 40 * 4984354 * 2
def baseEnd_4984354 : Nat := 2559369354160296925752379

theorem tailTrace_4984354 : CollatzResearch.WordTrace tailWord_4984354 prefixEnd_4984354 2559369354160296925752379 := by
  unfold tailWord_4984354
  simp only [CollatzResearch.WordTrace]
  refine ⟨45448581346136048184012029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 121196216923029461824032077 45448581346136048184012029)
  ·
    refine ⟨17043218004801018069004511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 45448581346136048184012029 17043218004801018069004511)
    ·
      refine ⟨25564827007201527103506767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17043218004801018069004511 25564827007201527103506767)
      ·
        refine ⟨38347240510802290655260151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25564827007201527103506767 38347240510802290655260151)
        ·
          refine ⟨57520860766203435982890227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38347240510802290655260151 57520860766203435982890227)
          ·
            refine ⟨86281291149305153974335341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 57520860766203435982890227 86281291149305153974335341)
            ·
              refine ⟨32355484180989432740375753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 86281291149305153974335341 32355484180989432740375753)
              ·
                refine ⟨24266613135742074555281815, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 32355484180989432740375753 24266613135742074555281815)
                ·
                  refine ⟨36399919703613111832922723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24266613135742074555281815 36399919703613111832922723)
                  ·
                    refine ⟨54599879555419667749384085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 36399919703613111832922723 54599879555419667749384085)
                    ·
                      refine ⟨2559369354160296925752379, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 54599879555419667749384085 2559369354160296925752379)
                      ·
                        rfl

theorem cell23_4984354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 3, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 3, 2, 1, 1, 6].length) (baseStart_4984354 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4984354 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4984354 prefixEnd_4984354 := by exact prefixLift 4984354
  have htrace : WordTrace (prefixWord ++ tailWord_4984354) baseStart_4984354 baseEnd_4984354 := by
    simpa [prefixWord, tailWord_4984354, baseEnd_4984354] using wordTrace_append hprefix tailTrace_4984354
  have hstable : (prefixWord ++ tailWord_4984354).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4984354).length < 2 ^ (prefixWord ++ tailWord_4984354).sum := by decide
  have hdescent : baseEnd_4984354 < baseStart_4984354 := by decide
  rcases family_descends (prefixWord ++ tailWord_4984354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4984444 : List Nat := [2, 2, 2, 1, 1, 2, 1, 1, 3, 4, 4]
def baseStart_4984444 : Nat := 118140960795 + 4984444 * 2 ^ 59
def prefixEnd_4984444 : Nat := 4983230072969 + 3 ^ 40 * 4984444 * 2
def baseEnd_4984444 : Nat := 2559415567419201573626965

theorem tailTrace_4984444 : CollatzResearch.WordTrace tailWord_4984444 prefixEnd_4984444 2559415567419201573626965 := by
  unfold tailWord_4984444
  simp only [CollatzResearch.WordTrace]
  refine ⟨90898803977109069053412193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 121198405302812092071216257 90898803977109069053412193)
  ·
    refine ⟨68174102982831801790059145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 90898803977109069053412193 68174102982831801790059145)
    ·
      refine ⟨51130577237123851342544359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 68174102982831801790059145 51130577237123851342544359)
      ·
        refine ⟨76695865855685777013816539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51130577237123851342544359 76695865855685777013816539)
        ·
          refine ⟨115043798783528665520724809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 76695865855685777013816539 115043798783528665520724809)
          ·
            refine ⟨86282849087646499140543607, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 115043798783528665520724809 86282849087646499140543607)
            ·
              refine ⟨129424273631469748710815411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 86282849087646499140543607 129424273631469748710815411)
              ·
                refine ⟨194136410447204623066223117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 129424273631469748710815411 194136410447204623066223117)
                ·
                  refine ⟨72801153917701733649833669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 194136410447204623066223117 72801153917701733649833669)
                  ·
                    refine ⟨13650216359569075059343813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 72801153917701733649833669 13650216359569075059343813)
                    ·
                      refine ⟨2559415567419201573626965, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13650216359569075059343813 2559415567419201573626965)
                      ·
                        rfl

theorem cell23_4984444_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 1, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 1, 1, 3, 4, 4].length) (baseStart_4984444 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4984444 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4984444 prefixEnd_4984444 := by exact prefixLift 4984444
  have htrace : WordTrace (prefixWord ++ tailWord_4984444) baseStart_4984444 baseEnd_4984444 := by
    simpa [prefixWord, tailWord_4984444, baseEnd_4984444] using wordTrace_append hprefix tailTrace_4984444
  have hstable : (prefixWord ++ tailWord_4984444).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4984444).length < 2 ^ (prefixWord ++ tailWord_4984444).sum := by decide
  have hdescent : baseEnd_4984444 < baseStart_4984444 := by decide
  rcases family_descends (prefixWord ++ tailWord_4984444) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4984448 : List Nat := [2, 1, 1, 2, 1, 4, 2, 2, 4, 2, 2]
def baseStart_4984448 : Nat := 118140960795 + 4984448 * 2 ^ 59
def prefixEnd_4984448 : Nat := 4983230072969 + 3 ^ 40 * 4984448 * 2
def baseEnd_4984448 : Nat := 2559417621341819557976947

theorem tailTrace_4984448 : CollatzResearch.WordTrace tailWord_4984448 prefixEnd_4984448 2559417621341819557976947 := by
  unfold tailWord_4984448
  simp only [CollatzResearch.WordTrace]
  refine ⟨90898876923101823394984999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 121198502564135764526646665 90898876923101823394984999)
  ·
    refine ⟨136348315384652735092477499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90898876923101823394984999 136348315384652735092477499)
    ·
      refine ⟨204522473076979102638716249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 136348315384652735092477499 204522473076979102638716249)
      ·
        refine ⟨153391854807734326979037187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 204522473076979102638716249 153391854807734326979037187)
        ·
          refine ⟨230087782211601490468555781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 153391854807734326979037187 230087782211601490468555781)
          ·
            refine ⟨43141459164675279462854209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 230087782211601490468555781 43141459164675279462854209)
            ·
              refine ⟨32356094373506459597140657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 43141459164675279462854209 32356094373506459597140657)
              ·
                refine ⟨24267070780129844697855493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 32356094373506459597140657 24267070780129844697855493)
                ·
                  refine ⟨4550075771274345880847905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 24267070780129844697855493 4550075771274345880847905)
                  ·
                    refine ⟨3412556828455759410635929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4550075771274345880847905 3412556828455759410635929)
                    ·
                      refine ⟨2559417621341819557976947, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3412556828455759410635929 2559417621341819557976947)
                      ·
                        rfl

theorem cell23_4984448_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 2, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 2, 2, 4, 2, 2].length) (baseStart_4984448 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4984448 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4984448 prefixEnd_4984448 := by exact prefixLift 4984448
  have htrace : WordTrace (prefixWord ++ tailWord_4984448) baseStart_4984448 baseEnd_4984448 := by
    simpa [prefixWord, tailWord_4984448, baseEnd_4984448] using wordTrace_append hprefix tailTrace_4984448
  have hstable : (prefixWord ++ tailWord_4984448).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4984448).length < 2 ^ (prefixWord ++ tailWord_4984448).sum := by decide
  have hdescent : baseEnd_4984448 < baseStart_4984448 := by decide
  rcases family_descends (prefixWord ++ tailWord_4984448) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4984471 : List Nat := [1, 1, 3, 3, 2, 3, 2, 1, 7]
def baseStart_4984471 : Nat := 118140960795 + 4984471 * 2 ^ 59
def prefixEnd_4984471 : Nat := 4983230072969 + 3 ^ 40 * 4984471 * 2
def baseEnd_4984471 : Nat := 284381047932985885332149

theorem tailTrace_4984471 : CollatzResearch.WordTrace tailWord_4984471 prefixEnd_4984471 284381047932985885332149 := by
  unfold tailWord_4984471
  simp only [CollatzResearch.WordTrace]
  refine ⟨181798592725120321718057267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121199061816746881145371511 181798592725120321718057267)
  ·
    refine ⟨272697889087680482577085901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 181798592725120321718057267 272697889087680482577085901)
    ·
      refine ⟨102261708407880180966407213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 272697889087680482577085901 102261708407880180966407213)
      ·
        refine ⟨38348140652955067862402705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 102261708407880180966407213 38348140652955067862402705)
        ·
          refine ⟨28761105489716300896802029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38348140652955067862402705 28761105489716300896802029)
          ·
            refine ⟨10785414558643612836300761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 28761105489716300896802029 10785414558643612836300761)
            ·
              refine ⟨8089060918982709627225571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10785414558643612836300761 8089060918982709627225571)
              ·
                refine ⟨12133591378474064440838357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8089060918982709627225571 12133591378474064440838357)
                ·
                  refine ⟨284381047932985885332149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 12133591378474064440838357 284381047932985885332149)
                  ·
                    rfl

theorem cell23_4984471_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 3, 2, 1, 7].length) (baseStart_4984471 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4984471 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4984471 prefixEnd_4984471 := by exact prefixLift 4984471
  have htrace : WordTrace (prefixWord ++ tailWord_4984471) baseStart_4984471 baseEnd_4984471 := by
    simpa [prefixWord, tailWord_4984471, baseEnd_4984471] using wordTrace_append hprefix tailTrace_4984471
  have hstable : (prefixWord ++ tailWord_4984471).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4984471).length < 2 ^ (prefixWord ++ tailWord_4984471).sum := by decide
  have hdescent : baseEnd_4984471 < baseStart_4984471 := by decide
  rcases family_descends (prefixWord ++ tailWord_4984471) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4984478 : List Nat := [4, 3, 1, 1, 1, 2, 2, 1, 2, 2, 4]
def baseStart_4984478 : Nat := 118140960795 + 4984478 * 2 ^ 59
def prefixEnd_4984478 : Nat := 4983230072969 + 3 ^ 40 * 4984478 * 2
def baseEnd_4984478 : Nat := 2559433025761454440601809

theorem tailTrace_4984478 : CollatzResearch.WordTrace tailWord_4984478 prefixEnd_4984478 2559433025761454440601809 := by
  unfold tailWord_4984478
  simp only [CollatzResearch.WordTrace]
  refine ⟨22724856004511870239195261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 121199232024063307942374725 22724856004511870239195261)
  ·
    refine ⟨8521821001691951339698223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 22724856004511870239195261 8521821001691951339698223)
    ·
      refine ⟨12782731502537927009547335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8521821001691951339698223 12782731502537927009547335)
      ·
        refine ⟨19174097253806890514321003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12782731502537927009547335 19174097253806890514321003)
        ·
          refine ⟨28761145880710335771481505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19174097253806890514321003 28761145880710335771481505)
          ·
            refine ⟨21570859410532751828611129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28761145880710335771481505 21570859410532751828611129)
            ·
              refine ⟨16178144557899563871458347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21570859410532751828611129 16178144557899563871458347)
              ·
                refine ⟨24267216836849345807187521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16178144557899563871458347 24267216836849345807187521)
                ·
                  refine ⟨18200412627637009355390641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 24267216836849345807187521 18200412627637009355390641)
                  ·
                    refine ⟨13650309470727757016542981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 18200412627637009355390641 13650309470727757016542981)
                    ·
                      refine ⟨2559433025761454440601809, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13650309470727757016542981 2559433025761454440601809)
                      ·
                        rfl

theorem cell23_4984478_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 2, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 2, 2, 1, 2, 2, 4].length) (baseStart_4984478 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4984478 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4984478 prefixEnd_4984478 := by exact prefixLift 4984478
  have htrace : WordTrace (prefixWord ++ tailWord_4984478) baseStart_4984478 baseEnd_4984478 := by
    simpa [prefixWord, tailWord_4984478, baseEnd_4984478] using wordTrace_append hprefix tailTrace_4984478
  have hstable : (prefixWord ++ tailWord_4984478).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4984478).length < 2 ^ (prefixWord ++ tailWord_4984478).sum := by decide
  have hdescent : baseEnd_4984478 < baseStart_4984478 := by decide
  rcases family_descends (prefixWord ++ tailWord_4984478) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4984606 : List Nat := [4, 3, 2, 2, 2, 1, 1, 1, 2, 1, 4]
def baseStart_4984606 : Nat := 118140960795 + 4984606 * 2 ^ 59
def prefixEnd_4984606 : Nat := 4983230072969 + 3 ^ 40 * 4984606 * 2
def baseEnd_4984606 : Nat := 2559498751285229939801221

theorem tailTrace_4984606 : CollatzResearch.WordTrace tailWord_4984606 prefixEnd_4984606 2559498751285229939801221 := by
  unfold tailWord_4984606
  simp only [CollatzResearch.WordTrace]
  refine ⟨22725439572453904971777709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 121202344386420826516147781 22725439572453904971777709)
  ·
    refine ⟨8522039839670214364416641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 22725439572453904971777709 8522039839670214364416641)
    ·
      refine ⟨6391529879752660773312481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8522039839670214364416641 6391529879752660773312481)
      ·
        refine ⟨4793647409814495579984361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6391529879752660773312481 4793647409814495579984361)
        ·
          refine ⟨3595235557360871684988271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4793647409814495579984361 3595235557360871684988271)
          ·
            refine ⟨5392853336041307527482407, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3595235557360871684988271 5392853336041307527482407)
            ·
              refine ⟨8089280004061961291223611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5392853336041307527482407 8089280004061961291223611)
              ·
                refine ⟨12133920006092941936835417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8089280004061961291223611 12133920006092941936835417)
                ·
                  refine ⟨9100440004569706452626563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12133920006092941936835417 9100440004569706452626563)
                  ·
                    refine ⟨13650660006854559678939845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9100440004569706452626563 13650660006854559678939845)
                    ·
                      refine ⟨2559498751285229939801221, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13650660006854559678939845 2559498751285229939801221)
                      ·
                        rfl

theorem cell23_4984606_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 2, 2, 1, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 2, 2, 1, 1, 1, 2, 1, 4].length) (baseStart_4984606 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4984606 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4984606 prefixEnd_4984606 := by exact prefixLift 4984606
  have htrace : WordTrace (prefixWord ++ tailWord_4984606) baseStart_4984606 baseEnd_4984606 := by
    simpa [prefixWord, tailWord_4984606, baseEnd_4984606] using wordTrace_append hprefix tailTrace_4984606
  have hstable : (prefixWord ++ tailWord_4984606).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4984606).length < 2 ^ (prefixWord ++ tailWord_4984606).sum := by decide
  have hdescent : baseEnd_4984606 < baseStart_4984606 := by decide
  rcases family_descends (prefixWord ++ tailWord_4984606) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4984608 : List Nat := [2, 1, 1, 5, 1, 1, 2, 4, 1, 5]
def baseStart_4984608 : Nat := 118140960795 + 4984608 * 2 ^ 59
def prefixEnd_4984608 : Nat := 4983230072969 + 3 ^ 40 * 4984608 * 2
def baseEnd_4984608 : Nat := 853166592748846310658737

theorem tailTrace_4984608 : CollatzResearch.WordTrace tailWord_4984608 prefixEnd_4984608 853166592748846310658737 := by
  unfold tailWord_4984608
  simp only [CollatzResearch.WordTrace]
  refine ⟨90901794762811997057897239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 121202393017082662743862985 90901794762811997057897239)
  ·
    refine ⟨136352692144217995586845859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90901794762811997057897239 136352692144217995586845859)
    ·
      refine ⟨204529038216326993380268789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 136352692144217995586845859 204529038216326993380268789)
      ·
        refine ⟨19174597332780655629400199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 204529038216326993380268789 19174597332780655629400199)
        ·
          refine ⟨28761895999170983444100299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19174597332780655629400199 28761895999170983444100299)
          ·
            refine ⟨43142843998756475166150449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28761895999170983444100299 43142843998756475166150449)
            ·
              refine ⟨32357132999067356374612837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 43142843998756475166150449 32357132999067356374612837)
              ·
                refine ⟨6066962437325129320239907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 32357132999067356374612837 6066962437325129320239907)
                ·
                  refine ⟨9100443655987693980359861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6066962437325129320239907 9100443655987693980359861)
                  ·
                    refine ⟨853166592748846310658737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9100443655987693980359861 853166592748846310658737)
                    ·
                      rfl

theorem cell23_4984608_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 2, 4, 1, 5].length) (baseStart_4984608 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4984608 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4984608 prefixEnd_4984608 := by exact prefixLift 4984608
  have htrace : WordTrace (prefixWord ++ tailWord_4984608) baseStart_4984608 baseEnd_4984608 := by
    simpa [prefixWord, tailWord_4984608, baseEnd_4984608] using wordTrace_append hprefix tailTrace_4984608
  have hstable : (prefixWord ++ tailWord_4984608).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4984608).length < 2 ^ (prefixWord ++ tailWord_4984608).sum := by decide
  have hdescent : baseEnd_4984608 < baseStart_4984608 := by decide
  rcases family_descends (prefixWord ++ tailWord_4984608) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4984625 : List Nat := [1, 2, 2, 3, 2, 2, 4, 1, 1, 5]
def baseStart_4984625 : Nat := 118140960795 + 4984625 * 2 ^ 59
def prefixEnd_4984625 : Nat := 4983230072969 + 3 ^ 40 * 4984625 * 2
def baseEnd_4984625 : Nat := 853169502472555121821211

theorem tailTrace_4984625 : CollatzResearch.WordTrace tailWord_4984625 prefixEnd_4984625 853169502472555121821211 := by
  unfold tailWord_4984625
  simp only [CollatzResearch.WordTrace]
  refine ⟨181804209566562406019163329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121202806377708270679442219 181804209566562406019163329)
  ·
    refine ⟨136353157174921804514372497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 181804209566562406019163329 136353157174921804514372497)
    ·
      refine ⟨102264867881191353385779373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 136353157174921804514372497 102264867881191353385779373)
      ·
        refine ⟨38349325455446757519667265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 102264867881191353385779373 38349325455446757519667265)
        ·
          refine ⟨28761994091585068139750449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38349325455446757519667265 28761994091585068139750449)
          ·
            refine ⟨21571495568688801104812837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28761994091585068139750449 21571495568688801104812837)
            ·
              refine ⟨4044655419129150207152407, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 21571495568688801104812837 4044655419129150207152407)
              ·
                refine ⟨6066983128693725310728611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4044655419129150207152407 6066983128693725310728611)
                ·
                  refine ⟨9100474693040587966092917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6066983128693725310728611 9100474693040587966092917)
                  ·
                    refine ⟨853169502472555121821211, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9100474693040587966092917 853169502472555121821211)
                    ·
                      rfl

theorem cell23_4984625_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 2, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 2, 4, 1, 1, 5].length) (baseStart_4984625 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4984625 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4984625 prefixEnd_4984625 := by exact prefixLift 4984625
  have htrace : WordTrace (prefixWord ++ tailWord_4984625) baseStart_4984625 baseEnd_4984625 := by
    simpa [prefixWord, tailWord_4984625, baseEnd_4984625] using wordTrace_append hprefix tailTrace_4984625
  have hstable : (prefixWord ++ tailWord_4984625).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4984625).length < 2 ^ (prefixWord ++ tailWord_4984625).sum := by decide
  have hdescent : baseEnd_4984625 < baseStart_4984625 := by decide
  rcases family_descends (prefixWord ++ tailWord_4984625) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4984648 : List Nat := [2, 1, 3, 1, 1, 5, 1, 2, 1, 1, 5]
def baseStart_4984648 : Nat := 118140960795 + 4984648 * 2 ^ 59
def prefixEnd_4984648 : Nat := 4983230072969 + 3 ^ 40 * 4984648 * 2
def baseEnd_4984648 : Nat := 2559520317472718775476027

theorem tailTrace_4984648 : CollatzResearch.WordTrace tailWord_4984648 prefixEnd_4984648 2559520317472718775476027 := by
  unfold tailWord_4984648
  simp only [CollatzResearch.WordTrace]
  refine ⟨90902524222739540473625299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 121203365630319387298167065 90902524222739540473625299)
  ·
    refine ⟨136353786334109310710437949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90902524222739540473625299 136353786334109310710437949)
    ·
      refine ⟨51132669875290991516414231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 136353786334109310710437949 51132669875290991516414231)
      ·
        refine ⟨76699004812936487274621347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51132669875290991516414231 76699004812936487274621347)
        ·
          refine ⟨115048507219404730911932021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 76699004812936487274621347 115048507219404730911932021)
          ·
            refine ⟨10785797551819193522993627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 115048507219404730911932021 10785797551819193522993627)
            ·
              refine ⟨16178696327728790284490441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10785797551819193522993627 16178696327728790284490441)
              ·
                refine ⟨12134022245796592713367831, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16178696327728790284490441 12134022245796592713367831)
                ·
                  refine ⟨18201033368694889070051747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12134022245796592713367831 18201033368694889070051747)
                  ·
                    refine ⟨27301550053042333605077621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 18201033368694889070051747 27301550053042333605077621)
                    ·
                      refine ⟨2559520317472718775476027, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 27301550053042333605077621 2559520317472718775476027)
                      ·
                        rfl

theorem cell23_4984648_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 5, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 5, 1, 2, 1, 1, 5].length) (baseStart_4984648 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4984648 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4984648 prefixEnd_4984648 := by exact prefixLift 4984648
  have htrace : WordTrace (prefixWord ++ tailWord_4984648) baseStart_4984648 baseEnd_4984648 := by
    simpa [prefixWord, tailWord_4984648, baseEnd_4984648] using wordTrace_append hprefix tailTrace_4984648
  have hstable : (prefixWord ++ tailWord_4984648).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4984648).length < 2 ^ (prefixWord ++ tailWord_4984648).sum := by decide
  have hdescent : baseEnd_4984648 < baseStart_4984648 := by decide
  rcases family_descends (prefixWord ++ tailWord_4984648) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4984658 : List Nat := [3, 2, 2, 1, 1, 4, 1, 1, 1, 1, 6]
def baseStart_4984658 : Nat := 118140960795 + 4984658 * 2 ^ 59
def prefixEnd_4984658 : Nat := 4983230072969 + 3 ^ 40 * 4984658 * 2
def baseEnd_4984658 : Nat := 2559525452279263736350981

theorem tailTrace_4984658 : CollatzResearch.WordTrace tailWord_4984658 prefixEnd_4984658 2559525452279263736350981 := by
  unfold tailWord_4984658
  simp only [CollatzResearch.WordTrace]
  refine ⟨45451353293860713163778657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 121203608783628568436743085 45451353293860713163778657)
  ·
    refine ⟨34088514970395534872833993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45451353293860713163778657 34088514970395534872833993)
    ·
      refine ⟨25566386227796651154625495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34088514970395534872833993 25566386227796651154625495)
      ·
        refine ⟨38349579341694976731938243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25566386227796651154625495 38349579341694976731938243)
        ·
          refine ⟨57524369012542465097907365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38349579341694976731938243 57524369012542465097907365)
          ·
            refine ⟨10785819189851712205857631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 57524369012542465097907365 10785819189851712205857631)
            ·
              refine ⟨16178728784777568308786447, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10785819189851712205857631 16178728784777568308786447)
              ·
                refine ⟨24268093177166352463179671, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16178728784777568308786447 24268093177166352463179671)
                ·
                  refine ⟨36402139765749528694769507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24268093177166352463179671 36402139765749528694769507)
                  ·
                    refine ⟨54603209648624293042154261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 36402139765749528694769507 54603209648624293042154261)
                    ·
                      refine ⟨2559525452279263736350981, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 54603209648624293042154261 2559525452279263736350981)
                      ·
                        rfl

theorem cell23_4984658_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 4, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 4, 1, 1, 1, 1, 6].length) (baseStart_4984658 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4984658 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4984658 prefixEnd_4984658 := by exact prefixLift 4984658
  have htrace : WordTrace (prefixWord ++ tailWord_4984658) baseStart_4984658 baseEnd_4984658 := by
    simpa [prefixWord, tailWord_4984658, baseEnd_4984658] using wordTrace_append hprefix tailTrace_4984658
  have hstable : (prefixWord ++ tailWord_4984658).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4984658).length < 2 ^ (prefixWord ++ tailWord_4984658).sum := by decide
  have hdescent : baseEnd_4984658 < baseStart_4984658 := by decide
  rcases family_descends (prefixWord ++ tailWord_4984658) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4984665 : List Nat := [1, 2, 1, 2, 2, 3, 4, 2, 1, 2, 3]
def baseStart_4984665 : Nat := 118140960795 + 4984665 * 2 ^ 59
def prefixEnd_4984665 : Nat := 4983230072969 + 3 ^ 40 * 4984665 * 2
def baseEnd_4984665 : Nat := 2559529046643845208963449

theorem tailTrace_4984665 : CollatzResearch.WordTrace tailWord_4984665 prefixEnd_4984665 2559529046643845208963449 := by
  unfold tailWord_4984665
  simp only [CollatzResearch.WordTrace]
  refine ⟨181805668486417492850619449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121203778990944995233746299 181805668486417492850619449)
  ·
    refine ⟨136354251364813119637964587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 181805668486417492850619449 136354251364813119637964587)
    ·
      refine ⟨204531377047219679456946881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 136354251364813119637964587 204531377047219679456946881)
      ·
        refine ⟨153398532785414759592710161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 204531377047219679456946881 153398532785414759592710161)
        ·
          refine ⟨115048899589061069694532621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 153398532785414759592710161 115048899589061069694532621)
          ·
            refine ⟨43143337345897901135449733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 115048899589061069694532621 43143337345897901135449733)
            ·
              refine ⟨8089375752355856462896825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 43143337345897901135449733 8089375752355856462896825)
              ·
                refine ⟨6067031814266892347172619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8089375752355856462896825 6067031814266892347172619)
                ·
                  refine ⟨9100547721400338520758929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6067031814266892347172619 9100547721400338520758929)
                  ·
                    refine ⟨6825410791050253890569197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9100547721400338520758929 6825410791050253890569197)
                    ·
                      refine ⟨2559529046643845208963449, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6825410791050253890569197 2559529046643845208963449)
                      ·
                        rfl

theorem cell23_4984665_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 4, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 4, 2, 1, 2, 3].length) (baseStart_4984665 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4984665 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4984665 prefixEnd_4984665 := by exact prefixLift 4984665
  have htrace : WordTrace (prefixWord ++ tailWord_4984665) baseStart_4984665 baseEnd_4984665 := by
    simpa [prefixWord, tailWord_4984665, baseEnd_4984665] using wordTrace_append hprefix tailTrace_4984665
  have hstable : (prefixWord ++ tailWord_4984665).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4984665).length < 2 ^ (prefixWord ++ tailWord_4984665).sum := by decide
  have hdescent : baseEnd_4984665 < baseStart_4984665 := by decide
  rcases family_descends (prefixWord ++ tailWord_4984665) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4984682 : List Nat := [3, 1, 3, 4, 1, 1, 2, 1, 1, 1, 5]
def baseStart_4984682 : Nat := 118140960795 + 4984682 * 2 ^ 59
def prefixEnd_4984682 : Nat := 4983230072969 + 3 ^ 40 * 4984682 * 2
def baseEnd_4984682 : Nat := 2559537775814971642450871

theorem tailTrace_4984682 : CollatzResearch.WordTrace tailWord_4984682 prefixEnd_4984682 2559537775814971642450871 := by
  unfold tailWord_4984682
  simp only [CollatzResearch.WordTrace]
  refine ⟨45451572131838976188497075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 121204192351570603169325533 45451572131838976188497075)
  ·
    refine ⟨68177358197758464282745613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45451572131838976188497075 68177358197758464282745613)
    ·
      refine ⟨25566509324159424106029605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 68177358197758464282745613 25566509324159424106029605)
      ·
        refine ⟨4793720498279892019880551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 25566509324159424106029605 4793720498279892019880551)
        ·
          refine ⟨7190580747419838029820827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4793720498279892019880551 7190580747419838029820827)
          ·
            refine ⟨10785871121129757044731241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7190580747419838029820827 10785871121129757044731241)
            ·
              refine ⟨8089403340847317783548431, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10785871121129757044731241 8089403340847317783548431)
              ·
                refine ⟨12134105011270976675322647, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8089403340847317783548431 12134105011270976675322647)
                ·
                  refine ⟨18201157516906465012983971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12134105011270976675322647 18201157516906465012983971)
                  ·
                    refine ⟨27301736275359697519475957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 18201157516906465012983971 27301736275359697519475957)
                    ·
                      refine ⟨2559537775814971642450871, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 27301736275359697519475957 2559537775814971642450871)
                      ·
                        rfl

theorem cell23_4984682_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 4, 1, 1, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 4, 1, 1, 2, 1, 1, 1, 5].length) (baseStart_4984682 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4984682 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4984682 prefixEnd_4984682 := by exact prefixLift 4984682
  have htrace : WordTrace (prefixWord ++ tailWord_4984682) baseStart_4984682 baseEnd_4984682 := by
    simpa [prefixWord, tailWord_4984682, baseEnd_4984682] using wordTrace_append hprefix tailTrace_4984682
  have hstable : (prefixWord ++ tailWord_4984682).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4984682).length < 2 ^ (prefixWord ++ tailWord_4984682).sum := by decide
  have hdescent : baseEnd_4984682 < baseStart_4984682 := by decide
  rcases family_descends (prefixWord ++ tailWord_4984682) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4984691 : List Nat := [1, 1, 1, 2, 2, 1, 3, 1, 4, 2, 5]
def baseStart_4984691 : Nat := 118140960795 + 4984691 * 2 ^ 59
def prefixEnd_4984691 : Nat := 4983230072969 + 3 ^ 40 * 4984691 * 2
def baseEnd_4984691 : Nat := 2559542397140862107238329

theorem tailTrace_4984691 : CollatzResearch.WordTrace tailWord_4984691 prefixEnd_4984691 2559542397140862107238329 := by
  unfold tailWord_4984691
  simp only [CollatzResearch.WordTrace]
  refine ⟨181806616784323299291065927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121204411189548866194043951 181806616784323299291065927)
  ·
    refine ⟨272709925176484948936598891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 181806616784323299291065927 272709925176484948936598891)
    ·
      refine ⟨409064887764727423404898337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 272709925176484948936598891 409064887764727423404898337)
      ·
        refine ⟨306798665823545567553673753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 409064887764727423404898337 306798665823545567553673753)
        ·
          refine ⟨230098999367659175665255315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 306798665823545567553673753 230098999367659175665255315)
          ·
            refine ⟨345148499051488763497882973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 230098999367659175665255315 345148499051488763497882973)
            ·
              refine ⟨129430687144308286311706115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 345148499051488763497882973 129430687144308286311706115)
              ·
                refine ⟨194146030716462429467559173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 129430687144308286311706115 194146030716462429467559173)
                ·
                  refine ⟨36402380759336705525167345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 194146030716462429467559173 36402380759336705525167345)
                  ·
                    refine ⟨27301785569502529143875509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 36402380759336705525167345 27301785569502529143875509)
                    ·
                      refine ⟨2559542397140862107238329, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 27301785569502529143875509 2559542397140862107238329)
                      ·
                        rfl

theorem cell23_4984691_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 3, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 3, 1, 4, 2, 5].length) (baseStart_4984691 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4984691 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4984691 prefixEnd_4984691 := by exact prefixLift 4984691
  have htrace : WordTrace (prefixWord ++ tailWord_4984691) baseStart_4984691 baseEnd_4984691 := by
    simpa [prefixWord, tailWord_4984691, baseEnd_4984691] using wordTrace_append hprefix tailTrace_4984691
  have hstable : (prefixWord ++ tailWord_4984691).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4984691).length < 2 ^ (prefixWord ++ tailWord_4984691).sum := by decide
  have hdescent : baseEnd_4984691 < baseStart_4984691 := by decide
  rcases family_descends (prefixWord ++ tailWord_4984691) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4984765 : List Nat := [1, 4, 1, 2, 3, 2, 1, 1, 2, 2, 4]
def baseStart_4984765 : Nat := 118140960795 + 4984765 * 2 ^ 59
def prefixEnd_4984765 : Nat := 4983230072969 + 3 ^ 40 * 4984765 * 2
def baseEnd_4984765 : Nat := 2559580394709294817712989

theorem tailTrace_4984765 : CollatzResearch.WordTrace tailWord_4984765 prefixEnd_4984765 2559580394709294817712989 := by
  unfold tailWord_4984765
  simp only [CollatzResearch.WordTrace]
  refine ⟨181809315786055209929259749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121206210524036806619506499 181809315786055209929259749)
  ·
    refine ⟨34089246709885351861736203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 181809315786055209929259749 34089246709885351861736203)
    ·
      refine ⟨51133870064828027792604305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34089246709885351861736203 51133870064828027792604305)
      ·
        refine ⟨38350402548621020844453229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 51133870064828027792604305 38350402548621020844453229)
        ·
          refine ⟨14381400955732882816669961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 38350402548621020844453229 14381400955732882816669961)
          ·
            refine ⟨10786050716799662112502471, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14381400955732882816669961 10786050716799662112502471)
            ·
              refine ⟨16179076075199493168753707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10786050716799662112502471 16179076075199493168753707)
              ·
                refine ⟨24268614112799239753130561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16179076075199493168753707 24268614112799239753130561)
                ·
                  refine ⟨18201460584599429814847921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 24268614112799239753130561 18201460584599429814847921)
                  ·
                    refine ⟨13651095438449572361135941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 18201460584599429814847921 13651095438449572361135941)
                    ·
                      refine ⟨2559580394709294817712989, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13651095438449572361135941 2559580394709294817712989)
                      ·
                        rfl

theorem cell23_4984765_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 2, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 2, 1, 1, 2, 2, 4].length) (baseStart_4984765 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4984765 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4984765 prefixEnd_4984765 := by exact prefixLift 4984765
  have htrace : WordTrace (prefixWord ++ tailWord_4984765) baseStart_4984765 baseEnd_4984765 := by
    simpa [prefixWord, tailWord_4984765, baseEnd_4984765] using wordTrace_append hprefix tailTrace_4984765
  have hstable : (prefixWord ++ tailWord_4984765).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4984765).length < 2 ^ (prefixWord ++ tailWord_4984765).sum := by decide
  have hdescent : baseEnd_4984765 < baseStart_4984765 := by decide
  rcases family_descends (prefixWord ++ tailWord_4984765) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4984790 : List Nat := [5, 2, 1, 1, 4, 1, 2, 1, 1, 3, 2]
def baseStart_4984790 : Nat := 118140960795 + 4984790 * 2 ^ 59
def prefixEnd_4984790 : Nat := 4983230072969 + 3 ^ 40 * 4984790 * 2
def baseEnd_4984790 : Nat := 2559593231725657219900375

theorem tailTrace_4984790 : CollatzResearch.WordTrace tailWord_4984790 prefixEnd_4984790 2559593231725657219900375 := by
  unfold tailWord_4984790
  simp only [CollatzResearch.WordTrace]
  refine ⟨11363139225685289949932489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 121206818407309759465946549 11363139225685289949932489)
  ·
    refine ⟨8522354419263967462449367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11363139225685289949932489 8522354419263967462449367)
    ·
      refine ⟨12783531628895951193674051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8522354419263967462449367 12783531628895951193674051)
      ·
        refine ⟨19175297443343926790511077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12783531628895951193674051 19175297443343926790511077)
        ·
          refine ⟨3595368270626986273220827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 19175297443343926790511077 3595368270626986273220827)
          ·
            refine ⟨5393052405940479409831241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3595368270626986273220827 5393052405940479409831241)
            ·
              refine ⟨4044789304455359557373431, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5393052405940479409831241 4044789304455359557373431)
              ·
                refine ⟨6067183956683039336060147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4044789304455359557373431 6067183956683039336060147)
                ·
                  refine ⟨9100775935024559004090221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6067183956683039336060147 9100775935024559004090221)
                  ·
                    refine ⟨3412790975634209626533833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9100775935024559004090221 3412790975634209626533833)
                    ·
                      refine ⟨2559593231725657219900375, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3412790975634209626533833 2559593231725657219900375)
                      ·
                        rfl

theorem cell23_4984790_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 4, 1, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 4, 1, 2, 1, 1, 3, 2].length) (baseStart_4984790 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4984790 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4984790 prefixEnd_4984790 := by exact prefixLift 4984790
  have htrace : WordTrace (prefixWord ++ tailWord_4984790) baseStart_4984790 baseEnd_4984790 := by
    simpa [prefixWord, tailWord_4984790, baseEnd_4984790] using wordTrace_append hprefix tailTrace_4984790
  have hstable : (prefixWord ++ tailWord_4984790).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4984790).length < 2 ^ (prefixWord ++ tailWord_4984790).sum := by decide
  have hdescent : baseEnd_4984790 < baseStart_4984790 := by decide
  rcases family_descends (prefixWord ++ tailWord_4984790) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4984882 : List Nat := [3, 2, 1, 1, 2, 3, 4, 1, 6]
def baseStart_4984882 : Nat := 118140960795 + 4984882 * 2 ^ 59
def prefixEnd_4984882 : Nat := 4983230072969 + 3 ^ 40 * 4984882 * 2
def baseEnd_4984882 : Nat := 284404496882874539994439

theorem tailTrace_4984882 : CollatzResearch.WordTrace tailWord_4984882 prefixEnd_4984882 284404496882874539994439 := by
  unfold tailWord_4984882
  simp only [CollatzResearch.WordTrace]
  refine ⟨45453395781657834727817225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 121209055417754225940845933 45453395781657834727817225)
  ·
    refine ⟨34090046836243376045862919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45453395781657834727817225 34090046836243376045862919)
    ·
      refine ⟨51135070254365064068794379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34090046836243376045862919 51135070254365064068794379)
      ·
        refine ⟨76702605381547596103191569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51135070254365064068794379 76702605381547596103191569)
        ·
          refine ⟨57526954036160697077393677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 76702605381547596103191569 57526954036160697077393677)
          ·
            refine ⟨21572607763560261404022629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 57526954036160697077393677 21572607763560261404022629)
            ·
              refine ⟨4044863955667549013254243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 21572607763560261404022629 4044863955667549013254243)
              ·
                refine ⟨6067295933501323519881365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4044863955667549013254243 6067295933501323519881365)
                ·
                  refine ⟨284404496882874539994439, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6067295933501323519881365 284404496882874539994439)
                  ·
                    rfl

theorem cell23_4984882_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 3, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 3, 4, 1, 6].length) (baseStart_4984882 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4984882 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4984882 prefixEnd_4984882 := by exact prefixLift 4984882
  have htrace : WordTrace (prefixWord ++ tailWord_4984882) baseStart_4984882 baseEnd_4984882 := by
    simpa [prefixWord, tailWord_4984882, baseEnd_4984882] using wordTrace_append hprefix tailTrace_4984882
  have hstable : (prefixWord ++ tailWord_4984882).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4984882).length < 2 ^ (prefixWord ++ tailWord_4984882).sum := by decide
  have hdescent : baseEnd_4984882 < baseStart_4984882 := by decide
  rcases family_descends (prefixWord ++ tailWord_4984882) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4984892 : List Nat := [2, 2, 2, 2, 2, 1, 2, 1, 5, 1, 3]
def baseStart_4984892 : Nat := 118140960795 + 4984892 * 2 ^ 59
def prefixEnd_4984892 : Nat := 4983230072969 + 3 ^ 40 * 4984892 * 2
def baseEnd_4984892 : Nat := 2559645606752415820824905

theorem tailTrace_4984892 : CollatzResearch.WordTrace tailWord_4984892 prefixEnd_4984892 2559645606752415820824905 := by
  unfold tailWord_4984892
  simp only [CollatzResearch.WordTrace]
  refine ⟨90906973928297555309566465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 121209298571063407079421953 90906973928297555309566465)
  ·
    refine ⟨68180230446223166482174849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 90906973928297555309566465 68180230446223166482174849)
    ·
      refine ⟨51135172834667374861631137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 68180230446223166482174849 51135172834667374861631137)
      ·
        refine ⟨38351379626000531146223353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 51135172834667374861631137 38351379626000531146223353)
        ·
          refine ⟨28763534719500398359667515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38351379626000531146223353 28763534719500398359667515)
          ·
            refine ⟨43145302079250597539501273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28763534719500398359667515 43145302079250597539501273)
            ·
              refine ⟨32358976559437948154625955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 43145302079250597539501273 32358976559437948154625955)
              ·
                refine ⟨48538464839156922231938933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32358976559437948154625955 48538464839156922231938933)
                ·
                  refine ⟨4550481078670961459244275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 48538464839156922231938933 4550481078670961459244275)
                  ·
                    refine ⟨6825721618006442188866413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4550481078670961459244275 6825721618006442188866413)
                    ·
                      refine ⟨2559645606752415820824905, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6825721618006442188866413 2559645606752415820824905)
                      ·
                        rfl

theorem cell23_4984892_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 2, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 2, 1, 5, 1, 3].length) (baseStart_4984892 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4984892 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4984892 prefixEnd_4984892 := by exact prefixLift 4984892
  have htrace : WordTrace (prefixWord ++ tailWord_4984892) baseStart_4984892 baseEnd_4984892 := by
    simpa [prefixWord, tailWord_4984892, baseEnd_4984892] using wordTrace_append hprefix tailTrace_4984892
  have hstable : (prefixWord ++ tailWord_4984892).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4984892).length < 2 ^ (prefixWord ++ tailWord_4984892).sum := by decide
  have hdescent : baseEnd_4984892 < baseStart_4984892 := by decide
  rcases family_descends (prefixWord ++ tailWord_4984892) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4984935 : List Nat := [1, 1, 5, 1, 1, 2, 2, 1, 3, 1, 5]
def baseStart_4984935 : Nat := 118140960795 + 4984935 * 2 ^ 59
def prefixEnd_4984935 : Nat := 4983230072969 + 3 ^ 40 * 4984935 * 2
def baseEnd_4984935 : Nat := 2559667686420559152587207

theorem tailTrace_4984935 : CollatzResearch.WordTrace tailWord_4984935 prefixEnd_4984935 2559667686420559152587207 := by
  unfold tailWord_4984935
  simp only [CollatzResearch.WordTrace]
  refine ⟨181815516195439328962948259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121210344130292885975298839 181815516195439328962948259)
  ·
    refine ⟨272723274293158993444422389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 181815516195439328962948259 272723274293158993444422389)
    ·
      refine ⟨25567806964983655635414599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 272723274293158993444422389 25567806964983655635414599)
      ·
        refine ⟨38351710447475483453121899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25567806964983655635414599 38351710447475483453121899)
        ·
          refine ⟨57527565671213225179682849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38351710447475483453121899 57527565671213225179682849)
          ·
            refine ⟨43145674253409918884762137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 57527565671213225179682849 43145674253409918884762137)
            ·
              refine ⟨32359255690057439163571603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 43145674253409918884762137 32359255690057439163571603)
              ·
                refine ⟨48538883535086158745357405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32359255690057439163571603 48538883535086158745357405)
                ·
                  refine ⟨18202081325657309529509027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 48538883535086158745357405 18202081325657309529509027)
                  ·
                    refine ⟨27303121988485964294263541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 18202081325657309529509027 27303121988485964294263541)
                    ·
                      refine ⟨2559667686420559152587207, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 27303121988485964294263541 2559667686420559152587207)
                      ·
                        rfl

theorem cell23_4984935_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 2, 1, 3, 1, 5].length) (baseStart_4984935 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4984935 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4984935 prefixEnd_4984935 := by exact prefixLift 4984935
  have htrace : WordTrace (prefixWord ++ tailWord_4984935) baseStart_4984935 baseEnd_4984935 := by
    simpa [prefixWord, tailWord_4984935, baseEnd_4984935] using wordTrace_append hprefix tailTrace_4984935
  have hstable : (prefixWord ++ tailWord_4984935).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4984935).length < 2 ^ (prefixWord ++ tailWord_4984935).sum := by decide
  have hdescent : baseEnd_4984935 < baseStart_4984935 := by decide
  rcases family_descends (prefixWord ++ tailWord_4984935) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4984942 : List Nat := [4, 1, 2, 2, 1, 1, 4, 1, 1, 6]
def baseStart_4984942 : Nat := 118140960795 + 4984942 * 2 ^ 59
def prefixEnd_4984942 : Nat := 4983230072969 + 3 ^ 40 * 4984942 * 2
def baseEnd_4984942 : Nat := 853223760261713541733225

theorem tailTrace_4984942 : CollatzResearch.WordTrace tailWord_4984942 prefixEnd_4984942 853223760261713541733225 := by
  unfold tailWord_4984942
  simp only [CollatzResearch.WordTrace]
  refine ⟨22726971438301746144806635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 121210514337609312772302053 22726971438301746144806635)
  ·
    refine ⟨34090457157452619217209953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22726971438301746144806635 34090457157452619217209953)
    ·
      refine ⟨25567842868089464412907465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34090457157452619217209953 25567842868089464412907465)
      ·
        refine ⟨19175882151067098309680599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25567842868089464412907465 19175882151067098309680599)
        ·
          refine ⟨28763823226600647464520899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19175882151067098309680599 28763823226600647464520899)
          ·
            refine ⟨43145734839900971196781349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28763823226600647464520899 43145734839900971196781349)
            ·
              refine ⟨8089825282481432099396503, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 43145734839900971196781349 8089825282481432099396503)
              ·
                refine ⟨12134737923722148149094755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8089825282481432099396503 12134737923722148149094755)
                ·
                  refine ⟨18202106885583222223642133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12134737923722148149094755 18202106885583222223642133)
                  ·
                    refine ⟨853223760261713541733225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 18202106885583222223642133 853223760261713541733225)
                    ·
                      rfl

theorem cell23_4984942_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 4, 1, 1, 6].length) (baseStart_4984942 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4984942 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4984942 prefixEnd_4984942 := by exact prefixLift 4984942
  have htrace : WordTrace (prefixWord ++ tailWord_4984942) baseStart_4984942 baseEnd_4984942 := by
    simpa [prefixWord, tailWord_4984942, baseEnd_4984942] using wordTrace_append hprefix tailTrace_4984942
  have hstable : (prefixWord ++ tailWord_4984942).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4984942).length < 2 ^ (prefixWord ++ tailWord_4984942).sum := by decide
  have hdescent : baseEnd_4984942 < baseStart_4984942 := by decide
  rcases family_descends (prefixWord ++ tailWord_4984942) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4984952 : List Nat := [2, 1, 2, 1, 1, 1, 3, 6, 1, 2, 3]
def baseStart_4984952 : Nat := 118140960795 + 4984952 * 2 ^ 59
def prefixEnd_4984952 : Nat := 4983230072969 + 3 ^ 40 * 4984952 * 2
def baseEnd_4984952 : Nat := 2559676415591685586074629

theorem tailTrace_4984952 : CollatzResearch.WordTrace tailWord_4984952 prefixEnd_4984952 2559676415591685586074629 := by
  unfold tailWord_4984952
  simp only [CollatzResearch.WordTrace]
  refine ⟨90908068118188870433158555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 121210757490918493910878073 90908068118188870433158555)
  ·
    refine ⟨136362102177283305649737833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90908068118188870433158555 136362102177283305649737833)
    ·
      refine ⟨102271576632962479237303375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 136362102177283305649737833 102271576632962479237303375)
      ·
        refine ⟨153407364949443718855955063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 102271576632962479237303375 153407364949443718855955063)
        ·
          refine ⟨230111047424165578283932595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 153407364949443718855955063 230111047424165578283932595)
          ·
            refine ⟨345166571136248367425898893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 230111047424165578283932595 345166571136248367425898893)
            ·
              refine ⟨129437464176093137784712085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 345166571136248367425898893 129437464176093137784712085)
              ·
                refine ⟨6067381133254365833658379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 129437464176093137784712085 6067381133254365833658379)
                ·
                  refine ⟨9101071699881548750487569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6067381133254365833658379 9101071699881548750487569)
                  ·
                    refine ⟨6825803774911161562865677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9101071699881548750487569 6825803774911161562865677)
                    ·
                      refine ⟨2559676415591685586074629, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6825803774911161562865677 2559676415591685586074629)
                      ·
                        rfl

theorem cell23_4984952_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 3, 6, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 3, 6, 1, 2, 3].length) (baseStart_4984952 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4984952 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4984952 prefixEnd_4984952 := by exact prefixLift 4984952
  have htrace : WordTrace (prefixWord ++ tailWord_4984952) baseStart_4984952 baseEnd_4984952 := by
    simpa [prefixWord, tailWord_4984952, baseEnd_4984952] using wordTrace_append hprefix tailTrace_4984952
  have hstable : (prefixWord ++ tailWord_4984952).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4984952).length < 2 ^ (prefixWord ++ tailWord_4984952).sum := by decide
  have hdescent : baseEnd_4984952 < baseStart_4984952 := by decide
  rcases family_descends (prefixWord ++ tailWord_4984952) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4984996 : List Nat := [2, 3, 1, 2, 5, 1, 1, 1, 1, 2, 4]
def baseStart_4984996 : Nat := 118140960795 + 4984996 * 2 ^ 59
def prefixEnd_4984996 : Nat := 4983230072969 + 3 ^ 40 * 4984996 * 2
def baseEnd_4984996 : Nat := 2559699008740483413924427

theorem tailTrace_4984996 : CollatzResearch.WordTrace tailWord_4984996 prefixEnd_4984996 2559699008740483413924427 := by
  unfold tailWord_4984996
  simp only [CollatzResearch.WordTrace]
  refine ⟨90908870524109168190459421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 121211827365478890920612561 90908870524109168190459421)
  ·
    refine ⟨34090826446540938071422283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 90908870524109168190459421 34090826446540938071422283)
    ·
      refine ⟨51136239669811407107133425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34090826446540938071422283 51136239669811407107133425)
      ·
        refine ⟨38352179752358555330350069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 51136239669811407107133425 38352179752358555330350069)
        ·
          refine ⟨3595516851783614562220319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 38352179752358555330350069 3595516851783614562220319)
          ·
            refine ⟨5393275277675421843330479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3595516851783614562220319 5393275277675421843330479)
            ·
              refine ⟨8089912916513132764995719, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5393275277675421843330479 8089912916513132764995719)
              ·
                refine ⟨12134869374769699147493579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8089912916513132764995719 12134869374769699147493579)
                ·
                  refine ⟨18202304062154548721240369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12134869374769699147493579 18202304062154548721240369)
                  ·
                    refine ⟨13651728046615911540930277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 18202304062154548721240369 13651728046615911540930277)
                    ·
                      refine ⟨2559699008740483413924427, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13651728046615911540930277 2559699008740483413924427)
                      ·
                        rfl

theorem cell23_4984996_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 5, 1, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 5, 1, 1, 1, 1, 2, 4].length) (baseStart_4984996 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4984996 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4984996 prefixEnd_4984996 := by exact prefixLift 4984996
  have htrace : WordTrace (prefixWord ++ tailWord_4984996) baseStart_4984996 baseEnd_4984996 := by
    simpa [prefixWord, tailWord_4984996, baseEnd_4984996] using wordTrace_append hprefix tailTrace_4984996
  have hstable : (prefixWord ++ tailWord_4984996).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4984996).length < 2 ^ (prefixWord ++ tailWord_4984996).sum := by decide
  have hdescent : baseEnd_4984996 < baseStart_4984996 := by decide
  rcases family_descends (prefixWord ++ tailWord_4984996) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4985039 : List Nat := [1, 1, 2, 1, 1, 3, 3, 3, 4, 2, 2]
def baseStart_4985039 : Nat := 118140960795 + 4985039 * 2 ^ 59
def prefixEnd_4985039 : Nat := 4983230072969 + 3 ^ 40 * 4985039 * 2
def baseEnd_4985039 : Nat := 2559721088408626745686729

theorem tailTrace_4985039 : CollatzResearch.WordTrace tailWord_4985039 prefixEnd_4985039 2559721088408626745686729 := by
  unfold tailWord_4985039
  simp only [CollatzResearch.WordTrace]
  refine ⟨181819309387062554724734171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121212872924708369816489447 181819309387062554724734171)
  ·
    refine ⟨272728964080593832087101257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 181819309387062554724734171 272728964080593832087101257)
    ·
      refine ⟨204546723060445374065325943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 272728964080593832087101257 204546723060445374065325943)
      ·
        refine ⟨306820084590668061097988915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 204546723060445374065325943 306820084590668061097988915)
        ·
          refine ⟨460230126886002091646983373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 306820084590668061097988915 460230126886002091646983373)
          ·
            refine ⟨172586297582250784367618765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 460230126886002091646983373 172586297582250784367618765)
            ·
              refine ⟨64719861593344044137857037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 172586297582250784367618765 64719861593344044137857037)
              ·
                refine ⟨24269948097504016551696389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 64719861593344044137857037 24269948097504016551696389)
                ·
                  refine ⟨4550615268282003103443073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 24269948097504016551696389 4550615268282003103443073)
                  ·
                    refine ⟨3412961451211502327582305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4550615268282003103443073 3412961451211502327582305)
                    ·
                      refine ⟨2559721088408626745686729, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3412961451211502327582305 2559721088408626745686729)
                      ·
                        rfl

theorem cell23_4985039_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 3, 3, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 3, 3, 4, 2, 2].length) (baseStart_4985039 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4985039 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4985039 prefixEnd_4985039 := by exact prefixLift 4985039
  have htrace : WordTrace (prefixWord ++ tailWord_4985039) baseStart_4985039 baseEnd_4985039 := by
    simpa [prefixWord, tailWord_4985039, baseEnd_4985039] using wordTrace_append hprefix tailTrace_4985039
  have hstable : (prefixWord ++ tailWord_4985039).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4985039).length < 2 ^ (prefixWord ++ tailWord_4985039).sum := by decide
  have hdescent : baseEnd_4985039 < baseStart_4985039 := by decide
  rcases family_descends (prefixWord ++ tailWord_4985039) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4985056 : List Nat := [2, 1, 1, 3, 1, 3, 3, 3, 2, 2, 2]
def baseStart_4985056 : Nat := 118140960795 + 4985056 * 2 ^ 59
def prefixEnd_4985056 : Nat := 4983230072969 + 3 ^ 40 * 4985056 * 2
def baseEnd_4985056 : Nat := 2559729817579753179174151

theorem tailTrace_4985056 : CollatzResearch.WordTrace tailWord_4985056 prefixEnd_4985056 2559729817579753179174151 := by
  unfold tailWord_4985056
  simp only [CollatzResearch.WordTrace]
  refine ⟨90909964714000483314051511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 121213286285333977752068681 90909964714000483314051511)
  ·
    refine ⟨136364947071000724971077267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90909964714000483314051511 136364947071000724971077267)
    ·
      refine ⟨204547420606501087456615901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 136364947071000724971077267 204547420606501087456615901)
      ·
        refine ⟨76705282727437907796230963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 204547420606501087456615901 76705282727437907796230963)
        ·
          refine ⟨115057924091156861694346445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 76705282727437907796230963 115057924091156861694346445)
          ·
            refine ⟨43146721534183823135379917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 115057924091156861694346445 43146721534183823135379917)
            ·
              refine ⟨16180020575318933675767469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 43146721534183823135379917 16180020575318933675767469)
              ·
                refine ⟨6067507715744600128412801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16180020575318933675767469 6067507715744600128412801)
                ·
                  refine ⟨4550630786808450096309601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6067507715744600128412801 4550630786808450096309601)
                  ·
                    refine ⟨3412973090106337572232201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4550630786808450096309601 3412973090106337572232201)
                    ·
                      refine ⟨2559729817579753179174151, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3412973090106337572232201 2559729817579753179174151)
                      ·
                        rfl

theorem cell23_4985056_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 3, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 3, 3, 2, 2, 2].length) (baseStart_4985056 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4985056 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4985056 prefixEnd_4985056 := by exact prefixLift 4985056
  have htrace : WordTrace (prefixWord ++ tailWord_4985056) baseStart_4985056 baseEnd_4985056 := by
    simpa [prefixWord, tailWord_4985056, baseEnd_4985056] using wordTrace_append hprefix tailTrace_4985056
  have hstable : (prefixWord ++ tailWord_4985056).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4985056).length < 2 ^ (prefixWord ++ tailWord_4985056).sum := by decide
  have hdescent : baseEnd_4985056 < baseStart_4985056 := by decide
  rcases family_descends (prefixWord ++ tailWord_4985056) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4985090 : List Nat := [3, 4, 1, 1, 2, 2, 2, 2, 2, 2, 2]
def baseStart_4985090 : Nat := 118140960795 + 4985090 * 2 ^ 59
def prefixEnd_4985090 : Nat := 4983230072969 + 3 ^ 40 * 4985090 * 2
def baseEnd_4985090 : Nat := 2559747275922006046148995

theorem tailTrace_4985090 : CollatzResearch.WordTrace tailWord_4985090 prefixEnd_4985090 2559747275922006046148995 := by
  unfold tailWord_4985090
  simp only [CollatzResearch.WordTrace]
  refine ⟨45455292377469447608710181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 121214113006585193623227149 45455292377469447608710181)
  ·
    refine ⟨8522867320775521426633159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 45455292377469447608710181 8522867320775521426633159)
    ·
      refine ⟨12784300981163282139949739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8522867320775521426633159 12784300981163282139949739)
      ·
        refine ⟨19176451471744923209924609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12784300981163282139949739 19176451471744923209924609)
        ·
          refine ⟨14382338603808692407443457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19176451471744923209924609 14382338603808692407443457)
          ·
            refine ⟨10786753952856519305582593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14382338603808692407443457 10786753952856519305582593)
            ·
              refine ⟨8090065464642389479186945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10786753952856519305582593 8090065464642389479186945)
              ·
                refine ⟨6067549098481792109390209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8090065464642389479186945 6067549098481792109390209)
                ·
                  refine ⟨4550661823861344082042657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6067549098481792109390209 4550661823861344082042657)
                  ·
                    refine ⟨3412996367896008061531993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4550661823861344082042657 3412996367896008061531993)
                    ·
                      refine ⟨2559747275922006046148995, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3412996367896008061531993 2559747275922006046148995)
                      ·
                        rfl

theorem cell23_4985090_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 2, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 2, 2, 2, 2, 2, 2].length) (baseStart_4985090 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4985090 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4985090 prefixEnd_4985090 := by exact prefixLift 4985090
  have htrace : WordTrace (prefixWord ++ tailWord_4985090) baseStart_4985090 baseEnd_4985090 := by
    simpa [prefixWord, tailWord_4985090, baseEnd_4985090] using wordTrace_append hprefix tailTrace_4985090
  have hstable : (prefixWord ++ tailWord_4985090).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4985090).length < 2 ^ (prefixWord ++ tailWord_4985090).sum := by decide
  have hdescent : baseEnd_4985090 < baseStart_4985090 := by decide
  rcases family_descends (prefixWord ++ tailWord_4985090) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4985096 : List Nat := [2, 1, 3, 2, 3, 1, 4, 2, 5]
def baseStart_4985096 : Nat := 118140960795 + 4985096 * 2 ^ 59
def prefixEnd_4985096 : Nat := 4983230072969 + 3 ^ 40 * 4985096 * 2
def baseEnd_4985096 : Nat := 284416706311770335852663

theorem tailTrace_4985096 : CollatzResearch.WordTrace tailWord_4985096 prefixEnd_4985096 284416706311770335852663 := by
  unfold tailWord_4985096
  simp only [CollatzResearch.WordTrace]
  refine ⟨90910694173928026729779571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 121214258898570702306372761 90910694173928026729779571)
  ·
    refine ⟨136366041260892040094669357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90910694173928026729779571 136366041260892040094669357)
    ·
      refine ⟨51137265472834515035501009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 136366041260892040094669357 51137265472834515035501009)
      ·
        refine ⟨38352949104625886276625757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 51137265472834515035501009 38352949104625886276625757)
        ·
          refine ⟨14382355914234707353734659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 38352949104625886276625757 14382355914234707353734659)
          ·
            refine ⟨21573533871352061030601989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14382355914234707353734659 21573533871352061030601989)
            ·
              refine ⟨4045037600878511443237873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 21573533871352061030601989 4045037600878511443237873)
              ·
                refine ⟨3033778200658883582428405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4045037600878511443237873 3033778200658883582428405)
                ·
                  refine ⟨284416706311770335852663, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3033778200658883582428405 284416706311770335852663)
                  ·
                    rfl

theorem cell23_4985096_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 1, 4, 2, 5].length) (baseStart_4985096 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4985096 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4985096 prefixEnd_4985096 := by exact prefixLift 4985096
  have htrace : WordTrace (prefixWord ++ tailWord_4985096) baseStart_4985096 baseEnd_4985096 := by
    simpa [prefixWord, tailWord_4985096, baseEnd_4985096] using wordTrace_append hprefix tailTrace_4985096
  have hstable : (prefixWord ++ tailWord_4985096).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4985096).length < 2 ^ (prefixWord ++ tailWord_4985096).sum := by decide
  have hdescent : baseEnd_4985096 < baseStart_4985096 := by decide
  rcases family_descends (prefixWord ++ tailWord_4985096) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4985102 : List Nat := [4, 1, 1, 2, 1, 2, 1, 3, 1, 2, 5]
def baseStart_4985102 : Nat := 118140960795 + 4985102 * 2 ^ 59
def prefixEnd_4985102 : Nat := 4983230072969 + 3 ^ 40 * 4985102 * 2
def baseEnd_4985102 : Nat := 2559753437689859999198939

theorem tailTrace_4985102 : CollatzResearch.WordTrace tailWord_4985102 prefixEnd_4985102 2559753437689859999198939 := by
  unfold tailWord_4985102
  simp only [CollatzResearch.WordTrace]
  refine ⟨22727700898229289560534695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 121214404790556210989518373 22727700898229289560534695)
  ·
    refine ⟨34091551347343934340802043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22727700898229289560534695 34091551347343934340802043)
    ·
      refine ⟨51137327021015901511203065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34091551347343934340802043 51137327021015901511203065)
      ·
        refine ⟨38352995265761926133402299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 51137327021015901511203065 38352995265761926133402299)
        ·
          refine ⟨57529492898642889200103449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38352995265761926133402299 57529492898642889200103449)
          ·
            refine ⟨43147119673982166900077587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 57529492898642889200103449 43147119673982166900077587)
            ·
              refine ⟨64720679510973250350116381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 43147119673982166900077587 64720679510973250350116381)
              ·
                refine ⟨24270254816614968881293643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 64720679510973250350116381 24270254816614968881293643)
                ·
                  refine ⟨36405382224922453321940465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24270254816614968881293643 36405382224922453321940465)
                  ·
                    refine ⟨27304036668691839991455349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 36405382224922453321940465 27304036668691839991455349)
                    ·
                      refine ⟨2559753437689859999198939, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 27304036668691839991455349 2559753437689859999198939)
                      ·
                        rfl

theorem cell23_4985102_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 1, 3, 1, 2, 5].length) (baseStart_4985102 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4985102 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4985102 prefixEnd_4985102 := by exact prefixLift 4985102
  have htrace : WordTrace (prefixWord ++ tailWord_4985102) baseStart_4985102 baseEnd_4985102 := by
    simpa [prefixWord, tailWord_4985102, baseEnd_4985102] using wordTrace_append hprefix tailTrace_4985102
  have hstable : (prefixWord ++ tailWord_4985102).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4985102).length < 2 ^ (prefixWord ++ tailWord_4985102).sum := by decide
  have hdescent : baseEnd_4985102 < baseStart_4985102 := by decide
  rcases family_descends (prefixWord ++ tailWord_4985102) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4985112 : List Nat := [2, 1, 2, 3, 1, 2, 2, 2, 1, 3, 4]
def baseStart_4985112 : Nat := 118140960795 + 4985112 * 2 ^ 59
def prefixEnd_4985112 : Nat := 4983230072969 + 3 ^ 40 * 4985112 * 2
def baseEnd_4985112 : Nat := 2559758572496404960073893

theorem tailTrace_4985112 : CollatzResearch.WordTrace tailWord_4985112 prefixEnd_4985112 2559758572496404960073893 := by
  unfold tailWord_4985112
  simp only [CollatzResearch.WordTrace]
  refine ⟨90910985957899044096070795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 121214647943865392128094393 90910985957899044096070795)
  ·
    refine ⟨136366478936848566144106193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90910985957899044096070795 136366478936848566144106193)
    ·
      refine ⟨102274859202636424608079645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 136366478936848566144106193 102274859202636424608079645)
      ·
        refine ⟨38353072200988659228029867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 102274859202636424608079645 38353072200988659228029867)
        ·
          refine ⟨57529608301482988842044801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38353072200988659228029867 57529608301482988842044801)
          ·
            refine ⟨43147206226112241631533601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 57529608301482988842044801 43147206226112241631533601)
            ·
              refine ⟨32360404669584181223650201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 43147206226112241631533601 32360404669584181223650201)
              ·
                refine ⟨24270303502188135917737651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 32360404669584181223650201 24270303502188135917737651)
                ·
                  refine ⟨36405455253282203876606477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24270303502188135917737651 36405455253282203876606477)
                  ·
                    refine ⟨13652045719980826453727429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 36405455253282203876606477 13652045719980826453727429)
                    ·
                      refine ⟨2559758572496404960073893, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13652045719980826453727429 2559758572496404960073893)
                      ·
                        rfl

theorem cell23_4985112_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 2, 2, 1, 3, 4].length) (baseStart_4985112 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4985112 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4985112 prefixEnd_4985112 := by exact prefixLift 4985112
  have htrace : WordTrace (prefixWord ++ tailWord_4985112) baseStart_4985112 baseEnd_4985112 := by
    simpa [prefixWord, tailWord_4985112, baseEnd_4985112] using wordTrace_append hprefix tailTrace_4985112
  have hstable : (prefixWord ++ tailWord_4985112).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4985112).length < 2 ^ (prefixWord ++ tailWord_4985112).sum := by decide
  have hdescent : baseEnd_4985112 < baseStart_4985112 := by decide
  rcases family_descends (prefixWord ++ tailWord_4985112) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4985152 : List Nat := [2, 1, 1, 2, 2, 1, 2, 6, 6]
def baseStart_4985152 : Nat := 118140960795 + 4985152 * 2 ^ 59
def prefixEnd_4985152 : Nat := 4983230072969 + 3 ^ 40 * 4985152 * 2
def baseEnd_4985152 : Nat := 284419901302509422619301

theorem tailTrace_4985152 : CollatzResearch.WordTrace tailWord_4985152 prefixEnd_4985152 284419901302509422619301 := by
  unfold tailWord_4985152
  simp only [CollatzResearch.WordTrace]
  refine ⟨90911715417826587511798855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 121215620557102116682398473 90911715417826587511798855)
  ·
    refine ⟨136367573126739881267698283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90911715417826587511798855 136367573126739881267698283)
    ·
      refine ⟨204551359690109821901547425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 136367573126739881267698283 204551359690109821901547425)
      ·
        refine ⟨153413519767582366426160569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 204551359690109821901547425 153413519767582366426160569)
        ·
          refine ⟨115060139825686774819620427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 153413519767582366426160569 115060139825686774819620427)
          ·
            refine ⟨172590209738530162229430641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 115060139825686774819620427 172590209738530162229430641)
            ·
              refine ⟨129442657303897621672072981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 172590209738530162229430641 129442657303897621672072981)
              ·
                refine ⟨6067624561120201015878421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 129442657303897621672072981 6067624561120201015878421)
                ·
                  refine ⟨284419901302509422619301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6067624561120201015878421 284419901302509422619301)
                  ·
                    rfl

theorem cell23_4985152_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 2, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 2, 6, 6].length) (baseStart_4985152 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4985152 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4985152 prefixEnd_4985152 := by exact prefixLift 4985152
  have htrace : WordTrace (prefixWord ++ tailWord_4985152) baseStart_4985152 baseEnd_4985152 := by
    simpa [prefixWord, tailWord_4985152, baseEnd_4985152] using wordTrace_append hprefix tailTrace_4985152
  have hstable : (prefixWord ++ tailWord_4985152).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4985152).length < 2 ^ (prefixWord ++ tailWord_4985152).sum := by decide
  have hdescent : baseEnd_4985152 < baseStart_4985152 := by decide
  rcases family_descends (prefixWord ++ tailWord_4985152) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4985212 : List Nat := [2, 2, 2, 1, 1, 1, 2, 1, 5, 6]
def baseStart_4985212 : Nat := 118140960795 + 4985212 * 2 ^ 59
def prefixEnd_4985212 : Nat := 4983230072969 + 3 ^ 40 * 4985212 * 2
def baseEnd_4985212 : Nat := 853269973520618189607811

theorem tailTrace_4985212 : CollatzResearch.WordTrace tailWord_4985212 prefixEnd_4985212 853269973520618189607811 := by
  unfold tailWord_4985212
  simp only [CollatzResearch.WordTrace]
  refine ⟨90912809607717902635390945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 121217079476957203513854593 90912809607717902635390945)
  ·
    refine ⟨68184607205788426976543209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 90912809607717902635390945 68184607205788426976543209)
    ·
      refine ⟨51138455404341320232407407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 68184607205788426976543209 51138455404341320232407407)
      ·
        refine ⟨76707683106511980348611111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51138455404341320232407407 76707683106511980348611111)
        ·
          refine ⟨115061524659767970522916667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 76707683106511980348611111 115061524659767970522916667)
          ·
            refine ⟨172592286989651955784375001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 115061524659767970522916667 172592286989651955784375001)
            ·
              refine ⟨129444215242238966838281251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 172592286989651955784375001 129444215242238966838281251)
              ·
                refine ⟨194166322863358450257421877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 129444215242238966838281251 194166322863358450257421877)
                ·
                  refine ⟨18203092768439854711633301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 194166322863358450257421877 18203092768439854711633301)
                  ·
                    refine ⟨853269973520618189607811, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 18203092768439854711633301 853269973520618189607811)
                    ·
                      rfl

theorem cell23_4985212_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 2, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 2, 1, 5, 6].length) (baseStart_4985212 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4985212 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4985212 prefixEnd_4985212 := by exact prefixLift 4985212
  have htrace : WordTrace (prefixWord ++ tailWord_4985212) baseStart_4985212 baseEnd_4985212 := by
    simpa [prefixWord, tailWord_4985212, baseEnd_4985212] using wordTrace_append hprefix tailTrace_4985212
  have hstable : (prefixWord ++ tailWord_4985212).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4985212).length < 2 ^ (prefixWord ++ tailWord_4985212).sum := by decide
  have hdescent : baseEnd_4985212 < baseStart_4985212 := by decide
  rcases family_descends (prefixWord ++ tailWord_4985212) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4985213 : List Nat := [1, 4, 1, 1, 2, 5, 1, 1, 3, 1, 3]
def baseStart_4985213 : Nat := 118140960795 + 4985213 * 2 ^ 59
def prefixEnd_4985213 : Nat := 4983230072969 + 3 ^ 40 * 4985213 * 2
def baseEnd_4985213 : Nat := 2559810434042509064910929

theorem tailTrace_4985213 : CollatzResearch.WordTrace tailWord_4985213 prefixEnd_4985213 2559810434042509064910929 := by
  unfold tailWord_4985213
  simp only [CollatzResearch.WordTrace]
  refine ⟨181825655688432182441568293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121217103792288121627712195 181825655688432182441568293)
  ·
    refine ⟨34092310441581034207794055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 181825655688432182441568293 34092310441581034207794055)
    ·
      refine ⟨51138465662371551311691083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34092310441581034207794055 51138465662371551311691083)
      ·
        refine ⟨76707698493557326967536625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51138465662371551311691083 76707698493557326967536625)
        ·
          refine ⟨57530773870167995225652469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 76707698493557326967536625 57530773870167995225652469)
          ·
            refine ⟨5393510050328249552404919, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 57530773870167995225652469 5393510050328249552404919)
            ·
              refine ⟨8090265075492374328607379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5393510050328249552404919 8090265075492374328607379)
              ·
                refine ⟨12135397613238561492911069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8090265075492374328607379 12135397613238561492911069)
                ·
                  refine ⟨4550774104964460559841651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12135397613238561492911069 4550774104964460559841651)
                  ·
                    refine ⟨6826161157446690839762477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4550774104964460559841651 6826161157446690839762477)
                    ·
                      refine ⟨2559810434042509064910929, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6826161157446690839762477 2559810434042509064910929)
                      ·
                        rfl

theorem cell23_4985213_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 5, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 5, 1, 1, 3, 1, 3].length) (baseStart_4985213 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4985213 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4985213 prefixEnd_4985213 := by exact prefixLift 4985213
  have htrace : WordTrace (prefixWord ++ tailWord_4985213) baseStart_4985213 baseEnd_4985213 := by
    simpa [prefixWord, tailWord_4985213, baseEnd_4985213] using wordTrace_append hprefix tailTrace_4985213
  have hstable : (prefixWord ++ tailWord_4985213).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4985213).length < 2 ^ (prefixWord ++ tailWord_4985213).sum := by decide
  have hdescent : baseEnd_4985213 < baseStart_4985213 := by decide
  rcases family_descends (prefixWord ++ tailWord_4985213) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4985246 : List Nat := [4, 3, 1, 2, 1, 1, 1, 1, 3, 6]
def baseStart_4985246 : Nat := 118140960795 + 4985246 * 2 ^ 59
def prefixEnd_4985246 : Nat := 4983230072969 + 3 ^ 40 * 4985246 * 2
def baseEnd_4985246 : Nat := 853275792968035811932759

theorem tailTrace_4985246 : CollatzResearch.WordTrace tailWord_4985246 prefixEnd_4985246 853275792968035811932759 := by
  unfold tailWord_4985246
  simp only [CollatzResearch.WordTrace]
  refine ⟨22728357412164078634689949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 121217906198208419385013061 22728357412164078634689949)
  ·
    refine ⟨8523134029561529488008731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 22728357412164078634689949 8523134029561529488008731)
    ·
      refine ⟨12784701044342294232013097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8523134029561529488008731 12784701044342294232013097)
      ·
        refine ⟨9588525783256720674009823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12784701044342294232013097 9588525783256720674009823)
        ·
          refine ⟨14382788674885081011014735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9588525783256720674009823 14382788674885081011014735)
          ·
            refine ⟨21574183012327621516522103, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14382788674885081011014735 21574183012327621516522103)
            ·
              refine ⟨32361274518491432274783155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21574183012327621516522103 32361274518491432274783155)
              ·
                refine ⟨48541911777737148412174733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32361274518491432274783155 48541911777737148412174733)
                ·
                  refine ⟨18203216916651430654565525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 48541911777737148412174733 18203216916651430654565525)
                  ·
                    refine ⟨853275792968035811932759, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 18203216916651430654565525 853275792968035811932759)
                    ·
                      rfl

theorem cell23_4985246_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 1, 1, 1, 3, 6].length) (baseStart_4985246 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4985246 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4985246 prefixEnd_4985246 := by exact prefixLift 4985246
  have htrace : WordTrace (prefixWord ++ tailWord_4985246) baseStart_4985246 baseEnd_4985246 := by
    simpa [prefixWord, tailWord_4985246, baseEnd_4985246] using wordTrace_append hprefix tailTrace_4985246
  have hstable : (prefixWord ++ tailWord_4985246).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4985246).length < 2 ^ (prefixWord ++ tailWord_4985246).sum := by decide
  have hdescent : baseEnd_4985246 < baseStart_4985246 := by decide
  rcases family_descends (prefixWord ++ tailWord_4985246) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4985276 : List Nat := [2, 2, 2, 4, 1, 3, 1, 8]
def baseStart_4985276 : Nat := 118140960795 + 4985276 * 2 ^ 59
def prefixEnd_4985276 : Nat := 4983230072969 + 3 ^ 40 * 4985276 * 2
def baseEnd_4985276 : Nat := 94808991974953419200857

theorem tailTrace_4985276 : CollatzResearch.WordTrace tailWord_4985276 prefixEnd_4985276 94808991974953419200857 := by
  unfold tailWord_4985276
  simp only [CollatzResearch.WordTrace]
  refine ⟨90913976743601972100555841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 121218635658135962800741121 90913976743601972100555841)
  ·
    refine ⟨68185482557701479075416881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 90913976743601972100555841 68185482557701479075416881)
    ·
      refine ⟨51139111918276109306562661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 68185482557701479075416881 51139111918276109306562661)
      ·
        refine ⟨9588583484676770494980499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 51139111918276109306562661 9588583484676770494980499)
        ·
          refine ⟨14382875227015155742470749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9588583484676770494980499 14382875227015155742470749)
          ·
            refine ⟨5393578210130683403426531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14382875227015155742470749 5393578210130683403426531)
            ·
              refine ⟨8090367315196025105139797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5393578210130683403426531 8090367315196025105139797)
              ·
                refine ⟨94808991974953419200857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 8090367315196025105139797 94808991974953419200857)
                ·
                  rfl

theorem cell23_4985276_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 3, 1, 8].length) (baseStart_4985276 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4985276 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4985276 prefixEnd_4985276 := by exact prefixLift 4985276
  have htrace : WordTrace (prefixWord ++ tailWord_4985276) baseStart_4985276 baseEnd_4985276 := by
    simpa [prefixWord, tailWord_4985276, baseEnd_4985276] using wordTrace_append hprefix tailTrace_4985276
  have hstable : (prefixWord ++ tailWord_4985276).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4985276).length < 2 ^ (prefixWord ++ tailWord_4985276).sum := by decide
  have hdescent : baseEnd_4985276 < baseStart_4985276 := by decide
  rcases family_descends (prefixWord ++ tailWord_4985276) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4985313 : List Nat := [1, 2, 3, 1, 2, 2, 3, 3, 1, 3, 2]
def baseStart_4985313 : Nat := 118140960795 + 4985313 * 2 ^ 59
def prefixEnd_4985313 : Nat := 4983230072969 + 3 ^ 40 * 4985313 * 2
def baseEnd_4985313 : Nat := 2559861782107958673660469

theorem tailTrace_4985313 : CollatzResearch.WordTrace tailWord_4985313 prefixEnd_4985313 2559861782107958673660469 := by
  unfold tailWord_4985313
  simp only [CollatzResearch.WordTrace]
  refine ⟨181829302988069899520208593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121219535325379933013472395 181829302988069899520208593)
  ·
    refine ⟨136371977241052424640156445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 181829302988069899520208593 136371977241052424640156445)
    ·
      refine ⟨51139491465394659240058667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 136371977241052424640156445 51139491465394659240058667)
      ·
        refine ⟨76709237198091988860088001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51139491465394659240058667 76709237198091988860088001)
        ·
          refine ⟨57531927898568991645066001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 76709237198091988860088001 57531927898568991645066001)
          ·
            refine ⟨43148945923926743733799501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 57531927898568991645066001 43148945923926743733799501)
            ·
              refine ⟨16180854721472528900174813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 43148945923926743733799501 16180854721472528900174813)
              ·
                refine ⟨6067820520552198337565555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16180854721472528900174813 6067820520552198337565555)
                ·
                  refine ⟨9101730780828297506348333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6067820520552198337565555 9101730780828297506348333)
                  ·
                    refine ⟨3413149042810611564880625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9101730780828297506348333 3413149042810611564880625)
                    ·
                      refine ⟨2559861782107958673660469, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3413149042810611564880625 2559861782107958673660469)
                      ·
                        rfl

theorem cell23_4985313_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 3, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 3, 3, 1, 3, 2].length) (baseStart_4985313 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4985313 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4985313 prefixEnd_4985313 := by exact prefixLift 4985313
  have htrace : WordTrace (prefixWord ++ tailWord_4985313) baseStart_4985313 baseEnd_4985313 := by
    simpa [prefixWord, tailWord_4985313, baseEnd_4985313] using wordTrace_append hprefix tailTrace_4985313
  have hstable : (prefixWord ++ tailWord_4985313).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4985313).length < 2 ^ (prefixWord ++ tailWord_4985313).sum := by decide
  have hdescent : baseEnd_4985313 < baseStart_4985313 := by decide
  rcases family_descends (prefixWord ++ tailWord_4985313) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4985314 : List Nat := [3, 3, 3, 2, 2, 1, 1, 2, 2, 4]
def baseStart_4985314 : Nat := 118140960795 + 4985314 * 2 ^ 59
def prefixEnd_4985314 : Nat := 4983230072969 + 3 ^ 40 * 4985314 * 2
def baseEnd_4985314 : Nat := 853287431862871056582655

theorem tailTrace_4985314 : CollatzResearch.WordTrace tailWord_4985314 prefixEnd_4985314 853287431862871056582655 := by
  unfold tailWord_4985314
  simp only [CollatzResearch.WordTrace]
  refine ⟨45457334865266569172748749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 121219559640710851127329997 45457334865266569172748749)
  ·
    refine ⟨17046500574474963439780781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 45457334865266569172748749 17046500574474963439780781)
    ·
      refine ⟨6392437715428111289917793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17046500574474963439780781 6392437715428111289917793)
      ·
        refine ⟨4794328286571083467438345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6392437715428111289917793 4794328286571083467438345)
        ·
          refine ⟨3595746214928312600578759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4794328286571083467438345 3595746214928312600578759)
          ·
            refine ⟨5393619322392468900868139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3595746214928312600578759 5393619322392468900868139)
            ·
              refine ⟨8090428983588703351302209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5393619322392468900868139 8090428983588703351302209)
              ·
                refine ⟨6067821737691527513476657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8090428983588703351302209 6067821737691527513476657)
                ·
                  refine ⟨4550866303268645635107493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6067821737691527513476657 4550866303268645635107493)
                  ·
                    refine ⟨853287431862871056582655, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4550866303268645635107493 853287431862871056582655)
                    ·
                      rfl

theorem cell23_4985314_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 2, 2, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 2, 2, 1, 1, 2, 2, 4].length) (baseStart_4985314 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4985314 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4985314 prefixEnd_4985314 := by exact prefixLift 4985314
  have htrace : WordTrace (prefixWord ++ tailWord_4985314) baseStart_4985314 baseEnd_4985314 := by
    simpa [prefixWord, tailWord_4985314, baseEnd_4985314] using wordTrace_append hprefix tailTrace_4985314
  have hstable : (prefixWord ++ tailWord_4985314).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4985314).length < 2 ^ (prefixWord ++ tailWord_4985314).sum := by decide
  have hdescent : baseEnd_4985314 < baseStart_4985314 := by decide
  rcases family_descends (prefixWord ++ tailWord_4985314) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4985319 : List Nat := [1, 1, 5, 2, 1, 1, 1, 1, 4, 6]
def baseStart_4985319 : Nat := 118140960795 + 4985319 * 2 ^ 59
def prefixEnd_4985319 : Nat := 4983230072969 + 3 ^ 40 * 4985319 * 2
def baseEnd_4985319 : Nat := 853288287663961883395147

theorem tailTrace_4985319 : CollatzResearch.WordTrace tailWord_4985319 prefixEnd_4985319 853288287663961883395147 := by
  unfold tailWord_4985319
  simp only [CollatzResearch.WordTrace]
  refine ⟨181829521826048162544927011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121219681217365441696618007 181829521826048162544927011)
  ·
    refine ⟨272744282739072243817390517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 181829521826048162544927011 272744282739072243817390517)
    ·
      refine ⟨25569776506788022857880361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 272744282739072243817390517 25569776506788022857880361)
      ·
        refine ⟨19177332380091017143410271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25569776506788022857880361 19177332380091017143410271)
        ·
          refine ⟨28765998570136525715115407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19177332380091017143410271 28765998570136525715115407)
          ·
            refine ⟨43148997855204788572673111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28765998570136525715115407 43148997855204788572673111)
            ·
              refine ⟨64723496782807182859009667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 43148997855204788572673111 64723496782807182859009667)
              ·
                refine ⟨97085245174210774288514501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 64723496782807182859009667 97085245174210774288514501)
                ·
                  refine ⟨18203483470164520179096469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 97085245174210774288514501 18203483470164520179096469)
                  ·
                    refine ⟨853288287663961883395147, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 18203483470164520179096469 853288287663961883395147)
                    ·
                      rfl

theorem cell23_4985319_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 1, 1, 4, 6].length) (baseStart_4985319 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4985319 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4985319 prefixEnd_4985319 := by exact prefixLift 4985319
  have htrace : WordTrace (prefixWord ++ tailWord_4985319) baseStart_4985319 baseEnd_4985319 := by
    simpa [prefixWord, tailWord_4985319, baseEnd_4985319] using wordTrace_append hprefix tailTrace_4985319
  have hstable : (prefixWord ++ tailWord_4985319).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4985319).length < 2 ^ (prefixWord ++ tailWord_4985319).sum := by decide
  have hdescent : baseEnd_4985319 < baseStart_4985319 := by decide
  rcases family_descends (prefixWord ++ tailWord_4985319) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4985320 : List Nat := [2, 1, 4, 1, 1, 5, 1, 2, 2, 1, 3]
def baseStart_4985320 : Nat := 118140960795 + 4985320 * 2 ^ 59
def prefixEnd_4985320 : Nat := 4983230072969 + 3 ^ 40 * 4985320 * 2
def baseEnd_4985320 : Nat := 2559865376472540146272937

theorem tailTrace_4985320 : CollatzResearch.WordTrace tailWord_4985320 prefixEnd_4985320 2559865376472540146272937 := by
  unfold tailWord_4985320
  simp only [CollatzResearch.WordTrace]
  refine ⟨90914779149522269857856707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 121219705532696359810475609 90914779149522269857856707)
  ·
    refine ⟨136372168724283404786785061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90914779149522269857856707 136372168724283404786785061)
    ·
      refine ⟨25569781635803138397522199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 136372168724283404786785061 25569781635803138397522199)
      ·
        refine ⟨38354672453704707596283299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25569781635803138397522199 38354672453704707596283299)
        ·
          refine ⟨57532008680557061394424949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38354672453704707596283299 57532008680557061394424949)
          ·
            refine ⟨5393625813802224505727339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 57532008680557061394424949 5393625813802224505727339)
            ·
              refine ⟨8090438720703336758591009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5393625813802224505727339 8090438720703336758591009)
              ·
                refine ⟨6067829040527502568943257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8090438720703336758591009 6067829040527502568943257)
                ·
                  refine ⟨4550871780395626926707443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6067829040527502568943257 4550871780395626926707443)
                  ·
                    refine ⟨6826307670593440390061165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4550871780395626926707443 6826307670593440390061165)
                    ·
                      refine ⟨2559865376472540146272937, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6826307670593440390061165 2559865376472540146272937)
                      ·
                        rfl

theorem cell23_4985320_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 5, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 5, 1, 2, 2, 1, 3].length) (baseStart_4985320 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4985320 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4985320 prefixEnd_4985320 := by exact prefixLift 4985320
  have htrace : WordTrace (prefixWord ++ tailWord_4985320) baseStart_4985320 baseEnd_4985320 := by
    simpa [prefixWord, tailWord_4985320, baseEnd_4985320] using wordTrace_append hprefix tailTrace_4985320
  have hstable : (prefixWord ++ tailWord_4985320).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4985320).length < 2 ^ (prefixWord ++ tailWord_4985320).sum := by decide
  have hdescent : baseEnd_4985320 < baseStart_4985320 := by decide
  rcases family_descends (prefixWord ++ tailWord_4985320) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4985349 : List Nat := [1, 3, 1, 1, 2, 2, 4, 2, 7]
def baseStart_4985349 : Nat := 118140960795 + 4985349 * 2 ^ 59
def prefixEnd_4985349 : Nat := 4983230072969 + 3 ^ 40 * 4985349 * 2
def baseEnd_4985349 : Nat := 284431140823502281423367

theorem tailTrace_4985349 : CollatzResearch.WordTrace tailWord_4985349 prefixEnd_4985349 284431140823502281423367 := by
  unfold tailWord_4985349
  simp only [CollatzResearch.WordTrace]
  refine ⟨181830616015939477668519101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121220410677292985112346067 181830616015939477668519101)
  ·
    refine ⟨68186481005977304125694663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 181830616015939477668519101 68186481005977304125694663)
    ·
      refine ⟨102279721508965956188541995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68186481005977304125694663 102279721508965956188541995)
      ·
        refine ⟨153419582263448934282812993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 102279721508965956188541995 153419582263448934282812993)
        ·
          refine ⟨115064686697586700712109745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 153419582263448934282812993 115064686697586700712109745)
          ·
            refine ⟨86298515023190025534082309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 115064686697586700712109745 86298515023190025534082309)
            ·
              refine ⟨16180971566848129787640433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 86298515023190025534082309 16180971566848129787640433)
              ·
                refine ⟨12135728675136097340730325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16180971566848129787640433 12135728675136097340730325)
                ·
                  refine ⟨284431140823502281423367, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 12135728675136097340730325 284431140823502281423367)
                  ·
                    rfl

theorem cell23_4985349_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 4, 2, 7].length) (baseStart_4985349 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4985349 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4985349 prefixEnd_4985349 := by exact prefixLift 4985349
  have htrace : WordTrace (prefixWord ++ tailWord_4985349) baseStart_4985349 baseEnd_4985349 := by
    simpa [prefixWord, tailWord_4985349, baseEnd_4985349] using wordTrace_append hprefix tailTrace_4985349
  have hstable : (prefixWord ++ tailWord_4985349).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4985349).length < 2 ^ (prefixWord ++ tailWord_4985349).sum := by decide
  have hdescent : baseEnd_4985349 < baseStart_4985349 := by decide
  rcases family_descends (prefixWord ++ tailWord_4985349) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4985350 : List Nat := [6, 2, 1, 1, 1, 1, 1, 1, 2, 2, 5]
def baseStart_4985350 : Nat := 118140960795 + 4985350 * 2 ^ 59
def prefixEnd_4985350 : Nat := 4983230072969 + 3 ^ 40 * 4985350 * 2
def baseEnd_4985350 : Nat := 2559880780892175028897799

theorem tailTrace_4985350 : CollatzResearch.WordTrace tailWord_4985350 prefixEnd_4985350 2559880780892175028897799 := by
  unfold tailWord_4985350
  simp only [CollatzResearch.WordTrace]
  refine ⟨5682207890279245463728297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 121220434992623903226203669 5682207890279245463728297)
  ·
    refine ⟨4261655917709434097796223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5682207890279245463728297 4261655917709434097796223)
    ·
      refine ⟨6392483876564151146694335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4261655917709434097796223 6392483876564151146694335)
      ·
        refine ⟨9588725814846226720041503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6392483876564151146694335 9588725814846226720041503)
        ·
          refine ⟨14383088722269340080062255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9588725814846226720041503 14383088722269340080062255)
          ·
            refine ⟨21574633083404010120093383, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14383088722269340080062255 21574633083404010120093383)
            ·
              refine ⟨32361949625106015180140075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21574633083404010120093383 32361949625106015180140075)
              ·
                refine ⟨48542924437659022770210113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32361949625106015180140075 48542924437659022770210113)
                ·
                  refine ⟨36407193328244267077657585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 48542924437659022770210113 36407193328244267077657585)
                  ·
                    refine ⟨27305394996183200308243189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 36407193328244267077657585 27305394996183200308243189)
                    ·
                      refine ⟨2559880780892175028897799, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 27305394996183200308243189 2559880780892175028897799)
                      ·
                        rfl

theorem cell23_4985350_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 1, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 1, 1, 1, 2, 2, 5].length) (baseStart_4985350 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4985350 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4985350 prefixEnd_4985350 := by exact prefixLift 4985350
  have htrace : WordTrace (prefixWord ++ tailWord_4985350) baseStart_4985350 baseEnd_4985350 := by
    simpa [prefixWord, tailWord_4985350, baseEnd_4985350] using wordTrace_append hprefix tailTrace_4985350
  have hstable : (prefixWord ++ tailWord_4985350).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4985350).length < 2 ^ (prefixWord ++ tailWord_4985350).sum := by decide
  have hdescent : baseEnd_4985350 < baseStart_4985350 := by decide
  rcases family_descends (prefixWord ++ tailWord_4985350) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4985359 : List Nat := [1, 1, 2, 1, 1, 1, 2, 3, 3, 5, 3]
def baseStart_4985359 : Nat := 118140960795 + 4985359 * 2 ^ 59
def prefixEnd_4985359 : Nat := 4983230072969 + 3 ^ 40 * 4985359 * 2
def baseEnd_4985359 : Nat := 2559885402218065493685257

theorem tailTrace_4985359 : CollatzResearch.WordTrace tailWord_4985359 prefixEnd_4985359 2559885402218065493685257 := by
  unfold tailWord_4985359
  simp only [CollatzResearch.WordTrace]
  refine ⟨181830980745903249376383131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121220653830602166250922087 181830980745903249376383131)
  ·
    refine ⟨272746471118854874064574697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 181830980745903249376383131 272746471118854874064574697)
    ·
      refine ⟨204559853339141155548431023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 272746471118854874064574697 204559853339141155548431023)
      ·
        refine ⟨306839780008711733322646535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 204559853339141155548431023 306839780008711733322646535)
        ·
          refine ⟨460259670013067599983969803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 306839780008711733322646535 460259670013067599983969803)
          ·
            refine ⟨690389505019601399975954705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 460259670013067599983969803 690389505019601399975954705)
            ·
              refine ⟨517792128764701049981966029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 690389505019601399975954705 517792128764701049981966029)
              ·
                refine ⟨194172048286762893743237261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 517792128764701049981966029 194172048286762893743237261)
                ·
                  refine ⟨72814518107536085153713973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 194172048286762893743237261 72814518107536085153713973)
                  ·
                    refine ⟨6826361072581507983160685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 72814518107536085153713973 6826361072581507983160685)
                    ·
                      refine ⟨2559885402218065493685257, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6826361072581507983160685 2559885402218065493685257)
                      ·
                        rfl

theorem cell23_4985359_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 3, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 3, 3, 5, 3].length) (baseStart_4985359 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4985359 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4985359 prefixEnd_4985359 := by exact prefixLift 4985359
  have htrace : WordTrace (prefixWord ++ tailWord_4985359) baseStart_4985359 baseEnd_4985359 := by
    simpa [prefixWord, tailWord_4985359, baseEnd_4985359] using wordTrace_append hprefix tailTrace_4985359
  have hstable : (prefixWord ++ tailWord_4985359).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4985359).length < 2 ^ (prefixWord ++ tailWord_4985359).sum := by decide
  have hdescent : baseEnd_4985359 < baseStart_4985359 := by decide
  rcases family_descends (prefixWord ++ tailWord_4985359) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4985439 : List Nat := [1, 1, 2, 3, 1, 1, 1, 5, 8]
def baseStart_4985439 : Nat := 118140960795 + 4985439 * 2 ^ 59
def prefixEnd_4985439 : Nat := 4983230072969 + 3 ^ 40 * 4985439 * 2
def baseEnd_4985439 : Nat := 284436275630047242298321

theorem tailTrace_4985439 : CollatzResearch.WordTrace tailWord_4985439 prefixEnd_4985439 284436275630047242298321 := by
  unfold tailWord_4985439
  simp only [CollatzResearch.WordTrace]
  refine ⟨181833898585613423039295371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121222599057075615359530247 181833898585613423039295371)
  ·
    refine ⟨272750847878420134558943057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 181833898585613423039295371 272750847878420134558943057)
    ·
      refine ⟨204563135908815100919207293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 272750847878420134558943057 204563135908815100919207293)
      ·
        refine ⟨76711175965805662844702735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 204563135908815100919207293 76711175965805662844702735)
        ·
          refine ⟨115066763948708494267054103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 76711175965805662844702735 115066763948708494267054103)
          ·
            refine ⟨172600145923062741400581155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 115066763948708494267054103 172600145923062741400581155)
            ·
              refine ⟨258900218884594112100871733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 172600145923062741400581155 258900218884594112100871733)
              ·
                refine ⟨24271895520430698009456725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 258900218884594112100871733 24271895520430698009456725)
                ·
                  refine ⟨284436275630047242298321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 24271895520430698009456725 284436275630047242298321)
                  ·
                    rfl

theorem cell23_4985439_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 1, 5, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 1, 5, 8].length) (baseStart_4985439 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4985439 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4985439 prefixEnd_4985439 := by exact prefixLift 4985439
  have htrace : WordTrace (prefixWord ++ tailWord_4985439) baseStart_4985439 baseEnd_4985439 := by
    simpa [prefixWord, tailWord_4985439, baseEnd_4985439] using wordTrace_append hprefix tailTrace_4985439
  have hstable : (prefixWord ++ tailWord_4985439).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4985439).length < 2 ^ (prefixWord ++ tailWord_4985439).sum := by decide
  have hdescent : baseEnd_4985439 < baseStart_4985439 := by decide
  rcases family_descends (prefixWord ++ tailWord_4985439) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4985459 : List Nat := [1, 1, 1, 2, 2, 1, 1, 3, 3, 2, 6]
def baseStart_4985459 : Nat := 118140960795 + 4985459 * 2 ^ 59
def prefixEnd_4985459 : Nat := 4983230072969 + 3 ^ 40 * 4985459 * 2
def baseEnd_4985459 : Nat := 2559936750283515102434797

theorem tailTrace_4985459 : CollatzResearch.WordTrace tailWord_4985459 prefixEnd_4985459 2559936750283515102434797 := by
  unfold tailWord_4985459
  simp only [CollatzResearch.WordTrace]
  refine ⟨181834628045540966455023431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121223085363693977636682287 181834628045540966455023431)
  ·
    refine ⟨272751942068311449682535147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 181834628045540966455023431 272751942068311449682535147)
    ·
      refine ⟨409127913102467174523802721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 272751942068311449682535147 409127913102467174523802721)
      ·
        refine ⟨306845934826850380892852041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 409127913102467174523802721 306845934826850380892852041)
        ·
          refine ⟨230134451120137785669639031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 306845934826850380892852041 230134451120137785669639031)
          ·
            refine ⟨345201676680206678504458547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 230134451120137785669639031 345201676680206678504458547)
            ·
              refine ⟨517802515020310017756687821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 345201676680206678504458547 517802515020310017756687821)
              ·
                refine ⟨194175943132616256658757933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 517802515020310017756687821 194175943132616256658757933)
                ·
                  refine ⟨72815978674731096247034225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 194175943132616256658757933 72815978674731096247034225)
                  ·
                    refine ⟨54611984006048322185275669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 72815978674731096247034225 54611984006048322185275669)
                    ·
                      refine ⟨2559936750283515102434797, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 54611984006048322185275669 2559936750283515102434797)
                      ·
                        rfl

theorem cell23_4985459_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 3, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 3, 3, 2, 6].length) (baseStart_4985459 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4985459 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4985459 prefixEnd_4985459 := by exact prefixLift 4985459
  have htrace : WordTrace (prefixWord ++ tailWord_4985459) baseStart_4985459 baseEnd_4985459 := by
    simpa [prefixWord, tailWord_4985459, baseEnd_4985459] using wordTrace_append hprefix tailTrace_4985459
  have hstable : (prefixWord ++ tailWord_4985459).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4985459).length < 2 ^ (prefixWord ++ tailWord_4985459).sum := by decide
  have hdescent : baseEnd_4985459 < baseStart_4985459 := by decide
  rcases family_descends (prefixWord ++ tailWord_4985459) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4985490 : List Nat := [3, 2, 3, 1, 2, 3, 1, 2, 6]
def baseStart_4985490 : Nat := 118140960795 + 4985490 * 2 ^ 59
def prefixEnd_4985490 : Nat := 4983230072969 + 3 ^ 40 * 4985490 * 2
def baseEnd_4985490 : Nat := 284439185353756053460795

theorem tailTrace_4985490 : CollatzResearch.WordTrace tailWord_4985490 prefixEnd_4985490 284439185353756053460795 := by
  unfold tailWord_4985490
  simp only [CollatzResearch.WordTrace]
  refine ⟨45458939677107164687350481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 121223839138952439166267949 45458939677107164687350481)
  ·
    refine ⟨34094204757830373515512861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45458939677107164687350481 34094204757830373515512861)
    ·
      refine ⟨12785326784186390068317323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 34094204757830373515512861 12785326784186390068317323)
      ·
        refine ⟨19177990176279585102475985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12785326784186390068317323 19177990176279585102475985)
        ·
          refine ⟨14383492632209688826856989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19177990176279585102475985 14383492632209688826856989)
          ·
            refine ⟨5393809737078633310071371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14383492632209688826856989 5393809737078633310071371)
            ·
              refine ⟨8090714605617949965107057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5393809737078633310071371 8090714605617949965107057)
              ·
                refine ⟨6068035954213462473830293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8090714605617949965107057 6068035954213462473830293)
                ·
                  refine ⟨284439185353756053460795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6068035954213462473830293 284439185353756053460795)
                  ·
                    rfl

theorem cell23_4985490_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 3, 1, 2, 6].length) (baseStart_4985490 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4985490 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4985490 prefixEnd_4985490 := by exact prefixLift 4985490
  have htrace : WordTrace (prefixWord ++ tailWord_4985490) baseStart_4985490 baseEnd_4985490 := by
    simpa [prefixWord, tailWord_4985490, baseEnd_4985490] using wordTrace_append hprefix tailTrace_4985490
  have hstable : (prefixWord ++ tailWord_4985490).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4985490).length < 2 ^ (prefixWord ++ tailWord_4985490).sum := by decide
  have hdescent : baseEnd_4985490 < baseStart_4985490 := by decide
  rcases family_descends (prefixWord ++ tailWord_4985490) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4985500 : List Nat := [2, 2, 3, 2, 2, 1, 1, 3, 3, 1, 3]
def baseStart_4985500 : Nat := 118140960795 + 4985500 * 2 ^ 59
def prefixEnd_4985500 : Nat := 4983230072969 + 3 ^ 40 * 4985500 * 2
def baseEnd_4985500 : Nat := 2559957802990349442022109

theorem tailTrace_4985500 : CollatzResearch.WordTrace tailWord_4985500 prefixEnd_4985500 2559957802990349442022109 := by
  unfold tailWord_4985500
  simp only [CollatzResearch.WordTrace]
  refine ⟨90918061719196215228632977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 121224082292261620304843969 90918061719196215228632977)
  ·
    refine ⟨68188546289397161421474733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 90918061719196215228632977 68188546289397161421474733)
    ·
      refine ⟨25570704858523935533053025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 68188546289397161421474733 25570704858523935533053025)
      ·
        refine ⟨19178028643892951649789769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25570704858523935533053025 19178028643892951649789769)
        ·
          refine ⟨14383521482919713737342327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19178028643892951649789769 14383521482919713737342327)
          ·
            refine ⟨21575282224379570606013491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14383521482919713737342327 21575282224379570606013491)
            ·
              refine ⟨32362923336569355909020237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21575282224379570606013491 32362923336569355909020237)
              ·
                refine ⟨12136096251213508465882589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 32362923336569355909020237 12136096251213508465882589)
                ·
                  refine ⟨4551036094205065674705971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12136096251213508465882589 4551036094205065674705971)
                  ·
                    refine ⟨6826554141307598512058957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4551036094205065674705971 6826554141307598512058957)
                    ·
                      refine ⟨2559957802990349442022109, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6826554141307598512058957 2559957802990349442022109)
                      ·
                        rfl

theorem cell23_4985500_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 1, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 1, 1, 3, 3, 1, 3].length) (baseStart_4985500 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4985500 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4985500 prefixEnd_4985500 := by exact prefixLift 4985500
  have htrace : WordTrace (prefixWord ++ tailWord_4985500) baseStart_4985500 baseEnd_4985500 := by
    simpa [prefixWord, tailWord_4985500, baseEnd_4985500] using wordTrace_append hprefix tailTrace_4985500
  have hstable : (prefixWord ++ tailWord_4985500).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4985500).length < 2 ^ (prefixWord ++ tailWord_4985500).sum := by decide
  have hdescent : baseEnd_4985500 < baseStart_4985500 := by decide
  rcases family_descends (prefixWord ++ tailWord_4985500) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4985523 : List Nat := [1, 1, 1, 2, 3, 4, 1, 4, 1, 1, 4]
def baseStart_4985523 : Nat := 118140960795 + 4985523 * 2 ^ 59
def prefixEnd_4985523 : Nat := 4983230072969 + 3 ^ 40 * 4985523 * 2
def baseEnd_4985523 : Nat := 2559969613045402852034503

theorem tailTrace_4985523 : CollatzResearch.WordTrace tailWord_4985523 prefixEnd_4985523 2559969613045402852034503 := by
  unfold tailWord_4985523
  simp only [CollatzResearch.WordTrace]
  refine ⟨181836962317309105385353223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121224641544872736923568815 181836962317309105385353223)
  ·
    refine ⟨272755443475963658078029835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 181836962317309105385353223 272755443475963658078029835)
    ·
      refine ⟨409133165213945487117044753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 272755443475963658078029835 409133165213945487117044753)
      ·
        refine ⟨306849873910459115337783565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 409133165213945487117044753 306849873910459115337783565)
        ·
          refine ⟨115068702716422168251668837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 306849873910459115337783565 115068702716422168251668837)
          ·
            refine ⟨21575381759329156547187907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 115068702716422168251668837 21575381759329156547187907)
            ·
              refine ⟨32363072638993734820781861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21575381759329156547187907 32363072638993734820781861)
              ·
                refine ⟨6068076119811325278896599, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 32363072638993734820781861 6068076119811325278896599)
                ·
                  refine ⟨9102114179716987918344899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6068076119811325278896599 9102114179716987918344899)
                  ·
                    refine ⟨13653171269575481877517349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9102114179716987918344899 13653171269575481877517349)
                    ·
                      refine ⟨2559969613045402852034503, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13653171269575481877517349 2559969613045402852034503)
                      ·
                        rfl

theorem cell23_4985523_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 4, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 4, 1, 4, 1, 1, 4].length) (baseStart_4985523 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4985523 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4985523 prefixEnd_4985523 := by exact prefixLift 4985523
  have htrace : WordTrace (prefixWord ++ tailWord_4985523) baseStart_4985523 baseEnd_4985523 := by
    simpa [prefixWord, tailWord_4985523, baseEnd_4985523] using wordTrace_append hprefix tailTrace_4985523
  have hstable : (prefixWord ++ tailWord_4985523).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4985523).length < 2 ^ (prefixWord ++ tailWord_4985523).sum := by decide
  have hdescent : baseEnd_4985523 < baseStart_4985523 := by decide
  rcases family_descends (prefixWord ++ tailWord_4985523) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4985533 : List Nat := [1, 4, 1, 2, 1, 3, 1, 2, 4, 4]
def baseStart_4985533 : Nat := 118140960795 + 4985533 * 2 ^ 59
def prefixEnd_4985533 : Nat := 4983230072969 + 3 ^ 40 * 4985533 * 2
def baseEnd_4985533 : Nat := 853324915950649270969819

theorem tailTrace_4985533 : CollatzResearch.WordTrace tailWord_4985533 prefixEnd_4985533 853324915950649270969819 := by
  unfold tailWord_4985533
  simp only [CollatzResearch.WordTrace]
  refine ⟨181837327047272877093217253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121224884698181918062144835 181837327047272877093217253)
  ·
    refine ⟨34094498821363664454978235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 181837327047272877093217253 34094498821363664454978235)
    ·
      refine ⟨51141748232045496682467353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34094498821363664454978235 51141748232045496682467353)
      ·
        refine ⟨38356311174034122511850515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 51141748232045496682467353 38356311174034122511850515)
        ·
          refine ⟨57534466761051183767775773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38356311174034122511850515 57534466761051183767775773)
          ·
            refine ⟨21575425035394193912915915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 57534466761051183767775773 21575425035394193912915915)
            ·
              refine ⟨32363137553091290869373873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21575425035394193912915915 32363137553091290869373873)
              ·
                refine ⟨24272353164818468152030405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 32363137553091290869373873 24272353164818468152030405)
                ·
                  refine ⟨4551066218403462778505701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 24272353164818468152030405 4551066218403462778505701)
                  ·
                    refine ⟨853324915950649270969819, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4551066218403462778505701 853324915950649270969819)
                    ·
                      rfl

theorem cell23_4985533_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 3, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 3, 1, 2, 4, 4].length) (baseStart_4985533 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4985533 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4985533 prefixEnd_4985533 := by exact prefixLift 4985533
  have htrace : WordTrace (prefixWord ++ tailWord_4985533) baseStart_4985533 baseEnd_4985533 := by
    simpa [prefixWord, tailWord_4985533, baseEnd_4985533] using wordTrace_append hprefix tailTrace_4985533
  have hstable : (prefixWord ++ tailWord_4985533).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4985533).length < 2 ^ (prefixWord ++ tailWord_4985533).sum := by decide
  have hdescent : baseEnd_4985533 < baseStart_4985533 := by decide
  rcases family_descends (prefixWord ++ tailWord_4985533) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4985540 : List Nat := [2, 3, 3, 1, 1, 2, 2, 3, 1, 1, 4]
def baseStart_4985540 : Nat := 118140960795 + 4985540 * 2 ^ 59
def prefixEnd_4985540 : Nat := 4983230072969 + 3 ^ 40 * 4985540 * 2
def baseEnd_4985540 : Nat := 2559978342216529285521925

theorem tailTrace_4985540 : CollatzResearch.WordTrace tailWord_4985540 prefixEnd_4985540 2559978342216529285521925 := by
  unfold tailWord_4985540
  simp only [CollatzResearch.WordTrace]
  refine ⟨90918791179123758644361037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 121225054905498344859148049 90918791179123758644361037)
  ·
    refine ⟨34094546692171409491635389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 90918791179123758644361037 34094546692171409491635389)
    ·
      refine ⟨12785455009564278559363271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 34094546692171409491635389 12785455009564278559363271)
      ·
        refine ⟨19178182514346417839044907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12785455009564278559363271 19178182514346417839044907)
        ·
          refine ⟨28767273771519626758567361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19178182514346417839044907 28767273771519626758567361)
          ·
            refine ⟨21575455328639720068925521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28767273771519626758567361 21575455328639720068925521)
            ·
              refine ⟨16181591496479790051694141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21575455328639720068925521 16181591496479790051694141)
              ·
                refine ⟨6068096811179921269385303, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16181591496479790051694141 6068096811179921269385303)
                ·
                  refine ⟨9102145216769881904077955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6068096811179921269385303 9102145216769881904077955)
                  ·
                    refine ⟨13653217825154822856116933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9102145216769881904077955 13653217825154822856116933)
                    ·
                      refine ⟨2559978342216529285521925, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13653217825154822856116933 2559978342216529285521925)
                      ·
                        rfl

theorem cell23_4985540_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 2, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 2, 2, 3, 1, 1, 4].length) (baseStart_4985540 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4985540 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4985540 prefixEnd_4985540 := by exact prefixLift 4985540
  have htrace : WordTrace (prefixWord ++ tailWord_4985540) baseStart_4985540 baseEnd_4985540 := by
    simpa [prefixWord, tailWord_4985540, baseEnd_4985540] using wordTrace_append hprefix tailTrace_4985540
  have hstable : (prefixWord ++ tailWord_4985540).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4985540).length < 2 ^ (prefixWord ++ tailWord_4985540).sum := by decide
  have hdescent : baseEnd_4985540 < baseStart_4985540 := by decide
  rcases family_descends (prefixWord ++ tailWord_4985540) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4985546 : List Nat := [3, 1, 2, 1, 4, 1, 11]
def baseStart_4985546 : Nat := 118140960795 + 4985546 * 2 ^ 59
def prefixEnd_4985546 : Nat := 4983230072969 + 3 ^ 40 * 4985546 * 2
def baseEnd_4985546 : Nat := 31604708927166126691937

theorem tailTrace_4985546 : CollatzResearch.WordTrace tailWord_4985546 prefixEnd_4985546 31604708927166126691937 := by
  unfold tailWord_4985546
  simp only [CollatzResearch.WordTrace]
  refine ⟨45459450299056445078360123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 121225200797483853542293661 45459450299056445078360123)
  ·
    refine ⟨68189175448584667617540185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45459450299056445078360123 68189175448584667617540185)
    ·
      refine ⟨51141881586438500713155139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 68189175448584667617540185 51141881586438500713155139)
      ·
        refine ⟨76712822379657751069732709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51141881586438500713155139 76712822379657751069732709)
        ·
          refine ⟨14383654196185828325574883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 76712822379657751069732709 14383654196185828325574883)
          ·
            refine ⟨21575481294278742488362325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14383654196185828325574883 21575481294278742488362325)
            ·
              refine ⟨31604708927166126691937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 21575481294278742488362325 31604708927166126691937)
              ·
                rfl

theorem cell23_4985546_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 1, 11].length) (baseStart_4985546 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4985546 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4985546 prefixEnd_4985546 := by exact prefixLift 4985546
  have htrace : WordTrace (prefixWord ++ tailWord_4985546) baseStart_4985546 baseEnd_4985546 := by
    simpa [prefixWord, tailWord_4985546, baseEnd_4985546] using wordTrace_append hprefix tailTrace_4985546
  have hstable : (prefixWord ++ tailWord_4985546).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4985546).length < 2 ^ (prefixWord ++ tailWord_4985546).sum := by decide
  have hdescent : baseEnd_4985546 < baseStart_4985546 := by decide
  rcases family_descends (prefixWord ++ tailWord_4985546) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4985567 : List Nat := [1, 1, 2, 3, 2, 5, 2, 1, 2, 4]
def baseStart_4985567 : Nat := 118140960795 + 4985567 * 2 ^ 59
def prefixEnd_4985567 : Nat := 4983230072969 + 3 ^ 40 * 4985567 * 2
def baseEnd_4985567 : Nat := 853330735398066893294767

theorem tailTrace_4985567 : CollatzResearch.WordTrace tailWord_4985567 prefixEnd_4985567 853330735398066893294767 := by
  unfold tailWord_4985567
  simp only [CollatzResearch.WordTrace]
  refine ⟨181838567129149700899954955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121225711419433133933303303 181838567129149700899954955)
  ·
    refine ⟨272757850693724551349932433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 181838567129149700899954955 272757850693724551349932433)
    ·
      refine ⟨204568388020293413512449325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 272757850693724551349932433 204568388020293413512449325)
      ·
        refine ⟨76713145507610030067168497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 204568388020293413512449325 76713145507610030067168497)
        ·
          refine ⟨57534859130707522550376373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 76713145507610030067168497 57534859130707522550376373)
          ·
            refine ⟨5393893043503830239097785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 57534859130707522550376373 5393893043503830239097785)
            ·
              refine ⟨4045419782627872679323339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5393893043503830239097785 4045419782627872679323339)
              ·
                refine ⟨6068129673941809018985009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4045419782627872679323339 6068129673941809018985009)
                ·
                  refine ⟨4551097255456356764238757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6068129673941809018985009 4551097255456356764238757)
                  ·
                    refine ⟨853330735398066893294767, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4551097255456356764238757 853330735398066893294767)
                    ·
                      rfl

theorem cell23_4985567_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 5, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 5, 2, 1, 2, 4].length) (baseStart_4985567 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4985567 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4985567 prefixEnd_4985567 := by exact prefixLift 4985567
  have htrace : WordTrace (prefixWord ++ tailWord_4985567) baseStart_4985567 baseEnd_4985567 := by
    simpa [prefixWord, tailWord_4985567, baseEnd_4985567] using wordTrace_append hprefix tailTrace_4985567
  have hstable : (prefixWord ++ tailWord_4985567).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4985567).length < 2 ^ (prefixWord ++ tailWord_4985567).sum := by decide
  have hdescent : baseEnd_4985567 < baseStart_4985567 := by decide
  rcases family_descends (prefixWord ++ tailWord_4985567) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4985590 : List Nat := [5, 1, 1, 1, 1, 2, 3, 2, 1, 3, 3]
def baseStart_4985590 : Nat := 118140960795 + 4985590 * 2 ^ 59
def prefixEnd_4985590 : Nat := 4983230072969 + 3 ^ 40 * 4985590 * 2
def baseEnd_4985590 : Nat := 2560004016249254089896695

theorem tailTrace_4985590 : CollatzResearch.WordTrace tailWord_4985590 prefixEnd_4985590 2560004016249254089896695 := by
  unfold tailWord_4985590
  simp only [CollatzResearch.WordTrace]
  refine ⟨11364962875504148489252639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 121226270672044250552028149 11364962875504148489252639)
  ·
    refine ⟨17047444313256222733878959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11364962875504148489252639 17047444313256222733878959)
    ·
      refine ⟨25571166469884334100818439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17047444313256222733878959 25571166469884334100818439)
      ·
        refine ⟨38356749704826501151227659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25571166469884334100818439 38356749704826501151227659)
        ·
          refine ⟨57535124557239751726841489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38356749704826501151227659 57535124557239751726841489)
          ·
            refine ⟨43151343417929813795131117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 57535124557239751726841489 43151343417929813795131117)
            ·
              refine ⟨16181753781723680173174169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 43151343417929813795131117 16181753781723680173174169)
              ·
                refine ⟨12136315336292760129880627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16181753781723680173174169 12136315336292760129880627)
                ·
                  refine ⟨18204473004439140194820941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12136315336292760129880627 18204473004439140194820941)
                  ·
                    refine ⟨6826677376664677573057853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 18204473004439140194820941 6826677376664677573057853)
                    ·
                      refine ⟨2560004016249254089896695, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6826677376664677573057853 2560004016249254089896695)
                      ·
                        rfl

theorem cell23_4985590_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 3, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 3, 2, 1, 3, 3].length) (baseStart_4985590 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4985590 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4985590 prefixEnd_4985590 := by exact prefixLift 4985590
  have htrace : WordTrace (prefixWord ++ tailWord_4985590) baseStart_4985590 baseEnd_4985590 := by
    simpa [prefixWord, tailWord_4985590, baseEnd_4985590] using wordTrace_append hprefix tailTrace_4985590
  have hstable : (prefixWord ++ tailWord_4985590).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4985590).length < 2 ^ (prefixWord ++ tailWord_4985590).sum := by decide
  have hdescent : baseEnd_4985590 < baseStart_4985590 := by decide
  rcases family_descends (prefixWord ++ tailWord_4985590) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4985607 : List Nat := [1, 1, 4, 4, 1, 1, 1, 4, 2, 1, 3]
def baseStart_4985607 : Nat := 118140960795 + 4985607 * 2 ^ 59
def prefixEnd_4985607 : Nat := 4983230072969 + 3 ^ 40 * 4985607 * 2
def baseEnd_4985607 : Nat := 2560012745420380523384117

theorem tailTrace_4985607 : CollatzResearch.WordTrace tailWord_4985607 prefixEnd_4985607 2560012745420380523384117 := by
  unfold tailWord_4985607
  simp only [CollatzResearch.WordTrace]
  refine ⟨181840026049004787731411075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121226684032669858487607383 181840026049004787731411075)
  ·
    refine ⟨272760039073507181597116613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 181840026049004787731411075 272760039073507181597116613)
    ·
      refine ⟨51142507326282596549459365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 272760039073507181597116613 51142507326282596549459365)
      ·
        refine ⟨9589220123677986853023631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 51142507326282596549459365 9589220123677986853023631)
        ·
          refine ⟨14383830185516980279535447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9589220123677986853023631 14383830185516980279535447)
          ·
            refine ⟨21575745278275470419303171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14383830185516980279535447 21575745278275470419303171)
            ·
              refine ⟨32363617917413205628954757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21575745278275470419303171 32363617917413205628954757)
              ·
                refine ⟨6068178359514976055429017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 32363617917413205628954757 6068178359514976055429017)
                ·
                  refine ⟨4551133769636232041571763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6068178359514976055429017 4551133769636232041571763)
                  ·
                    refine ⟨6826700654454348062357645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4551133769636232041571763 6826700654454348062357645)
                    ·
                      refine ⟨2560012745420380523384117, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6826700654454348062357645 2560012745420380523384117)
                      ·
                        rfl

theorem cell23_4985607_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 1, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 1, 1, 4, 2, 1, 3].length) (baseStart_4985607 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4985607 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4985607 prefixEnd_4985607 := by exact prefixLift 4985607
  have htrace : WordTrace (prefixWord ++ tailWord_4985607) baseStart_4985607 baseEnd_4985607 := by
    simpa [prefixWord, tailWord_4985607, baseEnd_4985607] using wordTrace_append hprefix tailTrace_4985607
  have hstable : (prefixWord ++ tailWord_4985607).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4985607).length < 2 ^ (prefixWord ++ tailWord_4985607).sum := by decide
  have hdescent : baseEnd_4985607 < baseStart_4985607 := by decide
  rcases family_descends (prefixWord ++ tailWord_4985607) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4985633 : List Nat := [1, 2, 3, 2, 1, 2, 1, 2, 2, 4, 3]
def baseStart_4985633 : Nat := 118140960795 + 4985633 * 2 ^ 59
def prefixEnd_4985633 : Nat := 4983230072969 + 3 ^ 40 * 4985633 * 2
def baseEnd_4985633 : Nat := 2560026095917397421658997

theorem tailTrace_4985633 : CollatzResearch.WordTrace tailWord_4985633 prefixEnd_4985633 2560026095917397421658997 := by
  unfold tailWord_4985633
  simp only [CollatzResearch.WordTrace]
  refine ⟨181840974346910594171857553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121227316231273729447905035 181840974346910594171857553)
  ·
    refine ⟨136380730760182945628893165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 181840974346910594171857553 136380730760182945628893165)
    ·
      refine ⟨51142774035068604610834937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 136380730760182945628893165 51142774035068604610834937)
      ·
        refine ⟨38357080526301453458126203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 51142774035068604610834937 38357080526301453458126203)
        ·
          refine ⟨57535620789452180187189305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38357080526301453458126203 57535620789452180187189305)
          ·
            refine ⟨43151715592089135140391979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 57535620789452180187189305 43151715592089135140391979)
            ·
              refine ⟨64727573388133702710587969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 43151715592089135140391979 64727573388133702710587969)
              ·
                refine ⟨48545680041100277032940977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 64727573388133702710587969 48545680041100277032940977)
                ·
                  refine ⟨36409260030825207774705733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 48545680041100277032940977 36409260030825207774705733)
                  ·
                    refine ⟨6826736255779726457757325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 36409260030825207774705733 6826736255779726457757325)
                    ·
                      refine ⟨2560026095917397421658997, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6826736255779726457757325 2560026095917397421658997)
                      ·
                        rfl

theorem cell23_4985633_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 1, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 1, 2, 2, 4, 3].length) (baseStart_4985633 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4985633 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4985633 prefixEnd_4985633 := by exact prefixLift 4985633
  have htrace : WordTrace (prefixWord ++ tailWord_4985633) baseStart_4985633 baseEnd_4985633 := by
    simpa [prefixWord, tailWord_4985633, baseEnd_4985633] using wordTrace_append hprefix tailTrace_4985633
  have hstable : (prefixWord ++ tailWord_4985633).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4985633).length < 2 ^ (prefixWord ++ tailWord_4985633).sum := by decide
  have hdescent : baseEnd_4985633 < baseStart_4985633 := by decide
  rcases family_descends (prefixWord ++ tailWord_4985633) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4985681 : List Nat := [1, 2, 2, 1, 6, 1, 3, 1, 2, 2, 2]
def baseStart_4985681 : Nat := 118140960795 + 4985681 * 2 ^ 59
def prefixEnd_4985681 : Nat := 4983230072969 + 3 ^ 40 * 4985681 * 2
def baseEnd_4985681 : Nat := 2560050742988813233858777

theorem tailTrace_4985681 : CollatzResearch.WordTrace tailWord_4985681 prefixEnd_4985681 2560050742988813233858777 := by
  unfold tailWord_4985681
  simp only [CollatzResearch.WordTrace]
  refine ⟨181842725050736698369604897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121228483367157798913069931 181842725050736698369604897)
  ·
    refine ⟨136382043788052523777203673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 181842725050736698369604897 136382043788052523777203673)
    ·
      refine ⟨102286532841039392832902755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 136382043788052523777203673 102286532841039392832902755)
      ·
        refine ⟨153429799261559089249354133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 102286532841039392832902755 153429799261559089249354133)
        ·
          refine ⟨7192021840385582308563475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 153429799261559089249354133 7192021840385582308563475)
          ·
            refine ⟨10788032760578373462845213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7192021840385582308563475 10788032760578373462845213)
            ·
              refine ⟨4045512285216890048566955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10788032760578373462845213 4045512285216890048566955)
              ·
                refine ⟨6068268427825335072850433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4045512285216890048566955 6068268427825335072850433)
                ·
                  refine ⟨4551201320869001304637825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6068268427825335072850433 4551201320869001304637825)
                  ·
                    refine ⟨3413400990651750978478369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4551201320869001304637825 3413400990651750978478369)
                    ·
                      refine ⟨2560050742988813233858777, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3413400990651750978478369 2560050742988813233858777)
                      ·
                        rfl

theorem cell23_4985681_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 6, 1, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 6, 1, 3, 1, 2, 2, 2].length) (baseStart_4985681 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4985681 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4985681 prefixEnd_4985681 := by exact prefixLift 4985681
  have htrace : WordTrace (prefixWord ++ tailWord_4985681) baseStart_4985681 baseEnd_4985681 := by
    simpa [prefixWord, tailWord_4985681, baseEnd_4985681] using wordTrace_append hprefix tailTrace_4985681
  have hstable : (prefixWord ++ tailWord_4985681).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4985681).length < 2 ^ (prefixWord ++ tailWord_4985681).sum := by decide
  have hdescent : baseEnd_4985681 < baseStart_4985681 := by decide
  rcases family_descends (prefixWord ++ tailWord_4985681) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4985720 : List Nat := [2, 1, 2, 1, 1, 1, 1, 6, 2, 4, 2]
def baseStart_4985720 : Nat := 118140960795 + 4985720 * 2 ^ 59
def prefixEnd_4985720 : Nat := 4983230072969 + 3 ^ 40 * 4985720 * 2
def baseEnd_4985720 : Nat := 2560070768734338581271097

theorem tailTrace_4985720 : CollatzResearch.WordTrace tailWord_4985720 prefixEnd_4985720 2560070768734338581271097 := by
  unfold tailWord_4985720
  simp only [CollatzResearch.WordTrace]
  refine ⟨90922073748797704015137307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 121229431665063605353516409 90922073748797704015137307)
  ·
    refine ⟨136383110623196556022705961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90922073748797704015137307 136383110623196556022705961)
    ·
      refine ⟨102287332967397417017029471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 136383110623196556022705961 102287332967397417017029471)
      ·
        refine ⟨153430999451096125525544207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 102287332967397417017029471 153430999451096125525544207)
        ·
          refine ⟨230146499176644188288316311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 153430999451096125525544207 230146499176644188288316311)
          ·
            refine ⟨345219748764966282432474467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 230146499176644188288316311 345219748764966282432474467)
            ·
              refine ⟨517829623147449423648711701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 345219748764966282432474467 517829623147449423648711701)
              ·
                refine ⟨24273263585036691733533361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 517829623147449423648711701 24273263585036691733533361)
                ·
                  refine ⟨18204947688777518800150021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 24273263585036691733533361 18204947688777518800150021)
                  ·
                    refine ⟨3413427691645784775028129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 18204947688777518800150021 3413427691645784775028129)
                    ·
                      refine ⟨2560070768734338581271097, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3413427691645784775028129 2560070768734338581271097)
                      ·
                        rfl

theorem cell23_4985720_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 6, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 6, 2, 4, 2].length) (baseStart_4985720 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4985720 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4985720 prefixEnd_4985720 := by exact prefixLift 4985720
  have htrace : WordTrace (prefixWord ++ tailWord_4985720) baseStart_4985720 baseEnd_4985720 := by
    simpa [prefixWord, tailWord_4985720, baseEnd_4985720] using wordTrace_append hprefix tailTrace_4985720
  have hstable : (prefixWord ++ tailWord_4985720).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4985720).length < 2 ^ (prefixWord ++ tailWord_4985720).sum := by decide
  have hdescent : baseEnd_4985720 < baseStart_4985720 := by decide
  rcases family_descends (prefixWord ++ tailWord_4985720) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4985757 : List Nat := [1, 4, 2, 1, 2, 1, 4, 1, 2, 2, 3]
def baseStart_4985757 : Nat := 118140960795 + 4985757 * 2 ^ 59
def prefixEnd_4985757 : Nat := 4983230072969 + 3 ^ 40 * 4985757 * 2
def baseEnd_4985757 : Nat := 2560089767518554936508427

theorem tailTrace_4985757 : CollatzResearch.WordTrace tailWord_4985757 prefixEnd_4985757 2560089767518554936508427 := by
  unfold tailWord_4985757
  simp only [CollatzResearch.WordTrace]
  refine ⟨181845496998461363349371525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121230331332307575566247683 181845496998461363349371525)
  ·
    refine ⟨34096030687211505628007161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 181845496998461363349371525 34096030687211505628007161)
    ·
      refine ⟨25572023015408629221005371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34096030687211505628007161 25572023015408629221005371)
      ·
        refine ⟨38358034523112943831508057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25572023015408629221005371 38358034523112943831508057)
        ·
          refine ⟨28768525892334707873631043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38358034523112943831508057 28768525892334707873631043)
          ·
            refine ⟨43152788838502061810446565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28768525892334707873631043 43152788838502061810446565)
            ·
              refine ⟨8091147907219136589458731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 43152788838502061810446565 8091147907219136589458731)
              ·
                refine ⟨12136721860828704884188097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8091147907219136589458731 12136721860828704884188097)
                ·
                  refine ⟨9102541395621528663141073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12136721860828704884188097 9102541395621528663141073)
                  ·
                    refine ⟨6826906046716146497355805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9102541395621528663141073 6826906046716146497355805)
                    ·
                      refine ⟨2560089767518554936508427, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6826906046716146497355805 2560089767518554936508427)
                      ·
                        rfl

theorem cell23_4985757_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 4, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 4, 1, 2, 2, 3].length) (baseStart_4985757 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4985757 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4985757 prefixEnd_4985757 := by exact prefixLift 4985757
  have htrace : WordTrace (prefixWord ++ tailWord_4985757) baseStart_4985757 baseEnd_4985757 := by
    simpa [prefixWord, tailWord_4985757, baseEnd_4985757] using wordTrace_append hprefix tailTrace_4985757
  have hstable : (prefixWord ++ tailWord_4985757).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4985757).length < 2 ^ (prefixWord ++ tailWord_4985757).sum := by decide
  have hdescent : baseEnd_4985757 < baseStart_4985757 := by decide
  rcases family_descends (prefixWord ++ tailWord_4985757) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4985777 : List Nat := [1, 2, 2, 4, 3, 1, 2, 2, 6]
def baseStart_4985777 : Nat := 118140960795 + 4985777 * 2 ^ 59
def prefixEnd_4985777 : Nat := 4983230072969 + 3 ^ 40 * 4985777 * 2
def baseEnd_4985777 : Nat := 284455559681293873139815

theorem tailTrace_4985777 : CollatzResearch.WordTrace tailWord_4985777 prefixEnd_4985777 284455559681293873139815 := by
  unfold tailWord_4985777
  simp only [CollatzResearch.WordTrace]
  refine ⟨181846226458388906765099585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121230817638925937843399723 181846226458388906765099585)
  ·
    refine ⟨136384669843791680073824689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 181846226458388906765099585 136384669843791680073824689)
    ·
      refine ⟨102288502382843760055368517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 136384669843791680073824689 102288502382843760055368517)
      ·
        refine ⟨19179094196783205010381597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 102288502382843760055368517 19179094196783205010381597)
        ·
          refine ⟨7192160323793701878893099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19179094196783205010381597 7192160323793701878893099)
          ·
            refine ⟨10788240485690552818339649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7192160323793701878893099 10788240485690552818339649)
            ·
              refine ⟨8091180364267914613754737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10788240485690552818339649 8091180364267914613754737)
              ·
                refine ⟨6068385273200935960316053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8091180364267914613754737 6068385273200935960316053)
                ·
                  refine ⟨284455559681293873139815, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6068385273200935960316053 284455559681293873139815)
                  ·
                    rfl

theorem cell23_4985777_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 3, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 3, 1, 2, 2, 6].length) (baseStart_4985777 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4985777 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4985777 prefixEnd_4985777 := by exact prefixLift 4985777
  have htrace : WordTrace (prefixWord ++ tailWord_4985777) baseStart_4985777 baseEnd_4985777 := by
    simpa [prefixWord, tailWord_4985777, baseEnd_4985777] using wordTrace_append hprefix tailTrace_4985777
  have hstable : (prefixWord ++ tailWord_4985777).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4985777).length < 2 ^ (prefixWord ++ tailWord_4985777).sum := by decide
  have hdescent : baseEnd_4985777 < baseStart_4985777 := by decide
  rcases family_descends (prefixWord ++ tailWord_4985777) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4985790 : List Nat := [4, 2, 1, 1, 1, 2, 1, 1, 5, 5]
def baseStart_4985790 : Nat := 118140960795 + 4985790 * 2 ^ 59
def prefixEnd_4985790 : Nat := 4983230072969 + 3 ^ 40 * 4985790 * 2
def baseEnd_4985790 : Nat := 853368904126717769131925

theorem tailTrace_4985790 : CollatzResearch.WordTrace tailWord_4985790 prefixEnd_4985790 853368904126717769131925 := by
  unfold tailWord_4985790
  simp only [CollatzResearch.WordTrace]
  refine ⟨22730837575917726248165353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 121231133738227873323548549 22730837575917726248165353)
  ·
    refine ⟨17048128181938294686124015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22730837575917726248165353 17048128181938294686124015)
    ·
      refine ⟨25572192272907442029186023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17048128181938294686124015 25572192272907442029186023)
      ·
        refine ⟨38358288409361163043779035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25572192272907442029186023 38358288409361163043779035)
        ·
          refine ⟨57537432614041744565668553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38358288409361163043779035 57537432614041744565668553)
          ·
            refine ⟨43153074460531308424251415, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 57537432614041744565668553 43153074460531308424251415)
            ·
              refine ⟨64729611690796962636377123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 43153074460531308424251415 64729611690796962636377123)
              ·
                refine ⟨97094417536195443954565685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 64729611690796962636377123 97094417536195443954565685)
                ·
                  refine ⟨9102601644018322870740533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 97094417536195443954565685 9102601644018322870740533)
                  ·
                    refine ⟨853368904126717769131925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9102601644018322870740533 853368904126717769131925)
                    ·
                      rfl

theorem cell23_4985790_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 1, 1, 5, 5].length) (baseStart_4985790 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4985790 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4985790 prefixEnd_4985790 := by exact prefixLift 4985790
  have htrace : WordTrace (prefixWord ++ tailWord_4985790) baseStart_4985790 baseEnd_4985790 := by
    simpa [prefixWord, tailWord_4985790, baseEnd_4985790] using wordTrace_append hprefix tailTrace_4985790
  have hstable : (prefixWord ++ tailWord_4985790).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4985790).length < 2 ^ (prefixWord ++ tailWord_4985790).sum := by decide
  have hdescent : baseEnd_4985790 < baseStart_4985790 := by decide
  rcases family_descends (prefixWord ++ tailWord_4985790) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4985805 : List Nat := [1, 6, 3, 1, 2, 1, 1, 1, 2, 1, 4]
def baseStart_4985805 : Nat := 118140960795 + 4985805 * 2 ^ 59
def prefixEnd_4985805 : Nat := 4983230072969 + 3 ^ 40 * 4985805 * 2
def baseEnd_4985805 : Nat := 2560114414589970748708207

theorem tailTrace_4985805 : CollatzResearch.WordTrace tailWord_4985805 prefixEnd_4985805 2560114414589970748708207 := by
  unfold tailWord_4985805
  simp only [CollatzResearch.WordTrace]
  refine ⟨181847247702287467547118869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121231498468191645031412579 181847247702287467547118869)
  ·
    refine ⟨8524089736044725041271197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 181847247702287467547118869 8524089736044725041271197)
    ·
      refine ⟨3196533651016771890476699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8524089736044725041271197 3196533651016771890476699)
      ·
        refine ⟨4794800476525157835715049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3196533651016771890476699 4794800476525157835715049)
        ·
          refine ⟨3596100357393868376786287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4794800476525157835715049 3596100357393868376786287)
          ·
            refine ⟨5394150536090802565179431, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3596100357393868376786287 5394150536090802565179431)
            ·
              refine ⟨8091225804136203847769147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5394150536090802565179431 8091225804136203847769147)
              ·
                refine ⟨12136838706204305771653721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8091225804136203847769147 12136838706204305771653721)
                ·
                  refine ⟨9102629029653229328740291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12136838706204305771653721 9102629029653229328740291)
                  ·
                    refine ⟨13653943544479843993110437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9102629029653229328740291 13653943544479843993110437)
                    ·
                      refine ⟨2560114414589970748708207, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13653943544479843993110437 2560114414589970748708207)
                      ·
                        rfl

theorem cell23_4985805_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 3, 1, 2, 1, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 3, 1, 2, 1, 1, 1, 2, 1, 4].length) (baseStart_4985805 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4985805 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4985805 prefixEnd_4985805 := by exact prefixLift 4985805
  have htrace : WordTrace (prefixWord ++ tailWord_4985805) baseStart_4985805 baseEnd_4985805 := by
    simpa [prefixWord, tailWord_4985805, baseEnd_4985805] using wordTrace_append hprefix tailTrace_4985805
  have hstable : (prefixWord ++ tailWord_4985805).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4985805).length < 2 ^ (prefixWord ++ tailWord_4985805).sum := by decide
  have hdescent : baseEnd_4985805 < baseStart_4985805 := by decide
  rcases family_descends (prefixWord ++ tailWord_4985805) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4985821 : List Nat := [1, 4, 3, 1, 2, 1, 1, 5, 1, 1, 3]
def baseStart_4985821 : Nat := 118140960795 + 4985821 * 2 ^ 59
def prefixEnd_4985821 : Nat := 4983230072969 + 3 ^ 40 * 4985821 * 2
def baseEnd_4985821 : Nat := 2560122630280442686108133

theorem tailTrace_4985821 : CollatzResearch.WordTrace tailWord_4985821 prefixEnd_4985821 2560122630280442686108133 := by
  unfold tailWord_4985821
  simp only [CollatzResearch.WordTrace]
  refine ⟨181847831270229502279701317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121231887513486334853134211 181847831270229502279701317)
  ·
    refine ⟨34096468363168031677443997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 181847831270229502279701317 34096468363168031677443997)
    ·
      refine ⟨12786175636188011879041499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 34096468363168031677443997 12786175636188011879041499)
      ·
        refine ⟨19179263454282017818562249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12786175636188011879041499 19179263454282017818562249)
        ·
          refine ⟨14384447590711513363921687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19179263454282017818562249 14384447590711513363921687)
          ·
            refine ⟨21576671386067270045882531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14384447590711513363921687 21576671386067270045882531)
            ·
              refine ⟨32365007079100905068823797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21576671386067270045882531 32365007079100905068823797)
              ·
                refine ⟨3034219413665709850202231, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 32365007079100905068823797 3034219413665709850202231)
                ·
                  refine ⟨4551329120498564775303347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3034219413665709850202231 4551329120498564775303347)
                  ·
                    refine ⟨6826993680747847162955021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4551329120498564775303347 6826993680747847162955021)
                    ·
                      refine ⟨2560122630280442686108133, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6826993680747847162955021 2560122630280442686108133)
                      ·
                        rfl

theorem cell23_4985821_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 1, 1, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 1, 1, 5, 1, 1, 3].length) (baseStart_4985821 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4985821 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4985821 prefixEnd_4985821 := by exact prefixLift 4985821
  have htrace : WordTrace (prefixWord ++ tailWord_4985821) baseStart_4985821 baseEnd_4985821 := by
    simpa [prefixWord, tailWord_4985821, baseEnd_4985821] using wordTrace_append hprefix tailTrace_4985821
  have hstable : (prefixWord ++ tailWord_4985821).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4985821).length < 2 ^ (prefixWord ++ tailWord_4985821).sum := by decide
  have hdescent : baseEnd_4985821 < baseStart_4985821 := by decide
  rcases family_descends (prefixWord ++ tailWord_4985821) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4985827 : List Nat := [1, 1, 1, 6, 1, 1, 3, 3, 1, 1, 4]
def baseStart_4985827 : Nat := 118140960795 + 4985827 * 2 ^ 59
def prefixEnd_4985827 : Nat := 4983230072969 + 3 ^ 40 * 4985827 * 2
def baseEnd_4985827 : Nat := 2560125711164369662633105

theorem tailTrace_4985827 : CollatzResearch.WordTrace tailWord_4985827 prefixEnd_4985827 2560125711164369662633105 := by
  unfold tailWord_4985827
  simp only [CollatzResearch.WordTrace]
  refine ⟨181848050108207765304419735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121232033405471843536279823 181848050108207765304419735)
  ·
    refine ⟨272772075162311647956629603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 181848050108207765304419735 272772075162311647956629603)
    ·
      refine ⟨409158112743467471934944405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 272772075162311647956629603 409158112743467471934944405)
      ·
        refine ⟨19179286534850037746950519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 409158112743467471934944405 19179286534850037746950519)
        ·
          refine ⟨28768929802275056620425779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19179286534850037746950519 28768929802275056620425779)
          ·
            refine ⟨43153394703412584930638669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28768929802275056620425779 43153394703412584930638669)
            ·
              refine ⟨16182523013779719348989501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 43153394703412584930638669 16182523013779719348989501)
              ·
                refine ⟨6068446130167394755871063, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16182523013779719348989501 6068446130167394755871063)
                ·
                  refine ⟨9102669195251092133806595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6068446130167394755871063 9102669195251092133806595)
                  ·
                    refine ⟨13654003792876638200709893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9102669195251092133806595 13654003792876638200709893)
                    ·
                      refine ⟨2560125711164369662633105, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13654003792876638200709893 2560125711164369662633105)
                      ·
                        rfl

theorem cell23_4985827_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 3, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 3, 3, 1, 1, 4].length) (baseStart_4985827 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4985827 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4985827 prefixEnd_4985827 := by exact prefixLift 4985827
  have htrace : WordTrace (prefixWord ++ tailWord_4985827) baseStart_4985827 baseEnd_4985827 := by
    simpa [prefixWord, tailWord_4985827, baseEnd_4985827] using wordTrace_append hprefix tailTrace_4985827
  have hstable : (prefixWord ++ tailWord_4985827).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4985827).length < 2 ^ (prefixWord ++ tailWord_4985827).sum := by decide
  have hdescent : baseEnd_4985827 < baseStart_4985827 := by decide
  rcases family_descends (prefixWord ++ tailWord_4985827) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4985843 : List Nat := [1, 1, 1, 2, 2, 2, 1, 1, 1, 4, 7]
def baseStart_4985843 : Nat := 118140960795 + 4985843 * 2 ^ 59
def prefixEnd_4985843 : Nat := 4983230072969 + 3 ^ 40 * 4985843 * 2
def baseEnd_4985843 : Nat := 2560133926854841600033031

theorem tailTrace_4985843 : CollatzResearch.WordTrace tailWord_4985843 prefixEnd_4985843 2560133926854841600033031 := by
  unfold tailWord_4985843
  simp only [CollatzResearch.WordTrace]
  refine ⟨181848633676149800037002183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121232422450766533358001455 181848633676149800037002183)
  ·
    refine ⟨272772950514224700055503275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 181848633676149800037002183 272772950514224700055503275)
    ·
      refine ⟨409159425771337050083254913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 272772950514224700055503275 409159425771337050083254913)
      ·
        refine ⟨306869569328502787562441185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 409159425771337050083254913 306869569328502787562441185)
        ·
          refine ⟨230152176996377090671830889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 306869569328502787562441185 230152176996377090671830889)
          ·
            refine ⟨172614132747282818003873167, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 230152176996377090671830889 172614132747282818003873167)
            ·
              refine ⟨258921199120924227005809751, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 172614132747282818003873167 258921199120924227005809751)
              ·
                refine ⟨388381798681386340508714627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 258921199120924227005809751 388381798681386340508714627)
                ·
                  refine ⟨582572698022079510763071941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 388381798681386340508714627 582572698022079510763071941)
                  ·
                    refine ⟨109232380879139908268075989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 582572698022079510763071941 109232380879139908268075989)
                    ·
                      refine ⟨2560133926854841600033031, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 109232380879139908268075989 2560133926854841600033031)
                      ·
                        rfl

theorem cell23_4985843_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 1, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 1, 1, 1, 4, 7].length) (baseStart_4985843 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4985843 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4985843 prefixEnd_4985843 := by exact prefixLift 4985843
  have htrace : WordTrace (prefixWord ++ tailWord_4985843) baseStart_4985843 baseEnd_4985843 := by
    simpa [prefixWord, tailWord_4985843, baseEnd_4985843] using wordTrace_append hprefix tailTrace_4985843
  have hstable : (prefixWord ++ tailWord_4985843).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4985843).length < 2 ^ (prefixWord ++ tailWord_4985843).sum := by decide
  have hdescent : baseEnd_4985843 < baseStart_4985843 := by decide
  rcases family_descends (prefixWord ++ tailWord_4985843) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4985857 : List Nat := [1, 2, 4, 1, 2, 2, 3, 1, 1, 2, 4]
def baseStart_4985857 : Nat := 118140960795 + 4985857 * 2 ^ 59
def prefixEnd_4985857 : Nat := 4983230072969 + 3 ^ 40 * 4985857 * 2
def baseEnd_4985857 : Nat := 2560141115584004545257967

theorem tailTrace_4985857 : CollatzResearch.WordTrace tailWord_4985857 prefixEnd_4985857 2560141115584004545257967 := by
  unfold tailWord_4985857
  simp only [CollatzResearch.WordTrace]
  refine ⟨181849144298099080428011825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121232762865399386952007883 181849144298099080428011825)
  ·
    refine ⟨136386858223574310321008869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 181849144298099080428011825 136386858223574310321008869)
    ·
      refine ⟨25572535916920183185189163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 136386858223574310321008869 25572535916920183185189163)
      ·
        refine ⟨38358803875380274777783745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25572535916920183185189163 38358803875380274777783745)
        ·
          refine ⟨28769102906535206083337809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38358803875380274777783745 28769102906535206083337809)
          ·
            refine ⟨21576827179901404562503357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28769102906535206083337809 21576827179901404562503357)
            ·
              refine ⟨8091310192463026710938759, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21576827179901404562503357 8091310192463026710938759)
              ·
                refine ⟨12136965288694540066408139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8091310192463026710938759 12136965288694540066408139)
                ·
                  refine ⟨18205447933041810099612209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12136965288694540066408139 18205447933041810099612209)
                  ·
                    refine ⟨13654085949781357574709157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 18205447933041810099612209 13654085949781357574709157)
                    ·
                      refine ⟨2560141115584004545257967, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13654085949781357574709157 2560141115584004545257967)
                      ·
                        rfl

theorem cell23_4985857_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 2, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 2, 3, 1, 1, 2, 4].length) (baseStart_4985857 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4985857 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4985857 prefixEnd_4985857 := by exact prefixLift 4985857
  have htrace : WordTrace (prefixWord ++ tailWord_4985857) baseStart_4985857 baseEnd_4985857 := by
    simpa [prefixWord, tailWord_4985857, baseEnd_4985857] using wordTrace_append hprefix tailTrace_4985857
  have hstable : (prefixWord ++ tailWord_4985857).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4985857).length < 2 ^ (prefixWord ++ tailWord_4985857).sum := by decide
  have hdescent : baseEnd_4985857 < baseStart_4985857 := by decide
  rcases family_descends (prefixWord ++ tailWord_4985857) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4985864 : List Nat := [2, 1, 3, 2, 1, 4, 2, 2, 1, 2, 3]
def baseStart_4985864 : Nat := 118140960795 + 4985864 * 2 ^ 59
def prefixEnd_4985864 : Nat := 4983230072969 + 3 ^ 40 * 4985864 * 2
def baseEnd_4985864 : Nat := 2560144709948586017870435

theorem tailTrace_4985864 : CollatzResearch.WordTrace tailWord_4985864 prefixEnd_4985864 2560144709948586017870435 := by
  unfold tailWord_4985864
  simp only [CollatzResearch.WordTrace]
  refine ⟨90924699804536860311758323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 121232933072715813749011097 90924699804536860311758323)
  ·
    refine ⟨136387049706805290467637485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90924699804536860311758323 136387049706805290467637485)
    ·
      refine ⟨51145143640051983925364057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 136387049706805290467637485 51145143640051983925364057)
      ·
        refine ⟨38358857730038987944023043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 51145143640051983925364057 38358857730038987944023043)
        ·
          refine ⟨57538286595058481916034565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38358857730038987944023043 57538286595058481916034565)
          ·
            refine ⟨10788428736573465359256481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 57538286595058481916034565 10788428736573465359256481)
            ·
              refine ⟨8091321552430099019442361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10788428736573465359256481 8091321552430099019442361)
              ·
                refine ⟨6068491164322574264581771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8091321552430099019442361 6068491164322574264581771)
                ·
                  refine ⟨9102736746483861396872657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6068491164322574264581771 9102736746483861396872657)
                  ·
                    refine ⟨6827052559862896047654493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9102736746483861396872657 6827052559862896047654493)
                    ·
                      refine ⟨2560144709948586017870435, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6827052559862896047654493 2560144709948586017870435)
                      ·
                        rfl

theorem cell23_4985864_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 4, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 4, 2, 2, 1, 2, 3].length) (baseStart_4985864 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4985864 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4985864 prefixEnd_4985864 := by exact prefixLift 4985864
  have htrace : WordTrace (prefixWord ++ tailWord_4985864) baseStart_4985864 baseEnd_4985864 := by
    simpa [prefixWord, tailWord_4985864, baseEnd_4985864] using wordTrace_append hprefix tailTrace_4985864
  have hstable : (prefixWord ++ tailWord_4985864).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4985864).length < 2 ^ (prefixWord ++ tailWord_4985864).sum := by decide
  have hdescent : baseEnd_4985864 < baseStart_4985864 := by decide
  rcases family_descends (prefixWord ++ tailWord_4985864) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4985867 : List Nat := [1, 1, 1, 1, 6, 4, 2, 7]
def baseStart_4985867 : Nat := 118140960795 + 4985867 * 2 ^ 59
def prefixEnd_4985867 : Nat := 4983230072969 + 3 ^ 40 * 4985867 * 2
def baseEnd_4985867 : Nat := 94820231495946278004923

theorem tailTrace_4985867 : CollatzResearch.WordTrace tailWord_4985867 prefixEnd_4985867 94820231495946278004923 := by
  unfold tailWord_4985867
  simp only [CollatzResearch.WordTrace]
  refine ⟨181849509028062852135875855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121233006018708568090583903 181849509028062852135875855)
  ·
    refine ⟨272774263542094278203813783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 181849509028062852135875855 272774263542094278203813783)
    ·
      refine ⟨409161395313141417305720675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 272774263542094278203813783 409161395313141417305720675)
      ·
        refine ⟨613742092969712125958581013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 409161395313141417305720675 613742092969712125958581013)
        ·
          refine ⟨28769160607955255904308485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 613742092969712125958581013 28769160607955255904308485)
          ·
            refine ⟨5394217613991610482057841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 28769160607955255904308485 5394217613991610482057841)
            ·
              refine ⟨4045663210493707861543381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5394217613991610482057841 4045663210493707861543381)
              ·
                refine ⟨94820231495946278004923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4045663210493707861543381 94820231495946278004923)
                ·
                  rfl

theorem cell23_4985867_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 4, 2, 7].length) (baseStart_4985867 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4985867 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4985867 prefixEnd_4985867 := by exact prefixLift 4985867
  have htrace : WordTrace (prefixWord ++ tailWord_4985867) baseStart_4985867 baseEnd_4985867 := by
    simpa [prefixWord, tailWord_4985867, baseEnd_4985867] using wordTrace_append hprefix tailTrace_4985867
  have hstable : (prefixWord ++ tailWord_4985867).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4985867).length < 2 ^ (prefixWord ++ tailWord_4985867).sum := by decide
  have hdescent : baseEnd_4985867 < baseStart_4985867 := by decide
  rcases family_descends (prefixWord ++ tailWord_4985867) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4985900 : List Nat := [2, 2, 1, 1, 1, 2, 4, 1, 2, 3, 4]
def baseStart_4985900 : Nat := 118140960795 + 4985900 * 2 ^ 59
def prefixEnd_4985900 : Nat := 4983230072969 + 3 ^ 40 * 4985900 * 2
def baseEnd_4985900 : Nat := 2560163195252147877020269

theorem tailTrace_4985900 : CollatzResearch.WordTrace tailWord_4985900 prefixEnd_4985900 2560163195252147877020269 := by
  unfold tailWord_4985900
  simp only [CollatzResearch.WordTrace]
  refine ⟨90925356318471649385913577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 121233808424628865847884769 90925356318471649385913577)
  ·
    refine ⟨68194017238853737039435183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 90925356318471649385913577 68194017238853737039435183)
    ·
      refine ⟨102291025858280605559152775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68194017238853737039435183 102291025858280605559152775)
      ·
        refine ⟨153436538787420908338729163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 102291025858280605559152775 153436538787420908338729163)
        ·
          refine ⟨230154808181131362508093745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 153436538787420908338729163 230154808181131362508093745)
          ·
            refine ⟨172616106135848521881070309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 230154808181131362508093745 172616106135848521881070309)
            ·
              refine ⟨32365519900471597852700683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 172616106135848521881070309 32365519900471597852700683)
              ·
                refine ⟨48548279850707396779051025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32365519900471597852700683 48548279850707396779051025)
                ·
                  refine ⟨36411209888030547584288269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 48548279850707396779051025 36411209888030547584288269)
                  ·
                    refine ⟨13654203708011455344108101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 36411209888030547584288269 13654203708011455344108101)
                    ·
                      refine ⟨2560163195252147877020269, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13654203708011455344108101 2560163195252147877020269)
                      ·
                        rfl

theorem cell23_4985900_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 3, 4].length) (baseStart_4985900 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4985900 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4985900 prefixEnd_4985900 := by exact prefixLift 4985900
  have htrace : WordTrace (prefixWord ++ tailWord_4985900) baseStart_4985900 baseEnd_4985900 := by
    simpa [prefixWord, tailWord_4985900, baseEnd_4985900] using wordTrace_append hprefix tailTrace_4985900
  have hstable : (prefixWord ++ tailWord_4985900).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4985900).length < 2 ^ (prefixWord ++ tailWord_4985900).sum := by decide
  have hdescent : baseEnd_4985900 < baseStart_4985900 := by decide
  rcases family_descends (prefixWord ++ tailWord_4985900) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4985920 : List Nat := [2, 1, 1, 2, 2, 3, 1, 1, 4, 1, 5]
def baseStart_4985920 : Nat := 118140960795 + 4985920 * 2 ^ 59
def prefixEnd_4985920 : Nat := 4983230072969 + 3 ^ 40 * 4985920 * 2
def baseEnd_4985920 : Nat := 2560173464865237798770177

theorem tailTrace_4985920 : CollatzResearch.WordTrace tailWord_4985920 prefixEnd_4985920 2560173464865237798770177 := by
  unfold tailWord_4985920
  simp only [CollatzResearch.WordTrace]
  refine ⟨90925721048435421093777607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 121234294731247228125036809 90925721048435421093777607)
  ·
    refine ⟨136388581572653131640666411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90925721048435421093777607 136388581572653131640666411)
    ·
      refine ⟨204582872358979697460999617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 136388581572653131640666411 204582872358979697460999617)
      ·
        refine ⟨153437154269234773095749713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 204582872358979697460999617 153437154269234773095749713)
        ·
          refine ⟨115077865701926079821812285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 153437154269234773095749713 115077865701926079821812285)
          ·
            refine ⟨43154199638222279933179607, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 115077865701926079821812285 43154199638222279933179607)
            ·
              refine ⟨64731299457333419899769411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 43154199638222279933179607 64731299457333419899769411)
              ·
                refine ⟨97096949186000129849654117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 64731299457333419899769411 97096949186000129849654117)
                ·
                  refine ⟨18205677972375024346810147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 97096949186000129849654117 18205677972375024346810147)
                  ·
                    refine ⟨27308516958562536520215221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 18205677972375024346810147 27308516958562536520215221)
                    ·
                      refine ⟨2560173464865237798770177, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 27308516958562536520215221 2560173464865237798770177)
                      ·
                        rfl

theorem cell23_4985920_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 1, 1, 4, 1, 5].length) (baseStart_4985920 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4985920 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4985920 prefixEnd_4985920 := by exact prefixLift 4985920
  have htrace : WordTrace (prefixWord ++ tailWord_4985920) baseStart_4985920 baseEnd_4985920 := by
    simpa [prefixWord, tailWord_4985920, baseEnd_4985920] using wordTrace_append hprefix tailTrace_4985920
  have hstable : (prefixWord ++ tailWord_4985920).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4985920).length < 2 ^ (prefixWord ++ tailWord_4985920).sum := by decide
  have hdescent : baseEnd_4985920 < baseStart_4985920 := by decide
  rcases family_descends (prefixWord ++ tailWord_4985920) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4985921 : List Nat := [1, 2, 5, 1, 3, 1, 1, 1, 3, 3, 2]
def baseStart_4985921 : Nat := 118140960795 + 4985921 * 2 ^ 59
def prefixEnd_4985921 : Nat := 4983230072969 + 3 ^ 40 * 4985921 * 2
def baseEnd_4985921 : Nat := 2560173978345892294857673

theorem tailTrace_4985921 : CollatzResearch.WordTrace tailWord_4985921 prefixEnd_4985921 2560173978345892294857673 := by
  unfold tailWord_4985921
  simp only [CollatzResearch.WordTrace]
  refine ⟨181851478569867219358341617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121234319046578146238894411 181851478569867219358341617)
  ·
    refine ⟨136388608927400414518756213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 181851478569867219358341617 136388608927400414518756213)
    ·
      refine ⟨12786432086943788861133395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 136388608927400414518756213 12786432086943788861133395)
      ·
        refine ⟨19179648130415683291700093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12786432086943788861133395 19179648130415683291700093)
        ·
          refine ⟨7192368048905881234387535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19179648130415683291700093 7192368048905881234387535)
          ·
            refine ⟨10788552073358821851581303, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7192368048905881234387535 10788552073358821851581303)
            ·
              refine ⟨16182828110038232777371955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10788552073358821851581303 16182828110038232777371955)
              ·
                refine ⟨24274242165057349166057933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16182828110038232777371955 24274242165057349166057933)
                ·
                  refine ⟨9102840811896505937271725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 24274242165057349166057933 9102840811896505937271725)
                  ·
                    refine ⟨3413565304461189726476897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9102840811896505937271725 3413565304461189726476897)
                    ·
                      refine ⟨2560173978345892294857673, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3413565304461189726476897 2560173978345892294857673)
                      ·
                        rfl

theorem cell23_4985921_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 3, 1, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 3, 1, 1, 1, 3, 3, 2].length) (baseStart_4985921 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4985921 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4985921 prefixEnd_4985921 := by exact prefixLift 4985921
  have htrace : WordTrace (prefixWord ++ tailWord_4985921) baseStart_4985921 baseEnd_4985921 := by
    simpa [prefixWord, tailWord_4985921, baseEnd_4985921] using wordTrace_append hprefix tailTrace_4985921
  have hstable : (prefixWord ++ tailWord_4985921).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4985921).length < 2 ^ (prefixWord ++ tailWord_4985921).sum := by decide
  have hdescent : baseEnd_4985921 < baseStart_4985921 := by decide
  rcases family_descends (prefixWord ++ tailWord_4985921) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4985934 : List Nat := [4, 1, 1, 1, 1, 3, 3, 2, 1, 4, 2]
def baseStart_4985934 : Nat := 118140960795 + 4985934 * 2 ^ 59
def prefixEnd_4985934 : Nat := 4983230072969 + 3 ^ 40 * 4985934 * 2
def baseEnd_4985934 : Nat := 2560180653594400743995113

theorem tailTrace_4985934 : CollatzResearch.WordTrace tailWord_4985934 prefixEnd_4985934 2560180653594400743995113 := by
  unfold tailWord_4985934
  simp only [CollatzResearch.WordTrace]
  refine ⟨22731494089852515322320607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 121234635145880081719043237 22731494089852515322320607)
  ·
    refine ⟨34097241134778772983480911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22731494089852515322320607 34097241134778772983480911)
    ·
      refine ⟨51145861702168159475221367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34097241134778772983480911 51145861702168159475221367)
      ·
        refine ⟨76718792553252239212832051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51145861702168159475221367 76718792553252239212832051)
        ·
          refine ⟨115078188829878358819248077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 76718792553252239212832051 115078188829878358819248077)
          ·
            refine ⟨43154320811204384557218029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 115078188829878358819248077 43154320811204384557218029)
            ·
              refine ⟨16182870304201644208956761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 43154320811204384557218029 16182870304201644208956761)
              ·
                refine ⟨12137152728151233156717571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16182870304201644208956761 12137152728151233156717571)
                ·
                  refine ⟨18205729092226849735076357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12137152728151233156717571 18205729092226849735076357)
                  ·
                    refine ⟨3413574204792534325326817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 18205729092226849735076357 3413574204792534325326817)
                    ·
                      refine ⟨2560180653594400743995113, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3413574204792534325326817 2560180653594400743995113)
                      ·
                        rfl

theorem cell23_4985934_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 3, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 3, 2, 1, 4, 2].length) (baseStart_4985934 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4985934 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4985934 prefixEnd_4985934 := by exact prefixLift 4985934
  have htrace : WordTrace (prefixWord ++ tailWord_4985934) baseStart_4985934 baseEnd_4985934 := by
    simpa [prefixWord, tailWord_4985934, baseEnd_4985934] using wordTrace_append hprefix tailTrace_4985934
  have hstable : (prefixWord ++ tailWord_4985934).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4985934).length < 2 ^ (prefixWord ++ tailWord_4985934).sum := by decide
  have hdescent : baseEnd_4985934 < baseStart_4985934 := by decide
  rcases family_descends (prefixWord ++ tailWord_4985934) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4985938 : List Nat := [3, 2, 2, 1, 3, 2, 3, 1, 1, 3, 2]
def baseStart_4985938 : Nat := 118140960795 + 4985938 * 2 ^ 59
def prefixEnd_4985938 : Nat := 4983230072969 + 3 ^ 40 * 4985938 * 2
def baseEnd_4985938 : Nat := 2560182707517018728345095

theorem tailTrace_4985938 : CollatzResearch.WordTrace tailWord_4985938 prefixEnd_4985938 2560182707517018728345095 := by
  unfold tailWord_4985938
  simp only [CollatzResearch.WordTrace]
  refine ⟨45463024652701407815427617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 121234732407203754174473645 45463024652701407815427617)
  ·
    refine ⟨34097268489526055861570713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45463024652701407815427617 34097268489526055861570713)
    ·
      refine ⟨25572951367144541896178035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34097268489526055861570713 25572951367144541896178035)
      ·
        refine ⟨38359427050716812844267053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25572951367144541896178035 38359427050716812844267053)
        ·
          refine ⟨14384785144018804816600145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 38359427050716812844267053 14384785144018804816600145)
          ·
            refine ⟨10788588858014103612450109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14384785144018804816600145 10788588858014103612450109)
            ·
              refine ⟨4045720821755288854668791, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10788588858014103612450109 4045720821755288854668791)
              ·
                refine ⟨6068581232632933282003187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4045720821755288854668791 6068581232632933282003187)
                ·
                  refine ⟨9102871848949399923004781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6068581232632933282003187 9102871848949399923004781)
                  ·
                    refine ⟨3413576943356024971126793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9102871848949399923004781 3413576943356024971126793)
                    ·
                      refine ⟨2560182707517018728345095, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3413576943356024971126793 2560182707517018728345095)
                      ·
                        rfl

theorem cell23_4985938_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 2, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 2, 3, 1, 1, 3, 2].length) (baseStart_4985938 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4985938 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4985938 prefixEnd_4985938 := by exact prefixLift 4985938
  have htrace : WordTrace (prefixWord ++ tailWord_4985938) baseStart_4985938 baseEnd_4985938 := by
    simpa [prefixWord, tailWord_4985938, baseEnd_4985938] using wordTrace_append hprefix tailTrace_4985938
  have hstable : (prefixWord ++ tailWord_4985938).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4985938).length < 2 ^ (prefixWord ++ tailWord_4985938).sum := by decide
  have hdescent : baseEnd_4985938 < baseStart_4985938 := by decide
  rcases family_descends (prefixWord ++ tailWord_4985938) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4985951 : List Nat := [1, 1, 2, 3, 1, 1, 6, 2, 2, 2, 2]
def baseStart_4985951 : Nat := 118140960795 + 4985951 * 2 ^ 59
def prefixEnd_4985951 : Nat := 4983230072969 + 3 ^ 40 * 4985951 * 2
def baseEnd_4985951 : Nat := 2560189382765527177482535

theorem tailTrace_4985951 : CollatzResearch.WordTrace tailWord_4985951 prefixEnd_4985951 2560189382765527177482535 := by
  unfold tailWord_4985951
  simp only [CollatzResearch.WordTrace]
  refine ⟨181852572759758534481933707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121235048506505689654622471 181852572759758534481933707)
  ·
    refine ⟨272778859139637801722900561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 181852572759758534481933707 272778859139637801722900561)
    ·
      refine ⟨204584144354728351292175421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 272778859139637801722900561 204584144354728351292175421)
      ·
        refine ⟨76719054133023131734565783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 204584144354728351292175421 76719054133023131734565783)
        ·
          refine ⟨115078581199534697601848675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 76719054133023131734565783 115078581199534697601848675)
          ·
            refine ⟨172617871799302046402773013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 115078581199534697601848675 172617871799302046402773013)
            ·
              refine ⟨8091462740592283425129985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 172617871799302046402773013 8091462740592283425129985)
              ·
                refine ⟨6068597055444212568847489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8091462740592283425129985 6068597055444212568847489)
                ·
                  refine ⟨4551447791583159426635617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6068597055444212568847489 4551447791583159426635617)
                  ·
                    refine ⟨3413585843687369569976713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4551447791583159426635617 3413585843687369569976713)
                    ·
                      refine ⟨2560189382765527177482535, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3413585843687369569976713 2560189382765527177482535)
                      ·
                        rfl

theorem cell23_4985951_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 6, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 6, 2, 2, 2, 2].length) (baseStart_4985951 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4985951 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4985951 prefixEnd_4985951 := by exact prefixLift 4985951
  have htrace : WordTrace (prefixWord ++ tailWord_4985951) baseStart_4985951 baseEnd_4985951 := by
    simpa [prefixWord, tailWord_4985951, baseEnd_4985951] using wordTrace_append hprefix tailTrace_4985951
  have hstable : (prefixWord ++ tailWord_4985951).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4985951).length < 2 ^ (prefixWord ++ tailWord_4985951).sum := by decide
  have hdescent : baseEnd_4985951 < baseStart_4985951 := by decide
  rcases family_descends (prefixWord ++ tailWord_4985951) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4985954 : List Nat := [3, 3, 2, 2, 1, 1, 1, 1, 2, 4, 3]
def baseStart_4985954 : Nat := 118140960795 + 4985954 * 2 ^ 59
def prefixEnd_4985954 : Nat := 4983230072969 + 3 ^ 40 * 4985954 * 2
def baseEnd_4985954 : Nat := 2560190923207490665745021

theorem tailTrace_4985954 : CollatzResearch.WordTrace tailWord_4985954 prefixEnd_4985954 2560190923207490665745021 := by
  unfold tailWord_4985954
  simp only [CollatzResearch.WordTrace]
  refine ⟨45463170544686916498573229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 121235121452498443996195277 45463170544686916498573229)
  ·
    refine ⟨17048688954257593686964961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 45463170544686916498573229 17048688954257593686964961)
    ·
      refine ⟨12786516715693195265223721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17048688954257593686964961 12786516715693195265223721)
      ·
        refine ⟨9589887536769896448917791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12786516715693195265223721 9589887536769896448917791)
        ·
          refine ⟨14384831305154844673376687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9589887536769896448917791 14384831305154844673376687)
          ·
            refine ⟨21577246957732267010065031, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14384831305154844673376687 21577246957732267010065031)
            ·
              refine ⟨32365870436598400515097547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21577246957732267010065031 32365870436598400515097547)
              ·
                refine ⟨48548805654897600772646321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32365870436598400515097547 48548805654897600772646321)
                ·
                  refine ⟨36411604241173200579484741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 48548805654897600772646321 36411604241173200579484741)
                  ·
                    refine ⟨6827175795219975108653389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 36411604241173200579484741 6827175795219975108653389)
                    ·
                      refine ⟨2560190923207490665745021, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6827175795219975108653389 2560190923207490665745021)
                      ·
                        rfl

theorem cell23_4985954_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 1, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 1, 1, 1, 2, 4, 3].length) (baseStart_4985954 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4985954 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4985954 prefixEnd_4985954 := by exact prefixLift 4985954
  have htrace : WordTrace (prefixWord ++ tailWord_4985954) baseStart_4985954 baseEnd_4985954 := by
    simpa [prefixWord, tailWord_4985954, baseEnd_4985954] using wordTrace_append hprefix tailTrace_4985954
  have hstable : (prefixWord ++ tailWord_4985954).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4985954).length < 2 ^ (prefixWord ++ tailWord_4985954).sum := by decide
  have hdescent : baseEnd_4985954 < baseStart_4985954 := by decide
  rcases family_descends (prefixWord ++ tailWord_4985954) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4985967 : List Nat := [1, 1, 2, 1, 3, 3, 3, 1, 2, 3, 3]
def baseStart_4985967 : Nat := 118140960795 + 4985967 * 2 ^ 59
def prefixEnd_4985967 : Nat := 4983230072969 + 3 ^ 40 * 4985967 * 2
def baseEnd_4985967 : Nat := 2560197598455999114882461

theorem tailTrace_4985967 : CollatzResearch.WordTrace tailWord_4985967 prefixEnd_4985967 2560197598455999114882461 := by
  unfold tailWord_4985967
  simp only [CollatzResearch.WordTrace]
  refine ⟨181853156327700569214516155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121235437551800379476344103 181853156327700569214516155)
  ·
    refine ⟨272779734491550853821774233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 181853156327700569214516155 272779734491550853821774233)
    ·
      refine ⟨204584800868663140366330675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 272779734491550853821774233 204584800868663140366330675)
      ·
        refine ⟨306877201302994710549496013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 204584800868663140366330675 306877201302994710549496013)
        ·
          refine ⟨115078950488623016456061005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 306877201302994710549496013 115078950488623016456061005)
          ·
            refine ⟨43154606433233631171022877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 115078950488623016456061005 43154606433233631171022877)
            ·
              refine ⟨16182977412462611689133579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 43154606433233631171022877 16182977412462611689133579)
              ·
                refine ⟨24274466118693917533700369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16182977412462611689133579 24274466118693917533700369)
                ·
                  refine ⟨18205849589020438150275277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 24274466118693917533700369 18205849589020438150275277)
                  ·
                    refine ⟨6827193595882664306353229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 18205849589020438150275277 6827193595882664306353229)
                    ·
                      refine ⟨2560197598455999114882461, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6827193595882664306353229 2560197598455999114882461)
                      ·
                        rfl

theorem cell23_4985967_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 3, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 3, 1, 2, 3, 3].length) (baseStart_4985967 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4985967 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4985967 prefixEnd_4985967 := by exact prefixLift 4985967
  have htrace : WordTrace (prefixWord ++ tailWord_4985967) baseStart_4985967 baseEnd_4985967 := by
    simpa [prefixWord, tailWord_4985967, baseEnd_4985967] using wordTrace_append hprefix tailTrace_4985967
  have hstable : (prefixWord ++ tailWord_4985967).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4985967).length < 2 ^ (prefixWord ++ tailWord_4985967).sum := by decide
  have hdescent : baseEnd_4985967 < baseStart_4985967 := by decide
  rcases family_descends (prefixWord ++ tailWord_4985967) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4986034 : List Nat := [3, 2, 1, 1, 1, 4, 2, 2, 3, 4]
def baseStart_4986034 : Nat := 118140960795 + 4986034 * 2 ^ 59
def prefixEnd_4986034 : Nat := 4983230072969 + 3 ^ 40 * 4986034 * 2
def baseEnd_4986034 : Nat := 853410667219950117581551

theorem tailTrace_4986034 : CollatzResearch.WordTrace tailWord_4986034 prefixEnd_4986034 853410667219950117581551 := by
  unfold tailWord_4986034
  simp only [CollatzResearch.WordTrace]
  refine ⟨45463900004614459914301289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 121237066678971893104803437 45463900004614459914301289)
  ·
    refine ⟨34097925003460844935725967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45463900004614459914301289 34097925003460844935725967)
    ·
      refine ⟨51146887505191267403588951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34097925003460844935725967 51146887505191267403588951)
      ·
        refine ⟨76720331257786901105383427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51146887505191267403588951 76720331257786901105383427)
        ·
          refine ⟨115080496886680351658075141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 76720331257786901105383427 115080496886680351658075141)
          ·
            refine ⟨21577593166252565935889089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 115080496886680351658075141 21577593166252565935889089)
            ·
              refine ⟨16183194874689424451916817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21577593166252565935889089 16183194874689424451916817)
              ·
                refine ⟨12137396156017068338937613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16183194874689424451916817 12137396156017068338937613)
                ·
                  refine ⟨4551523558506400627101605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12137396156017068338937613 4551523558506400627101605)
                  ·
                    refine ⟨853410667219950117581551, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4551523558506400627101605 853410667219950117581551)
                    ·
                      rfl

theorem cell23_4986034_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 4, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 4, 2, 2, 3, 4].length) (baseStart_4986034 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4986034 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4986034 prefixEnd_4986034 := by exact prefixLift 4986034
  have htrace : WordTrace (prefixWord ++ tailWord_4986034) baseStart_4986034 baseEnd_4986034 := by
    simpa [prefixWord, tailWord_4986034, baseEnd_4986034] using wordTrace_append hprefix tailTrace_4986034
  have hstable : (prefixWord ++ tailWord_4986034).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4986034).length < 2 ^ (prefixWord ++ tailWord_4986034).sum := by decide
  have hdescent : baseEnd_4986034 < baseStart_4986034 := by decide
  rcases family_descends (prefixWord ++ tailWord_4986034) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4986044 : List Nat := [2, 2, 2, 3, 2, 1, 2, 1, 1, 4, 3]
def baseStart_4986044 : Nat := 118140960795 + 4986044 * 2 ^ 59
def prefixEnd_4986044 : Nat := 4983230072969 + 3 ^ 40 * 4986044 * 2
def baseEnd_4986044 : Nat := 2560237136466395313619607

theorem tailTrace_4986044 : CollatzResearch.WordTrace tailWord_4986044 prefixEnd_4986044 2560237136466395313619607 := by
  unfold tailWord_4986044
  simp only [CollatzResearch.WordTrace]
  refine ⟨90927982374210805682534593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 121237309832281074243379457 90927982374210805682534593)
  ·
    refine ⟨68195986780658104261900945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 90927982374210805682534593 68195986780658104261900945)
    ·
      refine ⟨51146990085493578196425709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 68195986780658104261900945 51146990085493578196425709)
      ·
        refine ⟨19180121282060091823659641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 51146990085493578196425709 19180121282060091823659641)
        ·
          refine ⟨14385090961545068867744731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19180121282060091823659641 14385090961545068867744731)
          ·
            refine ⟨21577636442317603301617097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14385090961545068867744731 21577636442317603301617097)
            ·
              refine ⟨16183227331738202476212823, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21577636442317603301617097 16183227331738202476212823)
              ·
                refine ⟨24274840997607303714319235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16183227331738202476212823 24274840997607303714319235)
                ·
                  refine ⟨36412261496410955571478853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24274840997607303714319235 36412261496410955571478853)
                  ·
                    refine ⟨6827299030577054169652285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 36412261496410955571478853 6827299030577054169652285)
                    ·
                      refine ⟨2560237136466395313619607, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6827299030577054169652285 2560237136466395313619607)
                      ·
                        rfl

theorem cell23_4986044_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 1, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 1, 2, 1, 1, 4, 3].length) (baseStart_4986044 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4986044 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4986044 prefixEnd_4986044 := by exact prefixLift 4986044
  have htrace : WordTrace (prefixWord ++ tailWord_4986044) baseStart_4986044 baseEnd_4986044 := by
    simpa [prefixWord, tailWord_4986044, baseEnd_4986044] using wordTrace_append hprefix tailTrace_4986044
  have hstable : (prefixWord ++ tailWord_4986044).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4986044).length < 2 ^ (prefixWord ++ tailWord_4986044).sum := by decide
  have hdescent : baseEnd_4986044 < baseStart_4986044 := by decide
  rcases family_descends (prefixWord ++ tailWord_4986044) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4986081 : List Nat := [1, 2, 3, 1, 3, 4, 2, 1, 6]
def baseStart_4986081 : Nat := 118140960795 + 4986081 * 2 ^ 59
def prefixEnd_4986081 : Nat := 4983230072969 + 3 ^ 40 * 4986081 * 2
def baseEnd_4986081 : Nat := 284472903916734629872993

theorem tailTrace_4986081 : CollatzResearch.WordTrace tailWord_4986081 prefixEnd_4986081 284472903916734629872993 := by
  unfold tailWord_4986081
  simp only [CollatzResearch.WordTrace]
  refine ⟨181857314249287566684166097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121238209499525044456110731 181857314249287566684166097)
  ·
    refine ⟨136392985686965675013124573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 181857314249287566684166097 136392985686965675013124573)
    ·
      refine ⟨51147369632612128129921715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 136392985686965675013124573 51147369632612128129921715)
      ·
        refine ⟨76721054448918192194882573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51147369632612128129921715 76721054448918192194882573)
        ·
          refine ⟨28770395418344322073080965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 76721054448918192194882573 28770395418344322073080965)
          ·
            refine ⟨5394449140939560388702681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 28770395418344322073080965 5394449140939560388702681)
            ·
              refine ⟨4045836855704670291527011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5394449140939560388702681 4045836855704670291527011)
              ·
                refine ⟨6068755283557005437290517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4045836855704670291527011 6068755283557005437290517)
                ·
                  refine ⟨284472903916734629872993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6068755283557005437290517 284472903916734629872993)
                  ·
                    rfl

theorem cell23_4986081_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 4, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 4, 2, 1, 6].length) (baseStart_4986081 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4986081 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4986081 prefixEnd_4986081 := by exact prefixLift 4986081
  have htrace : WordTrace (prefixWord ++ tailWord_4986081) baseStart_4986081 baseEnd_4986081 := by
    simpa [prefixWord, tailWord_4986081, baseEnd_4986081] using wordTrace_append hprefix tailTrace_4986081
  have hstable : (prefixWord ++ tailWord_4986081).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4986081).length < 2 ^ (prefixWord ++ tailWord_4986081).sum := by decide
  have hdescent : baseEnd_4986081 < baseStart_4986081 := by decide
  rcases family_descends (prefixWord ++ tailWord_4986081) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4986084 : List Nat := [2, 3, 1, 1, 1, 2, 2, 1, 3, 5, 2]
def baseStart_4986084 : Nat := 118140960795 + 4986084 * 2 ^ 59
def prefixEnd_4986084 : Nat := 4983230072969 + 3 ^ 40 * 4986084 * 2
def baseEnd_4986084 : Nat := 2560257675692575157119423

theorem tailTrace_4986084 : CollatzResearch.WordTrace tailWord_4986084 prefixEnd_4986084 2560257675692575157119423 := by
  unfold tailWord_4986084
  simp only [CollatzResearch.WordTrace]
  refine ⟨90928711834138349098262653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 121238282445517798797683537 90928711834138349098262653)
  ·
    refine ⟨34098266937801880911848495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 90928711834138349098262653 34098266937801880911848495)
    ·
      refine ⟨51147400406702821367772743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34098266937801880911848495 51147400406702821367772743)
      ·
        refine ⟨76721100610054232051659115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51147400406702821367772743 76721100610054232051659115)
        ·
          refine ⟨115081650915081348077488673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 76721100610054232051659115 115081650915081348077488673)
          ·
            refine ⟨86311238186311011058116505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 115081650915081348077488673 86311238186311011058116505)
            ·
              refine ⟨64733428639733258293587379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 86311238186311011058116505 64733428639733258293587379)
              ·
                refine ⟨97100142959599887440381069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 64733428639733258293587379 97100142959599887440381069)
                ·
                  refine ⟨36412553609849957790142901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 97100142959599887440381069 36412553609849957790142901)
                  ·
                    refine ⟨3413676900923433542825897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 36412553609849957790142901 3413676900923433542825897)
                    ·
                      refine ⟨2560257675692575157119423, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3413676900923433542825897 2560257675692575157119423)
                      ·
                        rfl

theorem cell23_4986084_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 2, 1, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 2, 1, 3, 5, 2].length) (baseStart_4986084 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4986084 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4986084 prefixEnd_4986084 := by exact prefixLift 4986084
  have htrace : WordTrace (prefixWord ++ tailWord_4986084) baseStart_4986084 baseEnd_4986084 := by
    simpa [prefixWord, tailWord_4986084, baseEnd_4986084] using wordTrace_append hprefix tailTrace_4986084
  have hstable : (prefixWord ++ tailWord_4986084).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4986084).length < 2 ^ (prefixWord ++ tailWord_4986084).sum := by decide
  have hdescent : baseEnd_4986084 < baseStart_4986084 := by decide
  rcases family_descends (prefixWord ++ tailWord_4986084) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4986111 : List Nat := [1, 1, 2, 2, 1, 6, 3, 1, 1, 5]
def baseStart_4986111 : Nat := 118140960795 + 4986111 * 2 ^ 59
def prefixEnd_4986111 : Nat := 4983230072969 + 3 ^ 40 * 4986111 * 2
def baseEnd_4986111 : Nat := 853423846556748850493933

theorem tailTrace_4986111 : CollatzResearch.WordTrace tailWord_4986111 prefixEnd_4986111 853423846556748850493933 := by
  unfold tailWord_4986111
  simp only [CollatzResearch.WordTrace]
  refine ⟨181858408439178881807758187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121238938959452587871838791 181858408439178881807758187)
  ·
    refine ⟨272787612658768322711637281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 181858408439178881807758187 272787612658768322711637281)
    ·
      refine ⟨204590709494076242033727961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 272787612658768322711637281 204590709494076242033727961)
      ·
        refine ⟨153443032120557181525295971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 204590709494076242033727961 153443032120557181525295971)
        ·
          refine ⟨230164548180835772287943957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 153443032120557181525295971 230164548180835772287943957)
          ·
            refine ⟨10788963195976676825997373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 230164548180835772287943957 10788963195976676825997373)
            ·
              refine ⟨4045861198491253809749015, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10788963195976676825997373 4045861198491253809749015)
              ·
                refine ⟨6068791797736880714623523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4045861198491253809749015 6068791797736880714623523)
                ·
                  refine ⟨9103187696605321071935285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6068791797736880714623523 9103187696605321071935285)
                  ·
                    refine ⟨853423846556748850493933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9103187696605321071935285 853423846556748850493933)
                    ·
                      rfl

theorem cell23_4986111_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 6, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 6, 3, 1, 1, 5].length) (baseStart_4986111 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4986111 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4986111 prefixEnd_4986111 := by exact prefixLift 4986111
  have htrace : WordTrace (prefixWord ++ tailWord_4986111) baseStart_4986111 baseEnd_4986111 := by
    simpa [prefixWord, tailWord_4986111, baseEnd_4986111] using wordTrace_append hprefix tailTrace_4986111
  have hstable : (prefixWord ++ tailWord_4986111).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4986111).length < 2 ^ (prefixWord ++ tailWord_4986111).sum := by decide
  have hdescent : baseEnd_4986111 < baseStart_4986111 := by decide
  rcases family_descends (prefixWord ++ tailWord_4986111) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4986141 : List Nat := [1, 4, 2, 3, 1, 2, 2, 1, 1, 6]
def baseStart_4986141 : Nat := 118140960795 + 4986141 * 2 ^ 59
def prefixEnd_4986141 : Nat := 4983230072969 + 3 ^ 40 * 4986141 * 2
def baseEnd_4986141 : Nat := 853428981363293811368887

theorem tailTrace_4986141 : CollatzResearch.WordTrace tailWord_4986141 prefixEnd_4986141 853428981363293811368887 := by
  unfold tailWord_4986141
  simp only [CollatzResearch.WordTrace]
  refine ⟨181859502629070196931350277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121239668419380131287566851 181859502629070196931350277)
  ·
    refine ⟨34098656742950661924628177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 181859502629070196931350277 34098656742950661924628177)
    ·
      refine ⟨25573992557212996443471133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34098656742950661924628177 25573992557212996443471133)
      ·
        refine ⟨9590247208954873666301675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 25573992557212996443471133 9590247208954873666301675)
        ·
          refine ⟨14385370813432310499452513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9590247208954873666301675 14385370813432310499452513)
          ·
            refine ⟨10789028110074232874589385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14385370813432310499452513 10789028110074232874589385)
            ·
              refine ⟨8091771082555674655942039, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10789028110074232874589385 8091771082555674655942039)
              ·
                refine ⟨12137656623833511983913059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8091771082555674655942039 12137656623833511983913059)
                ·
                  refine ⟨18206484935750267975869589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12137656623833511983913059 18206484935750267975869589)
                  ·
                    refine ⟨853428981363293811368887, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 18206484935750267975869589 853428981363293811368887)
                    ·
                      rfl

theorem cell23_4986141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 2, 2, 1, 1, 6].length) (baseStart_4986141 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4986141 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4986141 prefixEnd_4986141 := by exact prefixLift 4986141
  have htrace : WordTrace (prefixWord ++ tailWord_4986141) baseStart_4986141 baseEnd_4986141 := by
    simpa [prefixWord, tailWord_4986141, baseEnd_4986141] using wordTrace_append hprefix tailTrace_4986141
  have hstable : (prefixWord ++ tailWord_4986141).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4986141).length < 2 ^ (prefixWord ++ tailWord_4986141).sum := by decide
  have hdescent : baseEnd_4986141 < baseStart_4986141 := by decide
  rcases family_descends (prefixWord ++ tailWord_4986141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4986148 : List Nat := [2, 3, 1, 3, 1, 1, 3, 2, 3, 2, 2]
def baseStart_4986148 : Nat := 118140960795 + 4986148 * 2 ^ 59
def prefixEnd_4986148 : Nat := 4983230072969 + 3 ^ 40 * 4986148 * 2
def baseEnd_4986148 : Nat := 2560290538454462906719129

theorem tailTrace_4986148 : CollatzResearch.WordTrace tailWord_4986148 prefixEnd_4986148 2560290538454462906719129 := by
  unfold tailWord_4986148
  simp only [CollatzResearch.WordTrace]
  refine ⟨90929878970022418563427549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 121239838626696558084570065 90929878970022418563427549)
  ·
    refine ⟨34098704613758406961285331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 90929878970022418563427549 34098704613758406961285331)
    ·
      refine ⟨51148056920637610441927997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34098704613758406961285331 51148056920637610441927997)
      ·
        refine ⟨19180521345239103915722999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 51148056920637610441927997 19180521345239103915722999)
        ·
          refine ⟨28770782017858655873584499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19180521345239103915722999 28770782017858655873584499)
          ·
            refine ⟨43156173026787983810376749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28770782017858655873584499 43156173026787983810376749)
            ·
              refine ⟨16183564885045493928891281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 43156173026787983810376749 16183564885045493928891281)
              ·
                refine ⟨12137673663784120446668461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16183564885045493928891281 12137673663784120446668461)
                ·
                  refine ⟨4551627623919045167500673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12137673663784120446668461 4551627623919045167500673)
                  ·
                    refine ⟨3413720717939283875625505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4551627623919045167500673 3413720717939283875625505)
                    ·
                      refine ⟨2560290538454462906719129, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3413720717939283875625505 2560290538454462906719129)
                      ·
                        rfl

theorem cell23_4986148_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 3, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 3, 2, 3, 2, 2].length) (baseStart_4986148 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4986148 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4986148 prefixEnd_4986148 := by exact prefixLift 4986148
  have htrace : WordTrace (prefixWord ++ tailWord_4986148) baseStart_4986148 baseEnd_4986148 := by
    simpa [prefixWord, tailWord_4986148, baseEnd_4986148] using wordTrace_append hprefix tailTrace_4986148
  have hstable : (prefixWord ++ tailWord_4986148).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4986148).length < 2 ^ (prefixWord ++ tailWord_4986148).sum := by decide
  have hdescent : baseEnd_4986148 < baseStart_4986148 := by decide
  rcases family_descends (prefixWord ++ tailWord_4986148) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4986165 : List Nat := [1, 3, 3, 1, 2, 2, 1, 5, 1, 2, 2]
def baseStart_4986165 : Nat := 118140960795 + 4986165 * 2 ^ 59
def prefixEnd_4986165 : Nat := 4983230072969 + 3 ^ 40 * 4986165 * 2
def baseEnd_4986165 : Nat := 2560299267625589340206551

theorem tailTrace_4986165 : CollatzResearch.WordTrace tailWord_4986165 prefixEnd_4986165 2560299267625589340206551 := by
  unfold tailWord_4986165
  simp only [CollatzResearch.WordTrace]
  refine ⟨181860377980983249030223949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121240251987322166020149299 181860377980983249030223949)
  ·
    refine ⟨68197641742868718386333981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 181860377980983249030223949 68197641742868718386333981)
    ·
      refine ⟨25574115653575769394875243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 68197641742868718386333981 25574115653575769394875243)
      ·
        refine ⟨38361173480363654092312865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25574115653575769394875243 38361173480363654092312865)
        ·
          refine ⟨28770880110272740569234649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38361173480363654092312865 28770880110272740569234649)
          ·
            refine ⟨21578160082704555426925987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28770880110272740569234649 21578160082704555426925987)
            ·
              refine ⟨32367240124056833140388981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21578160082704555426925987 32367240124056833140388981)
              ·
                refine ⟨3034428761630328106911467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 32367240124056833140388981 3034428761630328106911467)
                ·
                  refine ⟨4551643142445492160367201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3034428761630328106911467 4551643142445492160367201)
                  ·
                    refine ⟨3413732356834119120275401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4551643142445492160367201 3413732356834119120275401)
                    ·
                      refine ⟨2560299267625589340206551, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3413732356834119120275401 2560299267625589340206551)
                      ·
                        rfl

theorem cell23_4986165_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 2, 1, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 2, 1, 5, 1, 2, 2].length) (baseStart_4986165 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4986165 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4986165 prefixEnd_4986165 := by exact prefixLift 4986165
  have htrace : WordTrace (prefixWord ++ tailWord_4986165) baseStart_4986165 baseEnd_4986165 := by
    simpa [prefixWord, tailWord_4986165, baseEnd_4986165] using wordTrace_append hprefix tailTrace_4986165
  have hstable : (prefixWord ++ tailWord_4986165).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4986165).length < 2 ^ (prefixWord ++ tailWord_4986165).sum := by decide
  have hdescent : baseEnd_4986165 < baseStart_4986165 := by decide
  rcases family_descends (prefixWord ++ tailWord_4986165) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4986208 : List Nat := [2, 1, 1, 3, 4, 1, 1, 4, 1, 3, 2]
def baseStart_4986208 : Nat := 118140960795 + 4986208 * 2 ^ 59
def prefixEnd_4986208 : Nat := 4983230072969 + 3 ^ 40 * 4986208 * 2
def baseEnd_4986208 : Nat := 2560321347293732671968853

theorem tailTrace_4986208 : CollatzResearch.WordTrace tailWord_4986208 prefixEnd_4986208 2560321347293732671968853 := by
  unfold tailWord_4986208
  simp only [CollatzResearch.WordTrace]
  refine ⟨90930973159913733687019639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 121241297546551644916026185 90930973159913733687019639)
  ·
    refine ⟨136396459739870600530529459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90930973159913733687019639 136396459739870600530529459)
    ·
      refine ⟨204594689609805900795794189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 136396459739870600530529459 204594689609805900795794189)
      ·
        refine ⟨76723008603677212798422821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 204594689609805900795794189 76723008603677212798422821)
        ·
          refine ⟨14385564113189477399704279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 76723008603677212798422821 14385564113189477399704279)
          ·
            refine ⟨21578346169784216099556419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14385564113189477399704279 21578346169784216099556419)
            ·
              refine ⟨32367519254676324149334629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21578346169784216099556419 32367519254676324149334629)
              ·
                refine ⟨6068909860251810778000243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 32367519254676324149334629 6068909860251810778000243)
                ·
                  refine ⟨9103364790377716167000365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6068909860251810778000243 9103364790377716167000365)
                  ·
                    refine ⟨3413761796391643562625137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9103364790377716167000365 3413761796391643562625137)
                    ·
                      refine ⟨2560321347293732671968853, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3413761796391643562625137 2560321347293732671968853)
                      ·
                        rfl

theorem cell23_4986208_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 1, 1, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 1, 1, 4, 1, 3, 2].length) (baseStart_4986208 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4986208 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4986208 prefixEnd_4986208 := by exact prefixLift 4986208
  have htrace : WordTrace (prefixWord ++ tailWord_4986208) baseStart_4986208 baseEnd_4986208 := by
    simpa [prefixWord, tailWord_4986208, baseEnd_4986208] using wordTrace_append hprefix tailTrace_4986208
  have hstable : (prefixWord ++ tailWord_4986208).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4986208).length < 2 ^ (prefixWord ++ tailWord_4986208).sum := by decide
  have hdescent : baseEnd_4986208 < baseStart_4986208 := by decide
  rcases family_descends (prefixWord ++ tailWord_4986208) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4986224 : List Nat := [2, 1, 1, 1, 4, 2, 3, 1, 2, 1, 5]
def baseStart_4986224 : Nat := 118140960795 + 4986224 * 2 ^ 59
def prefixEnd_4986224 : Nat := 4983230072969 + 3 ^ 40 * 4986224 * 2
def baseEnd_4986224 : Nat := 2560329562984204609368779

theorem tailTrace_4986224 : CollatzResearch.WordTrace tailWord_4986224 prefixEnd_4986224 2560329562984204609368779 := by
  unfold tailWord_4986224
  simp only [CollatzResearch.WordTrace]
  refine ⟨90931264943884751053310863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 121241686591846334737747817 90931264943884751053310863)
  ·
    refine ⟨136396897415827126579966295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90931264943884751053310863 136396897415827126579966295)
    ·
      refine ⟨204595346123740689869949443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 136396897415827126579966295 204595346123740689869949443)
      ·
        refine ⟨306893019185611034804924165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 204595346123740689869949443 306893019185611034804924165)
        ·
          refine ⟨57542441097302069025923281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 306893019185611034804924165 57542441097302069025923281)
          ·
            refine ⟨43156830822976551769442461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 57542441097302069025923281 43156830822976551769442461)
            ·
              refine ⟨16183811558616206913540923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 43156830822976551769442461 16183811558616206913540923)
              ·
                refine ⟨24275717337924310370311385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16183811558616206913540923 24275717337924310370311385)
                ·
                  refine ⟨18206788003443232777733539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 24275717337924310370311385 18206788003443232777733539)
                  ·
                    refine ⟨27310182005164849166600309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 18206788003443232777733539 27310182005164849166600309)
                    ·
                      refine ⟨2560329562984204609368779, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 27310182005164849166600309 2560329562984204609368779)
                      ·
                        rfl

theorem cell23_4986224_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 3, 1, 2, 1, 5].length) (baseStart_4986224 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4986224 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4986224 prefixEnd_4986224 := by exact prefixLift 4986224
  have htrace : WordTrace (prefixWord ++ tailWord_4986224) baseStart_4986224 baseEnd_4986224 := by
    simpa [prefixWord, tailWord_4986224, baseEnd_4986224] using wordTrace_append hprefix tailTrace_4986224
  have hstable : (prefixWord ++ tailWord_4986224).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4986224).length < 2 ^ (prefixWord ++ tailWord_4986224).sum := by decide
  have hdescent : baseEnd_4986224 < baseStart_4986224 := by decide
  rcases family_descends (prefixWord ++ tailWord_4986224) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4986284 : List Nat := [2, 2, 1, 1, 1, 1, 5, 2, 1, 2, 5]
def baseStart_4986284 : Nat := 118140960795 + 4986284 * 2 ^ 59
def prefixEnd_4986284 : Nat := 4983230072969 + 3 ^ 40 * 4986284 * 2
def baseEnd_4986284 : Nat := 2560360371823474374618503

theorem tailTrace_4986284 : CollatzResearch.WordTrace tailWord_4986284 prefixEnd_4986284 2560360371823474374618503 := by
  unfold tailWord_4986284
  simp only [CollatzResearch.WordTrace]
  refine ⟨90932359133776066176902953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 121243145511701421569203937 90932359133776066176902953)
  ·
    refine ⟨68199269350332049632677215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 90932359133776066176902953 68199269350332049632677215)
    ·
      refine ⟨102298904025498074449015823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68199269350332049632677215 102298904025498074449015823)
      ·
        refine ⟨153448356038247111673523735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 102298904025498074449015823 153448356038247111673523735)
        ·
          refine ⟨230172534057370667510285603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 153448356038247111673523735 230172534057370667510285603)
          ·
            refine ⟨345258801086056001265428405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 230172534057370667510285603 345258801086056001265428405)
            ·
              refine ⟨32368012601817750118633913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 345258801086056001265428405 32368012601817750118633913)
              ·
                refine ⟨24276009451363312588975435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 32368012601817750118633913 24276009451363312588975435)
                ·
                  refine ⟨36414014177044968883463153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24276009451363312588975435 36414014177044968883463153)
                  ·
                    refine ⟨27310510632783726662597365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 36414014177044968883463153 27310510632783726662597365)
                    ·
                      refine ⟨2560360371823474374618503, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 27310510632783726662597365 2560360371823474374618503)
                      ·
                        rfl

theorem cell23_4986284_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 2, 5].length) (baseStart_4986284 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4986284 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4986284 prefixEnd_4986284 := by exact prefixLift 4986284
  have htrace : WordTrace (prefixWord ++ tailWord_4986284) baseStart_4986284 baseEnd_4986284 := by
    simpa [prefixWord, tailWord_4986284, baseEnd_4986284] using wordTrace_append hprefix tailTrace_4986284
  have hstable : (prefixWord ++ tailWord_4986284).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4986284).length < 2 ^ (prefixWord ++ tailWord_4986284).sum := by decide
  have hdescent : baseEnd_4986284 < baseStart_4986284 := by decide
  rcases family_descends (prefixWord ++ tailWord_4986284) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4986306 : List Nat := [3, 5, 2, 1, 1, 1, 2, 1, 1, 4, 2]
def baseStart_4986306 : Nat := 118140960795 + 4986306 * 2 ^ 59
def prefixEnd_4986306 : Nat := 4983230072969 + 3 ^ 40 * 4986306 * 2
def baseEnd_4986306 : Nat := 2560371668397873288543403

theorem tailTrace_4986306 : CollatzResearch.WordTrace tailWord_4986306 prefixEnd_4986306 2560371668397873288543403 := by
  unfold tailWord_4986306
  simp only [CollatzResearch.WordTrace]
  refine ⟨45466380168368107527776693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 121243680448981620074071181 45466380168368107527776693)
  ·
    refine ⟨4262473140784510080729065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 45466380168368107527776693 4262473140784510080729065)
    ·
      refine ⟨3196854855588382560546799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4262473140784510080729065 3196854855588382560546799)
      ·
        refine ⟨4795282283382573840820199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3196854855588382560546799 4795282283382573840820199)
        ·
          refine ⟨7192923425073860761230299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4795282283382573840820199 7192923425073860761230299)
          ·
            refine ⟨10789385137610791141845449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7192923425073860761230299 10789385137610791141845449)
            ·
              refine ⟨8092038853208093356384087, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10789385137610791141845449 8092038853208093356384087)
              ·
                refine ⟨12138058279812140034576131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8092038853208093356384087 12138058279812140034576131)
                ·
                  refine ⟨18207087419718210051864197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12138058279812140034576131 18207087419718210051864197)
                  ·
                    refine ⟨3413828891197164384724537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 18207087419718210051864197 3413828891197164384724537)
                    ·
                      refine ⟨2560371668397873288543403, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3413828891197164384724537 2560371668397873288543403)
                      ·
                        rfl

theorem cell23_4986306_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 2, 1, 1, 1, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 2, 1, 1, 1, 2, 1, 1, 4, 2].length) (baseStart_4986306 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4986306 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4986306 prefixEnd_4986306 := by exact prefixLift 4986306
  have htrace : WordTrace (prefixWord ++ tailWord_4986306) baseStart_4986306 baseEnd_4986306 := by
    simpa [prefixWord, tailWord_4986306, baseEnd_4986306] using wordTrace_append hprefix tailTrace_4986306
  have hstable : (prefixWord ++ tailWord_4986306).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4986306).length < 2 ^ (prefixWord ++ tailWord_4986306).sum := by decide
  have hdescent : baseEnd_4986306 < baseStart_4986306 := by decide
  rcases family_descends (prefixWord ++ tailWord_4986306) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4986341 : List Nat := [1, 3, 1, 5, 1, 1, 1, 1, 2, 1, 6]
def baseStart_4986341 : Nat := 118140960795 + 4986341 * 2 ^ 59
def prefixEnd_4986341 : Nat := 4983230072969 + 3 ^ 40 * 4986341 * 2
def baseEnd_4986341 : Nat := 2560389640220780651605741

theorem tailTrace_4986341 : CollatzResearch.WordTrace tailWord_4986341 prefixEnd_4986341 2560389640220780651605741 := by
  unfold tailWord_4986341
  simp only [CollatzResearch.WordTrace]
  refine ⟨181866797228345631088630877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121244531485563754059087251 181866797228345631088630877)
  ·
    refine ⟨68200048960629611658236579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 181866797228345631088630877 68200048960629611658236579)
    ·
      refine ⟨102300073440944417487354869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68200048960629611658236579 102300073440944417487354869)
      ·
        refine ⟨9590631885088539139439519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 102300073440944417487354869 9590631885088539139439519)
        ·
          refine ⟨14385947827632808709159279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9590631885088539139439519 14385947827632808709159279)
          ·
            refine ⟨21578921741449213063738919, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14385947827632808709159279 21578921741449213063738919)
            ·
              refine ⟨32368382612173819595608379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21578921741449213063738919 32368382612173819595608379)
              ·
                refine ⟨48552573918260729393412569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32368382612173819595608379 48552573918260729393412569)
                ·
                  refine ⟨36414430438695547045059427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 48552573918260729393412569 36414430438695547045059427)
                  ·
                    refine ⟨54621645658043320567589141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 36414430438695547045059427 54621645658043320567589141)
                    ·
                      refine ⟨2560389640220780651605741, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 54621645658043320567589141 2560389640220780651605741)
                      ·
                        rfl

theorem cell23_4986341_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 1, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 1, 1, 1, 2, 1, 6].length) (baseStart_4986341 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4986341 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4986341 prefixEnd_4986341 := by exact prefixLift 4986341
  have htrace : WordTrace (prefixWord ++ tailWord_4986341) baseStart_4986341 baseEnd_4986341 := by
    simpa [prefixWord, tailWord_4986341, baseEnd_4986341] using wordTrace_append hprefix tailTrace_4986341
  have hstable : (prefixWord ++ tailWord_4986341).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4986341).length < 2 ^ (prefixWord ++ tailWord_4986341).sum := by decide
  have hdescent : baseEnd_4986341 < baseStart_4986341 := by decide
  rcases family_descends (prefixWord ++ tailWord_4986341) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4986351 : List Nat := [1, 1, 2, 1, 4, 1, 5, 2, 6]
def baseStart_4986351 : Nat := 118140960795 + 4986351 * 2 ^ 59
def prefixEnd_4986351 : Nat := 4983230072969 + 3 ^ 40 * 4986351 * 2
def baseEnd_4986351 : Nat := 284488308336369512497855

theorem tailTrace_4986351 : CollatzResearch.WordTrace tailWord_4986351 prefixEnd_4986351 284488308336369512497855 := by
  unfold tailWord_4986351
  simp only [CollatzResearch.WordTrace]
  refine ⟨181867161958309402796494907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121244774638872935197663271 181867161958309402796494907)
  ·
    refine ⟨272800742937464104194742361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 181867161958309402796494907 272800742937464104194742361)
    ·
      refine ⟨204600557203098078146056771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 272800742937464104194742361 204600557203098078146056771)
      ·
        refine ⟨306900835804647117219085157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 204600557203098078146056771 306900835804647117219085157)
        ·
          refine ⟨57543906713371334478578467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 306900835804647117219085157 57543906713371334478578467)
          ·
            refine ⟨86315860070057001717867701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 57543906713371334478578467 86315860070057001717867701)
            ·
              refine ⟨8092111881567843911050097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 86315860070057001717867701 8092111881567843911050097)
              ·
                refine ⟨6069083911175882933287573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8092111881567843911050097 6069083911175882933287573)
                ·
                  refine ⟨284488308336369512497855, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6069083911175882933287573 284488308336369512497855)
                  ·
                    rfl

theorem cell23_4986351_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 5, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 5, 2, 6].length) (baseStart_4986351 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4986351 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4986351 prefixEnd_4986351 := by exact prefixLift 4986351
  have htrace : WordTrace (prefixWord ++ tailWord_4986351) baseStart_4986351 baseEnd_4986351 := by
    simpa [prefixWord, tailWord_4986351, baseEnd_4986351] using wordTrace_append hprefix tailTrace_4986351
  have hstable : (prefixWord ++ tailWord_4986351).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4986351).length < 2 ^ (prefixWord ++ tailWord_4986351).sum := by decide
  have hdescent : baseEnd_4986351 < baseStart_4986351 := by decide
  rcases family_descends (prefixWord ++ tailWord_4986351) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4986431 : List Nat := [1, 1, 2, 2, 3, 3, 2, 1, 1, 1, 6]
def baseStart_4986431 : Nat := 118140960795 + 4986431 * 2 ^ 59
def prefixEnd_4986431 : Nat := 4983230072969 + 3 ^ 40 * 4986431 * 2
def baseEnd_4986431 : Nat := 2560435853479685299480327

theorem tailTrace_4986431 : CollatzResearch.WordTrace tailWord_4986431 prefixEnd_4986431 2560435853479685299480327 := by
  unfold tailWord_4986431
  simp only [CollatzResearch.WordTrace]
  refine ⟨181870079798019576459407147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121246719865346384306271431 181870079798019576459407147)
  ·
    refine ⟨272805119697029364689110721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 181870079798019576459407147 272805119697029364689110721)
    ·
      refine ⟨204603839772772023516833041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 272805119697029364689110721 204603839772772023516833041)
      ·
        refine ⟨153452879829579017637624781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 204603839772772023516833041 153452879829579017637624781)
        ·
          refine ⟨57544829936092131614109293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 153452879829579017637624781 57544829936092131614109293)
          ·
            refine ⟨21579311226034549355290985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 57544829936092131614109293 21579311226034549355290985)
            ·
              refine ⟨16184483419525912016468239, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21579311226034549355290985 16184483419525912016468239)
              ·
                refine ⟨24276725129288868024702359, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16184483419525912016468239 24276725129288868024702359)
                ·
                  refine ⟨36415087693933302037053539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24276725129288868024702359 36415087693933302037053539)
                  ·
                    refine ⟨54622631540899953055580309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 36415087693933302037053539 54622631540899953055580309)
                    ·
                      refine ⟨2560435853479685299480327, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 54622631540899953055580309 2560435853479685299480327)
                      ·
                        rfl

theorem cell23_4986431_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 3, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 3, 2, 1, 1, 1, 6].length) (baseStart_4986431 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4986431 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4986431 prefixEnd_4986431 := by exact prefixLift 4986431
  have htrace : WordTrace (prefixWord ++ tailWord_4986431) baseStart_4986431 baseEnd_4986431 := by
    simpa [prefixWord, tailWord_4986431, baseEnd_4986431] using wordTrace_append hprefix tailTrace_4986431
  have hstable : (prefixWord ++ tailWord_4986431).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4986431).length < 2 ^ (prefixWord ++ tailWord_4986431).sum := by decide
  have hdescent : baseEnd_4986431 < baseStart_4986431 := by decide
  rcases family_descends (prefixWord ++ tailWord_4986431) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4986445 : List Nat := [1, 6, 1, 1, 3, 1, 1, 2, 1, 6]
def baseStart_4986445 : Nat := 118140960795 + 4986445 * 2 ^ 59
def prefixEnd_4986445 : Nat := 4983230072969 + 3 ^ 40 * 4986445 * 2
def baseEnd_4986445 : Nat := 853481014069616081568421

theorem tailTrace_4986445 : CollatzResearch.WordTrace tailWord_4986445 prefixEnd_4986445 853481014069616081568421 := by
  unfold tailWord_4986445
  simp only [CollatzResearch.WordTrace]
  refine ⟨181870590419968856850416789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121247060279979237900277859 181870590419968856850416789)
  ·
    refine ⟨8525183925936040164863287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 181870590419968856850416789 8525183925936040164863287)
    ·
      refine ⟨12787775888904060247294931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8525183925936040164863287 12787775888904060247294931)
      ·
        refine ⟨19181663833356090370942397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12787775888904060247294931 19181663833356090370942397)
        ·
          refine ⟨7193123937508533889103399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19181663833356090370942397 7193123937508533889103399)
          ·
            refine ⟨10789685906262800833655099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7193123937508533889103399 10789685906262800833655099)
            ·
              refine ⟨16184528859394201250482649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10789685906262800833655099 16184528859394201250482649)
              ·
                refine ⟨12138396644545650937861987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16184528859394201250482649 12138396644545650937861987)
                ·
                  refine ⟨18207594966818476406792981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12138396644545650937861987 18207594966818476406792981)
                  ·
                    refine ⟨853481014069616081568421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 18207594966818476406792981 853481014069616081568421)
                    ·
                      rfl

theorem cell23_4986445_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 3, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 3, 1, 1, 2, 1, 6].length) (baseStart_4986445 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4986445 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4986445 prefixEnd_4986445 := by exact prefixLift 4986445
  have htrace : WordTrace (prefixWord ++ tailWord_4986445) baseStart_4986445 baseEnd_4986445 := by
    simpa [prefixWord, tailWord_4986445, baseEnd_4986445] using wordTrace_append hprefix tailTrace_4986445
  have hstable : (prefixWord ++ tailWord_4986445).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4986445).length < 2 ^ (prefixWord ++ tailWord_4986445).sum := by decide
  have hdescent : baseEnd_4986445 < baseStart_4986445 := by decide
  rcases family_descends (prefixWord ++ tailWord_4986445) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4986469 : List Nat := [1, 3, 1, 3, 3, 2, 1, 4, 1, 2, 2]
def baseStart_4986469 : Nat := 118140960795 + 4986469 * 2 ^ 59
def prefixEnd_4986469 : Nat := 4983230072969 + 3 ^ 40 * 4986469 * 2
def baseEnd_4986469 : Nat := 2560455365744556150805153

theorem tailTrace_4986469 : CollatzResearch.WordTrace tailWord_4986469 prefixEnd_4986469 2560455365744556150805153 := by
  unfold tailWord_4986469
  simp only [CollatzResearch.WordTrace]
  refine ⟨181871465771881908949290461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121247643847921272632860307 181871465771881908949290461)
  ·
    refine ⟨68201799664455715855983923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 181871465771881908949290461 68201799664455715855983923)
    ·
      refine ⟨102302699496683573783975885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68201799664455715855983923 102302699496683573783975885)
      ·
        refine ⟨38363512311256340168990957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 102302699496683573783975885 38363512311256340168990957)
        ·
          refine ⟨14386317116721127563371609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 38363512311256340168990957 14386317116721127563371609)
          ·
            refine ⟨10789737837540845672528707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14386317116721127563371609 10789737837540845672528707)
            ·
              refine ⟨16184606756311268508793061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10789737837540845672528707 16184606756311268508793061)
              ·
                refine ⟨3034613766808362845398699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 16184606756311268508793061 3034613766808362845398699)
                ·
                  refine ⟨4551920650212544268098049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3034613766808362845398699 4551920650212544268098049)
                  ·
                    refine ⟨3413940487659408201073537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4551920650212544268098049 3413940487659408201073537)
                    ·
                      refine ⟨2560455365744556150805153, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3413940487659408201073537 2560455365744556150805153)
                      ·
                        rfl

theorem cell23_4986469_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 2, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 2, 1, 4, 1, 2, 2].length) (baseStart_4986469 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4986469 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4986469 prefixEnd_4986469 := by exact prefixLift 4986469
  have htrace : WordTrace (prefixWord ++ tailWord_4986469) baseStart_4986469 baseEnd_4986469 := by
    simpa [prefixWord, tailWord_4986469, baseEnd_4986469] using wordTrace_append hprefix tailTrace_4986469
  have hstable : (prefixWord ++ tailWord_4986469).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4986469).length < 2 ^ (prefixWord ++ tailWord_4986469).sum := by decide
  have hdescent : baseEnd_4986469 < baseStart_4986469 := by decide
  rcases family_descends (prefixWord ++ tailWord_4986469) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4986471 : List Nat := [1, 1, 5, 1, 1, 1, 3, 1, 2, 7]
def baseStart_4986471 : Nat := 118140960795 + 4986471 * 2 ^ 59
def prefixEnd_4986471 : Nat := 4983230072969 + 3 ^ 40 * 4986471 * 2
def baseEnd_4986471 : Nat := 853485464235288380993381

theorem tailTrace_4986471 : CollatzResearch.WordTrace tailWord_4986471 prefixEnd_4986471 853485464235288380993381 := by
  unfold tailWord_4986471
  simp only [CollatzResearch.WordTrace]
  refine ⟨181871538717874663290863267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121247692478583108860575511 181871538717874663290863267)
  ·
    refine ⟨272807308076811994936294901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 181871538717874663290863267 272807308076811994936294901)
    ·
      refine ⟨25575685132201124525277647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 272807308076811994936294901 25575685132201124525277647)
      ·
        refine ⟨38363527698301686787916471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25575685132201124525277647 38363527698301686787916471)
        ·
          refine ⟨57545291547452530181874707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38363527698301686787916471 57545291547452530181874707)
          ·
            refine ⟨86317937321178795272812061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 57545291547452530181874707 86317937321178795272812061)
            ·
              refine ⟨32369226495442048227304523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 86317937321178795272812061 32369226495442048227304523)
              ·
                refine ⟨48553839743163072340956785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32369226495442048227304523 48553839743163072340956785)
                ·
                  refine ⟨36415379807372304255717589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 48553839743163072340956785 36415379807372304255717589)
                  ·
                    refine ⟨853485464235288380993381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 36415379807372304255717589 853485464235288380993381)
                    ·
                      rfl

theorem cell23_4986471_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 3, 1, 2, 7].length) (baseStart_4986471 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4986471 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4986471 prefixEnd_4986471 := by exact prefixLift 4986471
  have htrace : WordTrace (prefixWord ++ tailWord_4986471) baseStart_4986471 baseEnd_4986471 := by
    simpa [prefixWord, tailWord_4986471, baseEnd_4986471] using wordTrace_append hprefix tailTrace_4986471
  have hstable : (prefixWord ++ tailWord_4986471).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4986471).length < 2 ^ (prefixWord ++ tailWord_4986471).sum := by decide
  have hdescent : baseEnd_4986471 < baseStart_4986471 := by decide
  rcases family_descends (prefixWord ++ tailWord_4986471) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4986485 : List Nat := [1, 3, 4, 2, 1, 1, 1, 3, 1, 3, 3]
def baseStart_4986485 : Nat := 118140960795 + 4986485 * 2 ^ 59
def prefixEnd_4986485 : Nat := 4983230072969 + 3 ^ 40 * 4986485 * 2
def baseEnd_4986485 : Nat := 2560463581435028088205079

theorem tailTrace_4986485 : CollatzResearch.WordTrace tailWord_4986485 prefixEnd_4986485 2560463581435028088205079 := by
  unfold tailWord_4986485
  simp only [CollatzResearch.WordTrace]
  refine ⟨181872049339823943681872909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121248032893215962454581939 181872049339823943681872909)
  ·
    refine ⟨68202018502433978880702341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 181872049339823943681872909 68202018502433978880702341)
    ·
      refine ⟨12787878469206371040131689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 68202018502433978880702341 12787878469206371040131689)
      ·
        refine ⟨9590908851904778280098767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12787878469206371040131689 9590908851904778280098767)
        ·
          refine ⟨14386363277857167420148151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9590908851904778280098767 14386363277857167420148151)
          ·
            refine ⟨21579544916785751130222227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14386363277857167420148151 21579544916785751130222227)
            ·
              refine ⟨32369317375178626695333341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21579544916785751130222227 32369317375178626695333341)
              ·
                refine ⟨12138494015691985010750003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 32369317375178626695333341 12138494015691985010750003)
                ·
                  refine ⟨18207741023537977516125005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12138494015691985010750003 18207741023537977516125005)
                  ·
                    refine ⟨6827902883826741568546877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 18207741023537977516125005 6827902883826741568546877)
                    ·
                      refine ⟨2560463581435028088205079, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6827902883826741568546877 2560463581435028088205079)
                      ·
                        rfl

theorem cell23_4986485_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 1, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 1, 1, 3, 1, 3, 3].length) (baseStart_4986485 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4986485 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4986485 prefixEnd_4986485 := by exact prefixLift 4986485
  have htrace : WordTrace (prefixWord ++ tailWord_4986485) baseStart_4986485 baseEnd_4986485 := by
    simpa [prefixWord, tailWord_4986485, baseEnd_4986485] using wordTrace_append hprefix tailTrace_4986485
  have hstable : (prefixWord ++ tailWord_4986485).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4986485).length < 2 ^ (prefixWord ++ tailWord_4986485).sum := by decide
  have hdescent : baseEnd_4986485 < baseStart_4986485 := by decide
  rcases family_descends (prefixWord ++ tailWord_4986485) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4986491 : List Nat := [1, 1, 1, 1, 1, 4, 3, 2, 2, 3, 4]
def baseStart_4986491 : Nat := 118140960795 + 4986491 * 2 ^ 59
def prefixEnd_4986491 : Nat := 4983230072969 + 3 ^ 40 * 4986491 * 2
def baseEnd_4986491 : Nat := 2560466662318955064730051

theorem tailTrace_4986491 : CollatzResearch.WordTrace tailWord_4986491 prefixEnd_4986491 2560466662318955064730051 := by
  unfold tailWord_4986491
  simp only [CollatzResearch.WordTrace]
  refine ⟨181872268177802206706591327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121248178785201471137727551 181872268177802206706591327)
  ·
    refine ⟨272808402266703310059886991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 181872268177802206706591327 272808402266703310059886991)
    ·
      refine ⟨409212603400054965089830487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 272808402266703310059886991 409212603400054965089830487)
      ·
        refine ⟨613818905100082447634745731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 409212603400054965089830487 613818905100082447634745731)
        ·
          refine ⟨920728357650123671452118597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 613818905100082447634745731 920728357650123671452118597)
          ·
            refine ⟨172636567059398188397272237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 920728357650123671452118597 172636567059398188397272237)
            ·
              refine ⟨64738712647274320648977089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 172636567059398188397272237 64738712647274320648977089)
              ·
                refine ⟨48554034485455740486732817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 64738712647274320648977089 48554034485455740486732817)
                ·
                  refine ⟨36415525864091805365049613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 48554034485455740486732817 36415525864091805365049613)
                  ·
                    refine ⟨13655822199034427011893605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 36415525864091805365049613 13655822199034427011893605)
                    ·
                      refine ⟨2560466662318955064730051, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13655822199034427011893605 2560466662318955064730051)
                      ·
                        rfl

theorem cell23_4986491_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 3, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 3, 2, 2, 3, 4].length) (baseStart_4986491 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4986491 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4986491 prefixEnd_4986491 := by exact prefixLift 4986491
  have htrace : WordTrace (prefixWord ++ tailWord_4986491) baseStart_4986491 baseEnd_4986491 := by
    simpa [prefixWord, tailWord_4986491, baseEnd_4986491] using wordTrace_append hprefix tailTrace_4986491
  have hstable : (prefixWord ++ tailWord_4986491).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4986491).length < 2 ^ (prefixWord ++ tailWord_4986491).sum := by decide
  have hdescent : baseEnd_4986491 < baseStart_4986491 := by decide
  rcases family_descends (prefixWord ++ tailWord_4986491) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4986501 : List Nat := [1, 3, 1, 1, 4, 1, 1, 2, 1, 8]
def baseStart_4986501 : Nat := 118140960795 + 4986501 * 2 ^ 59
def prefixEnd_4986501 : Nat := 4983230072969 + 3 ^ 40 * 4986501 * 2
def baseEnd_4986501 : Nat := 853490599041833341868335

theorem tailTrace_4986501 : CollatzResearch.WordTrace tailWord_4986501 prefixEnd_4986501 853490599041833341868335 := by
  unfold tailWord_4986501
  simp only [CollatzResearch.WordTrace]
  refine ⟨181872632907765978414455357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121248421938510652276303571 181872632907765978414455357)
  ·
    refine ⟨68202237340412241905420759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 181872632907765978414455357 68202237340412241905420759)
    ·
      refine ⟨102303356010618362858131139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68202237340412241905420759 102303356010618362858131139)
      ·
        refine ⟨153455034015927544287196709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 102303356010618362858131139 153455034015927544287196709)
        ·
          refine ⟨28772818877986414553849383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 153455034015927544287196709 28772818877986414553849383)
          ·
            refine ⟨43159228316979621830774075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28772818877986414553849383 43159228316979621830774075)
            ·
              refine ⟨64738842475469432746161113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 43159228316979621830774075 64738842475469432746161113)
              ·
                refine ⟨48554131856602074559620835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 64738842475469432746161113 48554131856602074559620835)
                ·
                  refine ⟨72831197784903111839431253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 48554131856602074559620835 72831197784903111839431253)
                  ·
                    refine ⟨853490599041833341868335, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 72831197784903111839431253 853490599041833341868335)
                    ·
                      rfl

theorem cell23_4986501_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 1, 2, 1, 8].length) (baseStart_4986501 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4986501 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4986501 prefixEnd_4986501 := by exact prefixLift 4986501
  have htrace : WordTrace (prefixWord ++ tailWord_4986501) baseStart_4986501 baseEnd_4986501 := by
    simpa [prefixWord, tailWord_4986501, baseEnd_4986501] using wordTrace_append hprefix tailTrace_4986501
  have hstable : (prefixWord ++ tailWord_4986501).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4986501).length < 2 ^ (prefixWord ++ tailWord_4986501).sum := by decide
  have hdescent : baseEnd_4986501 < baseStart_4986501 := by decide
  rcases family_descends (prefixWord ++ tailWord_4986501) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4986536 : List Nat := [2, 1, 7, 1, 1, 2, 1, 1, 1, 3, 3]
def baseStart_4986536 : Nat := 118140960795 + 4986536 * 2 ^ 59
def prefixEnd_4986536 : Nat := 4983230072969 + 3 ^ 40 * 4986536 * 2
def baseEnd_4986536 : Nat := 2560489768948407388667345

theorem tailTrace_4986536 : CollatzResearch.WordTrace tailWord_4986536 prefixEnd_4986536 2560489768948407388667345 := by
  unfold tailWord_4986536
  simp only [CollatzResearch.WordTrace]
  refine ⟨90936954731319589695989731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 121249272975092786261319641 90936954731319589695989731)
  ·
    refine ⟨136405432096979384543984597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90936954731319589695989731 136405432096979384543984597)
    ·
      refine ⟨3197002314772954325249639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 136405432096979384543984597 3197002314772954325249639)
      ·
        refine ⟨4795503472159431487874459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3197002314772954325249639 4795503472159431487874459)
        ·
          refine ⟨7193255208239147231811689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4795503472159431487874459 7193255208239147231811689)
          ·
            refine ⟨5394941406179360423858767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7193255208239147231811689 5394941406179360423858767)
            ·
              refine ⟨8092412109269040635788151, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5394941406179360423858767 8092412109269040635788151)
              ·
                refine ⟨12138618163903560953682227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8092412109269040635788151 12138618163903560953682227)
                ·
                  refine ⟨18207927245855341430523341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12138618163903560953682227 18207927245855341430523341)
                  ·
                    refine ⟨6827972717195753036446253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 18207927245855341430523341 6827972717195753036446253)
                    ·
                      refine ⟨2560489768948407388667345, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6827972717195753036446253 2560489768948407388667345)
                      ·
                        rfl

theorem cell23_4986536_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 7, 1, 1, 2, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 7, 1, 1, 2, 1, 1, 1, 3, 3].length) (baseStart_4986536 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4986536 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4986536 prefixEnd_4986536 := by exact prefixLift 4986536
  have htrace : WordTrace (prefixWord ++ tailWord_4986536) baseStart_4986536 baseEnd_4986536 := by
    simpa [prefixWord, tailWord_4986536, baseEnd_4986536] using wordTrace_append hprefix tailTrace_4986536
  have hstable : (prefixWord ++ tailWord_4986536).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4986536).length < 2 ^ (prefixWord ++ tailWord_4986536).sum := by decide
  have hdescent : baseEnd_4986536 < baseStart_4986536 := by decide
  rcases family_descends (prefixWord ++ tailWord_4986536) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4986571 : List Nat := [1, 1, 1, 1, 3, 2, 1, 2, 3, 1, 7]
def baseStart_4986571 : Nat := 118140960795 + 4986571 * 2 ^ 59
def prefixEnd_4986571 : Nat := 4983230072969 + 3 ^ 40 * 4986571 * 2
def baseEnd_4986571 : Nat := 2560507740771314751729683

theorem tailTrace_4986571 : CollatzResearch.WordTrace tailWord_4986571 prefixEnd_4986571 2560507740771314751729683 := by
  unfold tailWord_4986571
  simp only [CollatzResearch.WordTrace]
  refine ⟨181875186017512380369503567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121250124011674920246335711 181875186017512380369503567)
  ·
    refine ⟨272812779026268570554255351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 181875186017512380369503567 272812779026268570554255351)
    ·
      refine ⟨409219168539402855831383027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 272812779026268570554255351 409219168539402855831383027)
      ·
        refine ⟨613828752809104283747074541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 409219168539402855831383027 613828752809104283747074541)
        ·
          refine ⟨230185782303414106405152953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 613828752809104283747074541 230185782303414106405152953)
          ·
            refine ⟨172639336727560579803864715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 230185782303414106405152953 172639336727560579803864715)
            ·
              refine ⟨258959005091340869705797073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 172639336727560579803864715 258959005091340869705797073)
              ·
                refine ⟨194219253818505652279347805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 258959005091340869705797073 194219253818505652279347805)
                ·
                  refine ⟨72832220181939619604755427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 194219253818505652279347805 72832220181939619604755427)
                  ·
                    refine ⟨109248330272909429407133141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 72832220181939619604755427 109248330272909429407133141)
                    ·
                      refine ⟨2560507740771314751729683, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 109248330272909429407133141 2560507740771314751729683)
                      ·
                        rfl

theorem cell23_4986571_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 1, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 1, 2, 3, 1, 7].length) (baseStart_4986571 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4986571 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4986571 prefixEnd_4986571 := by exact prefixLift 4986571
  have htrace : WordTrace (prefixWord ++ tailWord_4986571) baseStart_4986571 baseEnd_4986571 := by
    simpa [prefixWord, tailWord_4986571, baseEnd_4986571] using wordTrace_append hprefix tailTrace_4986571
  have hstable : (prefixWord ++ tailWord_4986571).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4986571).length < 2 ^ (prefixWord ++ tailWord_4986571).sum := by decide
  have hdescent : baseEnd_4986571 < baseStart_4986571 := by decide
  rcases family_descends (prefixWord ++ tailWord_4986571) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4986593 : List Nat := [1, 2, 3, 1, 6, 1, 2, 1, 2, 2, 2]
def baseStart_4986593 : Nat := 118140960795 + 4986593 * 2 ^ 59
def prefixEnd_4986593 : Nat := 4983230072969 + 3 ^ 40 * 4986593 * 2
def baseEnd_4986593 : Nat := 2560519037345713665654583

theorem tailTrace_4986593 : CollatzResearch.WordTrace tailWord_4986593 prefixEnd_4986593 2560519037345713665654583 := by
  unfold tailWord_4986593
  simp only [CollatzResearch.WordTrace]
  refine ⟨181875988423432678126804433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121250658948955118751202955 181875988423432678126804433)
  ·
    refine ⟨136406991317574508595103325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 181875988423432678126804433 136406991317574508595103325)
    ·
      refine ⟨51152621744090440723163747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 136406991317574508595103325 51152621744090440723163747)
      ·
        refine ⟨76728932616135661084745621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51152621744090440723163747 76728932616135661084745621)
        ·
          refine ⟨3596668716381359113347451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 76728932616135661084745621 3596668716381359113347451)
          ·
            refine ⟨5395003074572038670021177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3596668716381359113347451 5395003074572038670021177)
            ·
              refine ⟨4046252305929029002515883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5395003074572038670021177 4046252305929029002515883)
              ·
                refine ⟨6069378458893543503773825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4046252305929029002515883 6069378458893543503773825)
                ·
                  refine ⟨4552033844170157627830369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6069378458893543503773825 4552033844170157627830369)
                  ·
                    refine ⟨3414025383127618220872777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4552033844170157627830369 3414025383127618220872777)
                    ·
                      refine ⟨2560519037345713665654583, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3414025383127618220872777 2560519037345713665654583)
                      ·
                        rfl

theorem cell23_4986593_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 6, 1, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 6, 1, 2, 1, 2, 2, 2].length) (baseStart_4986593 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4986593 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4986593 prefixEnd_4986593 := by exact prefixLift 4986593
  have htrace : WordTrace (prefixWord ++ tailWord_4986593) baseStart_4986593 baseEnd_4986593 := by
    simpa [prefixWord, tailWord_4986593, baseEnd_4986593] using wordTrace_append hprefix tailTrace_4986593
  have hstable : (prefixWord ++ tailWord_4986593).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4986593).length < 2 ^ (prefixWord ++ tailWord_4986593).sum := by decide
  have hdescent : baseEnd_4986593 < baseStart_4986593 := by decide
  rcases family_descends (prefixWord ++ tailWord_4986593) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4986635 : List Nat := [1, 1, 1, 1, 5, 1, 4, 2, 2, 2, 3]
def baseStart_4986635 : Nat := 118140960795 + 4986635 * 2 ^ 59
def prefixEnd_4986635 : Nat := 4983230072969 + 3 ^ 40 * 4986635 * 2
def baseEnd_4986635 : Nat := 2560540603533202501329389

theorem tailTrace_4986635 : CollatzResearch.WordTrace tailWord_4986635 prefixEnd_4986635 2560540603533202501329389 := by
  unfold tailWord_4986635
  simp only [CollatzResearch.WordTrace]
  refine ⟨181877520289280519299833359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121251680192853679533222239 181877520289280519299833359)
  ·
    refine ⟨272816280433920778949750039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 181877520289280519299833359 272816280433920778949750039)
    ·
      refine ⟨409224420650881168424625059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 272816280433920778949750039 409224420650881168424625059)
      ·
        refine ⟨613836630976321752636937589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 409224420650881168424625059 613836630976321752636937589)
        ·
          refine ⟨57547184154030164309712899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 613836630976321752636937589 57547184154030164309712899)
          ·
            refine ⟨86320776231045246464569349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 57547184154030164309712899 86320776231045246464569349)
            ·
              refine ⟨16185145543320983712106753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 86320776231045246464569349 16185145543320983712106753)
              ·
                refine ⟨12138859157490737784080065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16185145543320983712106753 12138859157490737784080065)
                ·
                  refine ⟨9104144368118053338060049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12138859157490737784080065 9104144368118053338060049)
                  ·
                    refine ⟨6828108276088540003545037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9104144368118053338060049 6828108276088540003545037)
                    ·
                      refine ⟨2560540603533202501329389, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6828108276088540003545037 2560540603533202501329389)
                      ·
                        rfl

theorem cell23_4986635_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 4, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 4, 2, 2, 2, 3].length) (baseStart_4986635 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4986635 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4986635 prefixEnd_4986635 := by exact prefixLift 4986635
  have htrace : WordTrace (prefixWord ++ tailWord_4986635) baseStart_4986635 baseEnd_4986635 := by
    simpa [prefixWord, tailWord_4986635, baseEnd_4986635] using wordTrace_append hprefix tailTrace_4986635
  have hstable : (prefixWord ++ tailWord_4986635).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4986635).length < 2 ^ (prefixWord ++ tailWord_4986635).sum := by decide
  have hdescent : baseEnd_4986635 < baseStart_4986635 := by decide
  rcases family_descends (prefixWord ++ tailWord_4986635) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4986638 : List Nat := [4, 1, 1, 2, 1, 1, 2, 3, 8]
def baseStart_4986638 : Nat := 118140960795 + 4986638 * 2 ^ 59
def prefixEnd_4986638 : Nat := 4983230072969 + 3 ^ 40 * 4986638 * 2
def baseEnd_4986638 : Nat := 284504682663907332176875

theorem tailTrace_4986638 : CollatzResearch.WordTrace tailWord_4986638 prefixEnd_4986638 284504682663907332176875 := by
  unfold tailWord_4986638
  simp only [CollatzResearch.WordTrace]
  refine ⟨22734703713533706351524071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 121251753138846433874795045 22734703713533706351524071)
  ·
    refine ⟨34102055570300559527286107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22734703713533706351524071 34102055570300559527286107)
    ·
      refine ⟨51153083355450839290929161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34102055570300559527286107 51153083355450839290929161)
      ·
        refine ⟨38364812516588129468196871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 51153083355450839290929161 38364812516588129468196871)
        ·
          refine ⟨57547218774882194202295307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38364812516588129468196871 57547218774882194202295307)
          ·
            refine ⟨86320828162323291303442961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 57547218774882194202295307 86320828162323291303442961)
            ·
              refine ⟨64740621121742468477582221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 86320828162323291303442961 64740621121742468477582221)
              ·
                refine ⟨24277732920653425679093333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 64740621121742468477582221 24277732920653425679093333)
                ·
                  refine ⟨284504682663907332176875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 24277732920653425679093333 284504682663907332176875)
                  ·
                    rfl

theorem cell23_4986638_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 2, 3, 8].length) (baseStart_4986638 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4986638 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4986638 prefixEnd_4986638 := by exact prefixLift 4986638
  have htrace : WordTrace (prefixWord ++ tailWord_4986638) baseStart_4986638 baseEnd_4986638 := by
    simpa [prefixWord, tailWord_4986638, baseEnd_4986638] using wordTrace_append hprefix tailTrace_4986638
  have hstable : (prefixWord ++ tailWord_4986638).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4986638).length < 2 ^ (prefixWord ++ tailWord_4986638).sum := by decide
  have hdescent : baseEnd_4986638 < baseStart_4986638 := by decide
  rcases family_descends (prefixWord ++ tailWord_4986638) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4986676 : List Nat := [2, 5, 1, 1, 2, 2, 2, 3, 1, 4]
def baseStart_4986676 : Nat := 118140960795 + 4986676 * 2 ^ 59
def prefixEnd_4986676 : Nat := 4983230072969 + 3 ^ 40 * 4986676 * 2
def baseEnd_4986676 : Nat := 853520552080012280305567

theorem tailTrace_4986676 : CollatzResearch.WordTrace tailWord_4986676 prefixEnd_4986676 853520552080012280305567 := by
  unfold tailWord_4986676
  simp only [CollatzResearch.WordTrace]
  refine ⟨90939507841065991651037941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 121252677121421322201383921 90939507841065991651037941)
  ·
    refine ⟨8525578860099936717284807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 90939507841065991651037941 8525578860099936717284807)
    ·
      refine ⟨12788368290149905075927211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8525578860099936717284807 12788368290149905075927211)
      ·
        refine ⟨19182552435224857613890817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12788368290149905075927211 19182552435224857613890817)
        ·
          refine ⟨14386914326418643210418113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19182552435224857613890817 14386914326418643210418113)
          ·
            refine ⟨10790185744813982407813585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14386914326418643210418113 10790185744813982407813585)
            ·
              refine ⟨8092639308610486805860189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10790185744813982407813585 8092639308610486805860189)
              ·
                refine ⟨3034739740728932552197571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8092639308610486805860189 3034739740728932552197571)
                ·
                  refine ⟨4552109611093398828296357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3034739740728932552197571 4552109611093398828296357)
                  ·
                    refine ⟨853520552080012280305567, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4552109611093398828296357 853520552080012280305567)
                    ·
                      rfl

theorem cell23_4986676_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 2, 2, 3, 1, 4].length) (baseStart_4986676 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4986676 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4986676 prefixEnd_4986676 := by exact prefixLift 4986676
  have htrace : WordTrace (prefixWord ++ tailWord_4986676) baseStart_4986676 baseEnd_4986676 := by
    simpa [prefixWord, tailWord_4986676, baseEnd_4986676] using wordTrace_append hprefix tailTrace_4986676
  have hstable : (prefixWord ++ tailWord_4986676).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4986676).length < 2 ^ (prefixWord ++ tailWord_4986676).sum := by decide
  have hdescent : baseEnd_4986676 < baseStart_4986676 := by decide
  rcases family_descends (prefixWord ++ tailWord_4986676) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4986750 : List Nat := [4, 2, 3, 1, 1, 2, 3, 2, 1, 1, 3]
def baseStart_4986750 : Nat := 118140960795 + 4986750 * 2 ^ 59
def prefixEnd_4986750 : Nat := 4983230072969 + 3 ^ 40 * 4986750 * 2
def baseEnd_4986750 : Nat := 2560599653808469551391361

theorem tailTrace_4986750 : CollatzResearch.WordTrace tailWord_4986750 prefixEnd_4986750 2560599653808469551391361 := by
  unfold tailWord_4986750
  simp only [CollatzResearch.WordTrace]
  refine ⟨22735214335482986742533713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 121254476455909262626846469 22735214335482986742533713)
  ·
    refine ⟨17051410751612240056900285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22735214335482986742533713 17051410751612240056900285)
    ·
      refine ⟨6394279031854590021337607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17051410751612240056900285 6394279031854590021337607)
      ·
        refine ⟨9591418547781885032006411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6394279031854590021337607 9591418547781885032006411)
        ·
          refine ⟨14387127821672827548009617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9591418547781885032006411 14387127821672827548009617)
          ·
            refine ⟨10790345866254620661007213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14387127821672827548009617 10790345866254620661007213)
            ·
              refine ⟨4046379699845482747877705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10790345866254620661007213 4046379699845482747877705)
              ·
                refine ⟨3034784774884112060908279, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4046379699845482747877705 3034784774884112060908279)
                ·
                  refine ⟨4552177162326168091362419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3034784774884112060908279 4552177162326168091362419)
                  ·
                    refine ⟨6828265743489252137043629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4552177162326168091362419 6828265743489252137043629)
                    ·
                      refine ⟨2560599653808469551391361, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6828265743489252137043629 2560599653808469551391361)
                      ·
                        rfl

theorem cell23_4986750_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 2, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 2, 3, 2, 1, 1, 3].length) (baseStart_4986750 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4986750 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4986750 prefixEnd_4986750 := by exact prefixLift 4986750
  have htrace : WordTrace (prefixWord ++ tailWord_4986750) baseStart_4986750 baseEnd_4986750 := by
    simpa [prefixWord, tailWord_4986750, baseEnd_4986750] using wordTrace_append hprefix tailTrace_4986750
  have hstable : (prefixWord ++ tailWord_4986750).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4986750).length < 2 ^ (prefixWord ++ tailWord_4986750).sum := by decide
  have hdescent : baseEnd_4986750 < baseStart_4986750 := by decide
  rcases family_descends (prefixWord ++ tailWord_4986750) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4986756 : List Nat := [2, 3, 2, 1, 1, 1, 2, 6, 1, 2, 2]
def baseStart_4986756 : Nat := 118140960795 + 4986756 * 2 ^ 59
def prefixEnd_4986756 : Nat := 4983230072969 + 3 ^ 40 * 4986756 * 2
def baseEnd_4986756 : Nat := 2560602734692396527916333

theorem tailTrace_4986756 : CollatzResearch.WordTrace tailWord_4986756 prefixEnd_4986756 2560602734692396527916333 := by
  unfold tailWord_4986756
  simp only [CollatzResearch.WordTrace]
  refine ⟨90940966760921078482494061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 121254622347894771309992081 90940966760921078482494061)
  ·
    refine ⟨34102862535345404430935273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 90940966760921078482494061 34102862535345404430935273)
    ·
      refine ⟨25577146901509053323201455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34102862535345404430935273 25577146901509053323201455)
      ·
        refine ⟨38365720352263579984802183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25577146901509053323201455 38365720352263579984802183)
        ·
          refine ⟨57548580528395369977203275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38365720352263579984802183 57548580528395369977203275)
          ·
            refine ⟨86322870792593054965804913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 57548580528395369977203275 86322870792593054965804913)
            ·
              refine ⟨64742153094444791224353685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 86322870792593054965804913 64742153094444791224353685)
              ·
                refine ⟨3034788426302099588641579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 64742153094444791224353685 3034788426302099588641579)
                ·
                  refine ⟨4552182639453149382962369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3034788426302099588641579 4552182639453149382962369)
                  ·
                    refine ⟨3414136979589862037221777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4552182639453149382962369 3414136979589862037221777)
                    ·
                      refine ⟨2560602734692396527916333, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3414136979589862037221777 2560602734692396527916333)
                      ·
                        rfl

theorem cell23_4986756_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 2, 6, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 2, 6, 1, 2, 2].length) (baseStart_4986756 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4986756 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4986756 prefixEnd_4986756 := by exact prefixLift 4986756
  have htrace : WordTrace (prefixWord ++ tailWord_4986756) baseStart_4986756 baseEnd_4986756 := by
    simpa [prefixWord, tailWord_4986756, baseEnd_4986756] using wordTrace_append hprefix tailTrace_4986756
  have hstable : (prefixWord ++ tailWord_4986756).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4986756).length < 2 ^ (prefixWord ++ tailWord_4986756).sum := by decide
  have hdescent : baseEnd_4986756 < baseStart_4986756 := by decide
  rcases family_descends (prefixWord ++ tailWord_4986756) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4986762 : List Nat := [3, 1, 2, 4, 2, 1, 2, 8]
def baseStart_4986762 : Nat := 118140960795 + 4986762 * 2 ^ 59
def prefixEnd_4986762 : Nat := 4983230072969 + 3 ^ 40 * 4986762 * 2
def baseEnd_4986762 : Nat := 94837252428752722386715

theorem tailTrace_4986762 : CollatzResearch.WordTrace tailWord_4986762 prefixEnd_4986762 94837252428752722386715 := by
  unfold tailWord_4986762
  simp only [CollatzResearch.WordTrace]
  refine ⟨45470538089955104997426635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 121254768239880279993137693 45470538089955104997426635)
  ·
    refine ⟨68205807134932657496139953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45470538089955104997426635 68205807134932657496139953)
    ·
      refine ⟨51154355351199493122104965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 68205807134932657496139953 51154355351199493122104965)
      ·
        refine ⟨9591441628349904960394681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 51154355351199493122104965 9591441628349904960394681)
        ·
          refine ⟨7193581221262428720296011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9591441628349904960394681 7193581221262428720296011)
          ·
            refine ⟨10790371831893643080444017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7193581221262428720296011 10790371831893643080444017)
            ·
              refine ⟨8092778873920232310333013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10790371831893643080444017 8092778873920232310333013)
              ·
                refine ⟨94837252428752722386715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 8092778873920232310333013 94837252428752722386715)
                ·
                  rfl

theorem cell23_4986762_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 2, 1, 2, 8].length) (baseStart_4986762 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4986762 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4986762 prefixEnd_4986762 := by exact prefixLift 4986762
  have htrace : WordTrace (prefixWord ++ tailWord_4986762) baseStart_4986762 baseEnd_4986762 := by
    simpa [prefixWord, tailWord_4986762, baseEnd_4986762] using wordTrace_append hprefix tailTrace_4986762
  have hstable : (prefixWord ++ tailWord_4986762).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4986762).length < 2 ^ (prefixWord ++ tailWord_4986762).sum := by decide
  have hdescent : baseEnd_4986762 < baseStart_4986762 := by decide
  rcases family_descends (prefixWord ++ tailWord_4986762) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4986766 : List Nat := [4, 1, 1, 5, 1, 1, 1, 3, 2, 4]
def baseStart_4986766 : Nat := 118140960795 + 4986766 * 2 ^ 59
def prefixEnd_4986766 : Nat := 4983230072969 + 3 ^ 40 * 4986766 * 2
def baseEnd_4986766 : Nat := 853535956499647162930429

theorem tailTrace_4986766 : CollatzResearch.WordTrace tailWord_4986766 prefixEnd_4986766 853535956499647162930429 := by
  unfold tailWord_4986766
  simp only [CollatzResearch.WordTrace]
  refine ⟨22735287281475741084106519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 121254865501203952448568101 22735287281475741084106519)
  ·
    refine ⟨34102930922213611626159779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22735287281475741084106519 34102930922213611626159779)
    ·
      refine ⟨51154396383320417439239669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34102930922213611626159779 51154396383320417439239669)
      ·
        refine ⟨4795724660936289134928719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 51154396383320417439239669 4795724660936289134928719)
        ·
          refine ⟨7193586991404433702393079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4795724660936289134928719 7193586991404433702393079)
          ·
            refine ⟨10790380487106650553589619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7193586991404433702393079 10790380487106650553589619)
            ·
              refine ⟨16185570730659975830384429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10790380487106650553589619 16185570730659975830384429)
              ·
                refine ⟨6069589023997490936394161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16185570730659975830384429 6069589023997490936394161)
                ·
                  refine ⟨4552191767998118202295621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6069589023997490936394161 4552191767998118202295621)
                  ·
                    refine ⟨853535956499647162930429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4552191767998118202295621 853535956499647162930429)
                    ·
                      rfl

theorem cell23_4986766_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 5, 1, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 5, 1, 1, 1, 3, 2, 4].length) (baseStart_4986766 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4986766 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4986766 prefixEnd_4986766 := by exact prefixLift 4986766
  have htrace : WordTrace (prefixWord ++ tailWord_4986766) baseStart_4986766 baseEnd_4986766 := by
    simpa [prefixWord, tailWord_4986766, baseEnd_4986766] using wordTrace_append hprefix tailTrace_4986766
  have hstable : (prefixWord ++ tailWord_4986766).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4986766).length < 2 ^ (prefixWord ++ tailWord_4986766).sum := by decide
  have hdescent : baseEnd_4986766 < baseStart_4986766 := by decide
  rcases family_descends (prefixWord ++ tailWord_4986766) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4986815 : List Nat := [1, 1, 2, 2, 2, 1, 3, 1, 1, 6, 3]
def baseStart_4986815 : Nat := 118140960795 + 4986815 * 2 ^ 59
def prefixEnd_4986815 : Nat := 4983230072969 + 3 ^ 40 * 4986815 * 2
def baseEnd_4986815 : Nat := 2560633030051011797078561

theorem tailTrace_4986815 : CollatzResearch.WordTrace tailWord_4986815 prefixEnd_4986815 2560633030051011797078561 := by
  unfold tailWord_4986815
  simp only [CollatzResearch.WordTrace]
  refine ⟨181884085428628410041385899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121256056952418940027590599 181884085428628410041385899)
  ·
    refine ⟨272826128142942615062078849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 181884085428628410041385899 272826128142942615062078849)
    ·
      refine ⟨204619596107206961296559137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 272826128142942615062078849 204619596107206961296559137)
      ·
        refine ⟨153464697080405220972419353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 204619596107206961296559137 153464697080405220972419353)
        ·
          refine ⟨115098522810303915729314515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 153464697080405220972419353 115098522810303915729314515)
          ·
            refine ⟨172647784215455873593971773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 115098522810303915729314515 172647784215455873593971773)
            ·
              refine ⟨64742919080795952597739415, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 172647784215455873593971773 64742919080795952597739415)
              ·
                refine ⟨97114378621193928896609123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 64742919080795952597739415 97114378621193928896609123)
                ·
                  refine ⟨145671567931790893344913685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 97114378621193928896609123 145671567931790893344913685)
                  ·
                    refine ⟨6828354746802698125542829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 145671567931790893344913685 6828354746802698125542829)
                    ·
                      refine ⟨2560633030051011797078561, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6828354746802698125542829 2560633030051011797078561)
                      ·
                        rfl

theorem cell23_4986815_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 3, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 3, 1, 1, 6, 3].length) (baseStart_4986815 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4986815 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4986815 prefixEnd_4986815 := by exact prefixLift 4986815
  have htrace : WordTrace (prefixWord ++ tailWord_4986815) baseStart_4986815 baseEnd_4986815 := by
    simpa [prefixWord, tailWord_4986815, baseEnd_4986815] using wordTrace_append hprefix tailTrace_4986815
  have hstable : (prefixWord ++ tailWord_4986815).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4986815).length < 2 ^ (prefixWord ++ tailWord_4986815).sum := by decide
  have hdescent : baseEnd_4986815 < baseStart_4986815 := by decide
  rcases family_descends (prefixWord ++ tailWord_4986815) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4986825 : List Nat := [1, 2, 1, 1, 2, 1, 2, 5, 2, 2, 4]
def baseStart_4986825 : Nat := 118140960795 + 4986825 * 2 ^ 59
def prefixEnd_4986825 : Nat := 4983230072969 + 3 ^ 40 * 4986825 * 2
def baseEnd_4986825 : Nat := 2560638164857556757953515

theorem tailTrace_4986825 : CollatzResearch.WordTrace tailWord_4986825 prefixEnd_4986825 2560638164857556757953515 := by
  unfold tailWord_4986825
  simp only [CollatzResearch.WordTrace]
  refine ⟨181884450158592181749249929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121256300105728121166166619 181884450158592181749249929)
  ·
    refine ⟨136413337618944136311937447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 181884450158592181749249929 136413337618944136311937447)
    ·
      refine ⟨204620006428416204467906171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 136413337618944136311937447 204620006428416204467906171)
      ·
        refine ⟨306930009642624306701859257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 204620006428416204467906171 306930009642624306701859257)
        ·
          refine ⟨230197507231968230026394443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 306930009642624306701859257 230197507231968230026394443)
          ·
            refine ⟨345296260847952345039591665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 230197507231968230026394443 345296260847952345039591665)
            ·
              refine ⟨258972195635964258779693749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 345296260847952345039591665 258972195635964258779693749)
              ·
                refine ⟨24278643340871649260596289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 258972195635964258779693749 24278643340871649260596289)
                ·
                  refine ⟨18208982505653736945447217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 24278643340871649260596289 18208982505653736945447217)
                  ·
                    refine ⟨13656736879240302709085413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 18208982505653736945447217 13656736879240302709085413)
                    ·
                      refine ⟨2560638164857556757953515, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13656736879240302709085413 2560638164857556757953515)
                      ·
                        rfl

theorem cell23_4986825_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 2, 5, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 2, 5, 2, 2, 4].length) (baseStart_4986825 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4986825 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4986825 prefixEnd_4986825 := by exact prefixLift 4986825
  have htrace : WordTrace (prefixWord ++ tailWord_4986825) baseStart_4986825 baseEnd_4986825 := by
    simpa [prefixWord, tailWord_4986825, baseEnd_4986825] using wordTrace_append hprefix tailTrace_4986825
  have hstable : (prefixWord ++ tailWord_4986825).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4986825).length < 2 ^ (prefixWord ++ tailWord_4986825).sum := by decide
  have hdescent : baseEnd_4986825 < baseStart_4986825 := by decide
  rcases family_descends (prefixWord ++ tailWord_4986825) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4986872 : List Nat := [2, 1, 2, 1, 1, 3, 2, 1, 1, 7, 2]
def baseStart_4986872 : Nat := 118140960795 + 4986872 * 2 ^ 59
def prefixEnd_4986872 : Nat := 4983230072969 + 3 ^ 40 * 4986872 * 2
def baseEnd_4986872 : Nat := 2560662298448318074065799

theorem tailTrace_4986872 : CollatzResearch.WordTrace tailWord_4986872 prefixEnd_4986872 2560662298448318074065799 := by
  unfold tailWord_4986872
  simp only [CollatzResearch.WordTrace]
  refine ⟨90943082194710954388105435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 121257442926281272517473913 90943082194710954388105435)
  ·
    refine ⟨136414623292066431582158153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90943082194710954388105435 136414623292066431582158153)
    ·
      refine ⟨102310967469049823686618615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 136414623292066431582158153 102310967469049823686618615)
      ·
        refine ⟨153466451203574735529927923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 102310967469049823686618615 153466451203574735529927923)
        ·
          refine ⟨230199676805362103294891885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 153466451203574735529927923 230199676805362103294891885)
          ·
            refine ⟨86324878802010788735584457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 230199676805362103294891885 86324878802010788735584457)
            ·
              refine ⟨64743659101508091551688343, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 86324878802010788735584457 64743659101508091551688343)
              ·
                refine ⟨97115488652262137327532515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 64743659101508091551688343 97115488652262137327532515)
                ·
                  refine ⟨145673232978393205991298773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 97115488652262137327532515 145673232978393205991298773)
                  ·
                    refine ⟨3414216397931090765421065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 145673232978393205991298773 3414216397931090765421065)
                    ·
                      refine ⟨2560662298448318074065799, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3414216397931090765421065 2560662298448318074065799)
                      ·
                        rfl

theorem cell23_4986872_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 2, 1, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 2, 1, 1, 7, 2].length) (baseStart_4986872 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4986872 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4986872 prefixEnd_4986872 := by exact prefixLift 4986872
  have htrace : WordTrace (prefixWord ++ tailWord_4986872) baseStart_4986872 baseEnd_4986872 := by
    simpa [prefixWord, tailWord_4986872, baseEnd_4986872] using wordTrace_append hprefix tailTrace_4986872
  have hstable : (prefixWord ++ tailWord_4986872).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4986872).length < 2 ^ (prefixWord ++ tailWord_4986872).sum := by decide
  have hdescent : baseEnd_4986872 < baseStart_4986872 := by decide
  rcases family_descends (prefixWord ++ tailWord_4986872) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4986875 : List Nat := [1, 1, 1, 1, 1, 3, 4, 3, 1, 2, 5]
def baseStart_4986875 : Nat := 118140960795 + 4986875 * 2 ^ 59
def prefixEnd_4986875 : Nat := 4983230072969 + 3 ^ 40 * 4986875 * 2
def baseEnd_4986875 : Nat := 2560663838890281562328285

theorem tailTrace_4986875 : CollatzResearch.WordTrace tailWord_4986875 prefixEnd_4986875 2560663838890281562328285 := by
  unfold tailWord_4986875
  simp only [CollatzResearch.WordTrace]
  refine ⟨181886273808411040288570079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121257515872274026859046719 181886273808411040288570079)
  ·
    refine ⟨272829410712616560432855119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 181886273808411040288570079 272829410712616560432855119)
    ·
      refine ⟨409244116068924840649282679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 272829410712616560432855119 409244116068924840649282679)
      ·
        refine ⟨613866174103387260973924019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 409244116068924840649282679 613866174103387260973924019)
        ·
          refine ⟨920799261155080891460886029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 613866174103387260973924019 920799261155080891460886029)
          ·
            refine ⟨345299722933155334297832261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 920799261155080891460886029 345299722933155334297832261)
            ·
              refine ⟨64743698049966625180843549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 345299722933155334297832261 64743698049966625180843549)
              ·
                refine ⟨24278886768737484442816331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 64743698049966625180843549 24278886768737484442816331)
                ·
                  refine ⟨36418330153106226664224497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24278886768737484442816331 36418330153106226664224497)
                  ·
                    refine ⟨27313747614829669998168373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 36418330153106226664224497 27313747614829669998168373)
                    ·
                      refine ⟨2560663838890281562328285, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 27313747614829669998168373 2560663838890281562328285)
                      ·
                        rfl

theorem cell23_4986875_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 4, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 4, 3, 1, 2, 5].length) (baseStart_4986875 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4986875 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4986875 prefixEnd_4986875 := by exact prefixLift 4986875
  have htrace : WordTrace (prefixWord ++ tailWord_4986875) baseStart_4986875 baseEnd_4986875 := by
    simpa [prefixWord, tailWord_4986875, baseEnd_4986875] using wordTrace_append hprefix tailTrace_4986875
  have hstable : (prefixWord ++ tailWord_4986875).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4986875).length < 2 ^ (prefixWord ++ tailWord_4986875).sum := by decide
  have hdescent : baseEnd_4986875 < baseStart_4986875 := by decide
  rcases family_descends (prefixWord ++ tailWord_4986875) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4986903 : List Nat := [1, 1, 3, 5, 3, 1, 1, 3, 5]
def baseStart_4986903 : Nat := 118140960795 + 4986903 * 2 ^ 59
def prefixEnd_4986903 : Nat := 4983230072969 + 3 ^ 40 * 4986903 * 2
def baseEnd_4986903 : Nat := 284519801816511939197573

theorem tailTrace_4986903 : CollatzResearch.WordTrace tailWord_4986903 prefixEnd_4986903 284519801816511939197573 := by
  unfold tailWord_4986903
  simp only [CollatzResearch.WordTrace]
  refine ⟨181887295052309601070589363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121258196701539734047059575 181887295052309601070589363)
  ·
    refine ⟨272830942578464401605884045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 181887295052309601070589363 272830942578464401605884045)
    ·
      refine ⟨102311603466924150602206517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 272830942578464401605884045 102311603466924150602206517)
      ·
        refine ⟨9591712825024139118956861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 102311603466924150602206517 9591712825024139118956861)
        ·
          refine ⟨3596892309384052169608823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9591712825024139118956861 3596892309384052169608823)
          ·
            refine ⟨5395338464076078254413235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3596892309384052169608823 5395338464076078254413235)
            ·
              refine ⟨8093007696114117381619853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5395338464076078254413235 8093007696114117381619853)
              ·
                refine ⟨3034877886042794018107445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8093007696114117381619853 3034877886042794018107445)
                ·
                  refine ⟨284519801816511939197573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3034877886042794018107445 284519801816511939197573)
                  ·
                    rfl

theorem cell23_4986903_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 3, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 3, 1, 1, 3, 5].length) (baseStart_4986903 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4986903 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4986903 prefixEnd_4986903 := by exact prefixLift 4986903
  have htrace : WordTrace (prefixWord ++ tailWord_4986903) baseStart_4986903 baseEnd_4986903 := by
    simpa [prefixWord, tailWord_4986903, baseEnd_4986903] using wordTrace_append hprefix tailTrace_4986903
  have hstable : (prefixWord ++ tailWord_4986903).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4986903).length < 2 ^ (prefixWord ++ tailWord_4986903).sum := by decide
  have hdescent : baseEnd_4986903 < baseStart_4986903 := by decide
  rcases family_descends (prefixWord ++ tailWord_4986903) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4986905 : List Nat := [1, 2, 1, 2, 1, 1, 3, 2, 2, 3, 5]
def baseStart_4986905 : Nat := 118140960795 + 4986905 * 2 ^ 59
def prefixEnd_4986905 : Nat := 4983230072969 + 3 ^ 40 * 4986905 * 2
def baseEnd_4986905 : Nat := 2560679243309916444953147

theorem tailTrace_4986905 : CollatzResearch.WordTrace tailWord_4986905 prefixEnd_4986905 2560679243309916444953147 := by
  unfold tailWord_4986905
  simp only [CollatzResearch.WordTrace]
  refine ⟨181887367998302355412162169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121258245332201570274774779 181887367998302355412162169)
  ·
    refine ⟨136415525998726766559121627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 181887367998302355412162169 136415525998726766559121627)
    ·
      refine ⟨204623288998090149838682441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 136415525998726766559121627 204623288998090149838682441)
      ·
        refine ⟨153467466748567612379011831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 204623288998090149838682441 153467466748567612379011831)
        ·
          refine ⟨230201200122851418568517747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 153467466748567612379011831 230201200122851418568517747)
          ·
            refine ⟨345301800184277127852776621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 230201200122851418568517747 345301800184277127852776621)
            ·
              refine ⟨129488175069103922944791233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 345301800184277127852776621 129488175069103922944791233)
              ·
                refine ⟨97116131301827942208593425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 129488175069103922944791233 97116131301827942208593425)
                ·
                  refine ⟨72837098476370956656445069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 97116131301827942208593425 72837098476370956656445069)
                  ·
                    refine ⟨27313911928639108746166901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 72837098476370956656445069 27313911928639108746166901)
                    ·
                      refine ⟨2560679243309916444953147, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 27313911928639108746166901 2560679243309916444953147)
                      ·
                        rfl

theorem cell23_4986905_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 3, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 3, 2, 2, 3, 5].length) (baseStart_4986905 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4986905 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4986905 prefixEnd_4986905 := by exact prefixLift 4986905
  have htrace : WordTrace (prefixWord ++ tailWord_4986905) baseStart_4986905 baseEnd_4986905 := by
    simpa [prefixWord, tailWord_4986905, baseEnd_4986905] using wordTrace_append hprefix tailTrace_4986905
  have hstable : (prefixWord ++ tailWord_4986905).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4986905).length < 2 ^ (prefixWord ++ tailWord_4986905).sum := by decide
  have hdescent : baseEnd_4986905 < baseStart_4986905 := by decide
  rcases family_descends (prefixWord ++ tailWord_4986905) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4986929 : List Nat := [1, 2, 2, 3, 1, 3, 3, 1, 3, 4]
def baseStart_4986929 : Nat := 118140960795 + 4986929 * 2 ^ 59
def prefixEnd_4986929 : Nat := 4983230072969 + 3 ^ 40 * 4986929 * 2
def baseEnd_4986929 : Nat := 853563855615208117017679

theorem tailTrace_4986929 : CollatzResearch.WordTrace tailWord_4986929 prefixEnd_4986929 853563855615208117017679 := by
  unfold tailWord_4986929
  simp only [CollatzResearch.WordTrace]
  refine ⟨181888243350215407511035841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121258828900143605007357227 181888243350215407511035841)
  ·
    refine ⟨136416182512661555633276881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 181888243350215407511035841 136416182512661555633276881)
    ·
      refine ⟨102312136884496166724957661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 136416182512661555633276881 102312136884496166724957661)
      ·
        refine ⟨38367051331686062521859123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 102312136884496166724957661 38367051331686062521859123)
        ·
          refine ⟨57550576997529093782788685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38367051331686062521859123 57550576997529093782788685)
          ·
            refine ⟨21581466374073410168545757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 57550576997529093782788685 21581466374073410168545757)
            ·
              refine ⟨8093049890277528813204659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21581466374073410168545757 8093049890277528813204659)
              ·
                refine ⟨12139574835416293219806989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8093049890277528813204659 12139574835416293219806989)
                ·
                  refine ⟨4552340563281109957427621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12139574835416293219806989 4552340563281109957427621)
                  ·
                    refine ⟨853563855615208117017679, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4552340563281109957427621 853563855615208117017679)
                    ·
                      rfl

theorem cell23_4986929_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 3, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 3, 3, 1, 3, 4].length) (baseStart_4986929 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4986929 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4986929 prefixEnd_4986929 := by exact prefixLift 4986929
  have htrace : WordTrace (prefixWord ++ tailWord_4986929) baseStart_4986929 baseEnd_4986929 := by
    simpa [prefixWord, tailWord_4986929, baseEnd_4986929] using wordTrace_append hprefix tailTrace_4986929
  have hstable : (prefixWord ++ tailWord_4986929).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4986929).length < 2 ^ (prefixWord ++ tailWord_4986929).sum := by decide
  have hdescent : baseEnd_4986929 < baseStart_4986929 := by decide
  rcases family_descends (prefixWord ++ tailWord_4986929) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4986955 : List Nat := [1, 1, 1, 1, 3, 1, 2, 2, 2, 9]
def baseStart_4986955 : Nat := 118140960795 + 4986955 * 2 ^ 59
def prefixEnd_4986955 : Nat := 4983230072969 + 3 ^ 40 * 4986955 * 2
def baseEnd_4986955 : Nat := 853568305780880416442639

theorem tailTrace_4986955 : CollatzResearch.WordTrace tailWord_4986955 prefixEnd_4986955 853568305780880416442639 := by
  unfold tailWord_4986955
  simp only [CollatzResearch.WordTrace]
  refine ⟨181889191648121213951482319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121259461098747475967654879 181889191648121213951482319)
  ·
    refine ⟨272833787472181820927223479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 181889191648121213951482319 272833787472181820927223479)
    ·
      refine ⟨409250681208272731390835219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 272833787472181820927223479 409250681208272731390835219)
      ·
        refine ⟨613876021812409097086252829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 409250681208272731390835219 613876021812409097086252829)
        ·
          refine ⟨230203508179653411407344811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 613876021812409097086252829 230203508179653411407344811)
          ·
            refine ⟨345305262269480117111017217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 230203508179653411407344811 345305262269480117111017217)
            ·
              refine ⟨258978946702110087833262913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 345305262269480117111017217 258978946702110087833262913)
              ·
                refine ⟨194234210026582565874947185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 258978946702110087833262913 194234210026582565874947185)
                ·
                  refine ⟨145675657519936924406210389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 194234210026582565874947185 145675657519936924406210389)
                  ·
                    refine ⟨853568305780880416442639, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 145675657519936924406210389 853568305780880416442639)
                    ·
                      rfl

theorem cell23_4986955_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 2, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 2, 2, 2, 9].length) (baseStart_4986955 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4986955 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4986955 prefixEnd_4986955 := by exact prefixLift 4986955
  have htrace : WordTrace (prefixWord ++ tailWord_4986955) baseStart_4986955 baseEnd_4986955 := by
    simpa [prefixWord, tailWord_4986955, baseEnd_4986955] using wordTrace_append hprefix tailTrace_4986955
  have hstable : (prefixWord ++ tailWord_4986955).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4986955).length < 2 ^ (prefixWord ++ tailWord_4986955).sum := by decide
  have hdescent : baseEnd_4986955 < baseStart_4986955 := by decide
  rcases family_descends (prefixWord ++ tailWord_4986955) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4987013 : List Nat := [1, 3, 1, 1, 5, 3, 1, 1, 2, 3, 2]
def baseStart_4987013 : Nat := 118140960795 + 4987013 * 2 ^ 59
def prefixEnd_4987013 : Nat := 4983230072969 + 3 ^ 40 * 4987013 * 2
def baseEnd_4987013 : Nat := 2560734699220602022402651

theorem tailTrace_4987013 : CollatzResearch.WordTrace tailWord_4987013 prefixEnd_4987013 2560734699220602022402651 := by
  unfold tailWord_4987013
  simp only [CollatzResearch.WordTrace]
  refine ⟨181891307081911089857093693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121260871387940726571395795 181891307081911089857093693)
  ·
    refine ⟨68209240155716658696410135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 181891307081911089857093693 68209240155716658696410135)
    ·
      refine ⟨102313860233574988044615203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68209240155716658696410135 102313860233574988044615203)
      ·
        refine ⟨153470790350362482066922805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 102313860233574988044615203 153470790350362482066922805)
        ·
          refine ⟨14387886595346482693774013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 153470790350362482066922805 14387886595346482693774013)
          ·
            refine ⟨5395457473254931010165255, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14387886595346482693774013 5395457473254931010165255)
            ·
              refine ⟨8093186209882396515247883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5395457473254931010165255 8093186209882396515247883)
              ·
                refine ⟨12139779314823594772871825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8093186209882396515247883 12139779314823594772871825)
                ·
                  refine ⟨9104834486117696079653869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12139779314823594772871825 9104834486117696079653869)
                  ·
                    refine ⟨3414312932294136029870201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9104834486117696079653869 3414312932294136029870201)
                    ·
                      refine ⟨2560734699220602022402651, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3414312932294136029870201 2560734699220602022402651)
                      ·
                        rfl

theorem cell23_4987013_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 3, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 3, 1, 1, 2, 3, 2].length) (baseStart_4987013 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4987013 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4987013 prefixEnd_4987013 := by exact prefixLift 4987013
  have htrace : WordTrace (prefixWord ++ tailWord_4987013) baseStart_4987013 baseEnd_4987013 := by
    simpa [prefixWord, tailWord_4987013, baseEnd_4987013] using wordTrace_append hprefix tailTrace_4987013
  have hstable : (prefixWord ++ tailWord_4987013).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4987013).length < 2 ^ (prefixWord ++ tailWord_4987013).sum := by decide
  have hdescent : baseEnd_4987013 < baseStart_4987013 := by decide
  rcases family_descends (prefixWord ++ tailWord_4987013) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4987026 : List Nat := [3, 2, 3, 1, 1, 1, 3, 3, 1, 1, 4]
def baseStart_4987026 : Nat := 118140960795 + 4987026 * 2 ^ 59
def prefixEnd_4987026 : Nat := 4983230072969 + 3 ^ 40 * 4987026 * 2
def baseEnd_4987026 : Nat := 2560741374469110471540091

theorem tailTrace_4987026 : CollatzResearch.WordTrace tailWord_4987026 prefixEnd_4987026 2560741374469110471540091 := by
  unfold tailWord_4987026
  simp only [CollatzResearch.WordTrace]
  refine ⟨45472945307715998269329233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 121261187487242662051544621 45472945307715998269329233)
  ·
    refine ⟨34104708980786998701996925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45472945307715998269329233 34104708980786998701996925)
    ·
      refine ⟨12789265867795124513248847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 34104708980786998701996925 12789265867795124513248847)
      ·
        refine ⟨19183898801692686769873271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12789265867795124513248847 19183898801692686769873271)
        ·
          refine ⟨28775848202539030154809907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19183898801692686769873271 28775848202539030154809907)
          ·
            refine ⟨43163772303808545232214861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28775848202539030154809907 43163772303808545232214861)
            ·
              refine ⟨16186414613928204462080573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 43163772303808545232214861 16186414613928204462080573)
              ·
                refine ⟨6069905480223076673280215, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16186414613928204462080573 6069905480223076673280215)
                ·
                  refine ⟨9104858220334615009920323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6069905480223076673280215 9104858220334615009920323)
                  ·
                    refine ⟨13657287330501922514880485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9104858220334615009920323 13657287330501922514880485)
                    ·
                      refine ⟨2560741374469110471540091, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13657287330501922514880485 2560741374469110471540091)
                      ·
                        rfl

theorem cell23_4987026_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 3, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 3, 3, 1, 1, 4].length) (baseStart_4987026 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4987026 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4987026 prefixEnd_4987026 := by exact prefixLift 4987026
  have htrace : WordTrace (prefixWord ++ tailWord_4987026) baseStart_4987026 baseEnd_4987026 := by
    simpa [prefixWord, tailWord_4987026, baseEnd_4987026] using wordTrace_append hprefix tailTrace_4987026
  have hstable : (prefixWord ++ tailWord_4987026).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4987026).length < 2 ^ (prefixWord ++ tailWord_4987026).sum := by decide
  have hdescent : baseEnd_4987026 < baseStart_4987026 := by decide
  rcases family_descends (prefixWord ++ tailWord_4987026) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4987116 : List Nat := [2, 2, 1, 1, 2, 3, 2, 3, 1, 4, 2]
def baseStart_4987116 : Nat := 118140960795 + 4987116 * 2 ^ 59
def prefixEnd_4987116 : Nat := 4983230072969 + 3 ^ 40 * 4987116 * 2
def baseEnd_4987116 : Nat := 2560787587728015119414677

theorem tailTrace_4987116 : CollatzResearch.WordTrace tailWord_4987116 prefixEnd_4987116 2560787587728015119414677 := by
  unfold tailWord_4987116
  simp only [CollatzResearch.WordTrace]
  refine ⟨90947531900268969224046601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 121263375867025292298728801 90947531900268969224046601)
  ·
    refine ⟨68210648925201726918034951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 90947531900268969224046601 68210648925201726918034951)
    ·
      refine ⟨102315973387802590377052427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68210648925201726918034951 102315973387802590377052427)
      ·
        refine ⟨153473960081703885565578641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 102315973387802590377052427 153473960081703885565578641)
        ·
          refine ⟨115105470061277914174183981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 153473960081703885565578641 115105470061277914174183981)
          ·
            refine ⟨43164551272979217815318993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 115105470061277914174183981 43164551272979217815318993)
            ·
              refine ⟨32373413454734413361489245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 43164551272979217815318993 32373413454734413361489245)
              ·
                refine ⟨12140030045525405010558467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 32373413454734413361489245 12140030045525405010558467)
                ·
                  refine ⟨18210045068288107515837701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12140030045525405010558467 18210045068288107515837701)
                  ·
                    refine ⟨3414383450304020159219569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 18210045068288107515837701 3414383450304020159219569)
                    ·
                      refine ⟨2560787587728015119414677, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3414383450304020159219569 2560787587728015119414677)
                      ·
                        rfl

theorem cell23_4987116_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 4, 2].length) (baseStart_4987116 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4987116 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4987116 prefixEnd_4987116 := by exact prefixLift 4987116
  have htrace : WordTrace (prefixWord ++ tailWord_4987116) baseStart_4987116 baseEnd_4987116 := by
    simpa [prefixWord, tailWord_4987116, baseEnd_4987116] using wordTrace_append hprefix tailTrace_4987116
  have hstable : (prefixWord ++ tailWord_4987116).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4987116).length < 2 ^ (prefixWord ++ tailWord_4987116).sum := by decide
  have hdescent : baseEnd_4987116 < baseStart_4987116 := by decide
  rcases family_descends (prefixWord ++ tailWord_4987116) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4987119 : List Nat := [1, 1, 2, 1, 6, 1, 1, 2, 2, 1, 5]
def baseStart_4987119 : Nat := 118140960795 + 4987119 * 2 ^ 59
def prefixEnd_4987119 : Nat := 4983230072969 + 3 ^ 40 * 4987119 * 2
def baseEnd_4987119 : Nat := 2560789128169978607677163

theorem tailTrace_4987119 : CollatzResearch.WordTrace tailWord_4987119 prefixEnd_4987119 2560789128169978607677163 := by
  unfold tailWord_4987119
  simp only [CollatzResearch.WordTrace]
  refine ⟨181895173219527069960452411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121263448813018046640301607 181895173219527069960452411)
  ·
    refine ⟨272842759829290604940678617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 181895173219527069960452411 272842759829290604940678617)
    ·
      refine ⟨204632069871967953705508963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 272842759829290604940678617 204632069871967953705508963)
      ·
        refine ⟨306948104807951930558263445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 204632069871967953705508963 306948104807951930558263445)
        ·
          refine ⟨14388192412872746744918599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 306948104807951930558263445 14388192412872746744918599)
          ·
            refine ⟨21582288619309120117377899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14388192412872746744918599 21582288619309120117377899)
            ·
              refine ⟨32373432928963680176066849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21582288619309120117377899 32373432928963680176066849)
              ·
                refine ⟨24280074696722760132050137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 32373432928963680176066849 24280074696722760132050137)
                ·
                  refine ⟨18210056022542070099037603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 24280074696722760132050137 18210056022542070099037603)
                  ·
                    refine ⟨27315084033813105148556405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 18210056022542070099037603 27315084033813105148556405)
                    ·
                      refine ⟨2560789128169978607677163, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 27315084033813105148556405 2560789128169978607677163)
                      ·
                        rfl

theorem cell23_4987119_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 1, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 1, 1, 2, 2, 1, 5].length) (baseStart_4987119 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4987119 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4987119 prefixEnd_4987119 := by exact prefixLift 4987119
  have htrace : WordTrace (prefixWord ++ tailWord_4987119) baseStart_4987119 baseEnd_4987119 := by
    simpa [prefixWord, tailWord_4987119, baseEnd_4987119] using wordTrace_append hprefix tailTrace_4987119
  have hstable : (prefixWord ++ tailWord_4987119).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4987119).length < 2 ^ (prefixWord ++ tailWord_4987119).sum := by decide
  have hdescent : baseEnd_4987119 < baseStart_4987119 := by decide
  rcases family_descends (prefixWord ++ tailWord_4987119) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4987150 : List Nat := [4, 1, 1, 2, 1, 2, 4, 2, 2, 2, 2]
def baseStart_4987150 : Nat := 118140960795 + 4987150 * 2 ^ 59
def prefixEnd_4987150 : Nat := 4983230072969 + 3 ^ 40 * 4987150 * 2
def baseEnd_4987150 : Nat := 2560805046070267986389521

theorem tailTrace_4987150 : CollatzResearch.WordTrace tailWord_4987150 prefixEnd_4987150 2560805046070267986389521 := by
  unfold tailWord_4987150
  simp only [CollatzResearch.WordTrace]
  refine ⟨22737037985301845281853863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 121264202588276508169887269 22737037985301845281853863)
  ·
    refine ⟨34105556977952767922780795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22737037985301845281853863 34105556977952767922780795)
    ·
      refine ⟨51158335466929151884171193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34105556977952767922780795 51158335466929151884171193)
      ·
        refine ⟨38368751600196863913128395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 51158335466929151884171193 38368751600196863913128395)
        ·
          refine ⟨57553127400295295869692593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38368751600196863913128395 57553127400295295869692593)
          ·
            refine ⟨43164845550221471902269445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 57553127400295295869692593 43164845550221471902269445)
            ·
              refine ⟨8093408540666525981675521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 43164845550221471902269445 8093408540666525981675521)
              ·
                refine ⟨6070056405499894486256641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8093408540666525981675521 6070056405499894486256641)
                ·
                  refine ⟨4552542304124920864692481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6070056405499894486256641 4552542304124920864692481)
                  ·
                    refine ⟨3414406728093690648519361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4552542304124920864692481 3414406728093690648519361)
                    ·
                      refine ⟨2560805046070267986389521, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3414406728093690648519361 2560805046070267986389521)
                      ·
                        rfl

theorem cell23_4987150_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 4, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 4, 2, 2, 2, 2].length) (baseStart_4987150 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4987150 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4987150 prefixEnd_4987150 := by exact prefixLift 4987150
  have htrace : WordTrace (prefixWord ++ tailWord_4987150) baseStart_4987150 baseEnd_4987150 := by
    simpa [prefixWord, tailWord_4987150, baseEnd_4987150] using wordTrace_append hprefix tailTrace_4987150
  have hstable : (prefixWord ++ tailWord_4987150).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4987150).length < 2 ^ (prefixWord ++ tailWord_4987150).sum := by decide
  have hdescent : baseEnd_4987150 < baseStart_4987150 := by decide
  rcases family_descends (prefixWord ++ tailWord_4987150) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4987169 : List Nat := [1, 2, 3, 2, 1, 1, 2, 2, 4, 5]
def baseStart_4987169 : Nat := 118140960795 + 4987169 * 2 ^ 59
def prefixEnd_4987169 : Nat := 4983230072969 + 3 ^ 40 * 4987169 * 2
def baseEnd_4987169 : Nat := 853604934067567804017311

theorem tailTrace_4987169 : CollatzResearch.WordTrace tailWord_4987169 prefixEnd_4987169 853604934067567804017311 := by
  unfold tailWord_4987169
  simp only [CollatzResearch.WordTrace]
  refine ⟨181896996869345928499772561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121264664579563952333181707 181896996869345928499772561)
  ·
    refine ⟨136422747652009446374829421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 181896996869345928499772561 136422747652009446374829421)
    ·
      refine ⟨51158530369503542390561033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 136422747652009446374829421 51158530369503542390561033)
      ·
        refine ⟨38368897777127656792920775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 51158530369503542390561033 38368897777127656792920775)
        ·
          refine ⟨57553346665691485189381163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38368897777127656792920775 57553346665691485189381163)
          ·
            refine ⟨86330019998537227784071745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 57553346665691485189381163 86330019998537227784071745)
            ·
              refine ⟨64747514998902920838053809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 86330019998537227784071745 64747514998902920838053809)
              ·
                refine ⟨48560636249177190628540357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 64747514998902920838053809 48560636249177190628540357)
                ·
                  refine ⟨9105119296720723242851317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 48560636249177190628540357 9105119296720723242851317)
                  ·
                    refine ⟨853604934067567804017311, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9105119296720723242851317 853604934067567804017311)
                    ·
                      rfl

theorem cell23_4987169_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 2, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 2, 2, 4, 5].length) (baseStart_4987169 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4987169 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4987169 prefixEnd_4987169 := by exact prefixLift 4987169
  have htrace : WordTrace (prefixWord ++ tailWord_4987169) baseStart_4987169 baseEnd_4987169 := by
    simpa [prefixWord, tailWord_4987169, baseEnd_4987169] using wordTrace_append hprefix tailTrace_4987169
  have hstable : (prefixWord ++ tailWord_4987169).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4987169).length < 2 ^ (prefixWord ++ tailWord_4987169).sum := by decide
  have hdescent : baseEnd_4987169 < baseStart_4987169 := by decide
  rcases family_descends (prefixWord ++ tailWord_4987169) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4987186 : List Nat := [3, 2, 1, 1, 5, 1, 1, 1, 1, 7]
def baseStart_4987186 : Nat := 118140960795 + 4987186 * 2 ^ 59
def prefixEnd_4987186 : Nat := 4983230072969 + 3 ^ 40 * 4987186 * 2
def baseEnd_4987186 : Nat := 853607843791276615179785

theorem tailTrace_4987186 : CollatzResearch.WordTrace tailWord_4987186 prefixEnd_4987186 853607843791276615179785 := by
  unfold tailWord_4987186
  simp only [CollatzResearch.WordTrace]
  refine ⟨45474404227571085100785353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 121265077940189560268760941 45474404227571085100785353)
  ·
    refine ⟨34105803170678313825589015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45474404227571085100785353 34105803170678313825589015)
    ·
      refine ⟨51158704756017470738383523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34105803170678313825589015 51158704756017470738383523)
      ·
        refine ⟨76738057134026206107575285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51158704756017470738383523 76738057134026206107575285)
        ·
          refine ⟨7194192856314956822585183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 76738057134026206107575285 7194192856314956822585183)
          ·
            refine ⟨10791289284472435233877775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7194192856314956822585183 10791289284472435233877775)
            ·
              refine ⟨16186933926708652850816663, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10791289284472435233877775 16186933926708652850816663)
              ·
                refine ⟨24280400890062979276224995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16186933926708652850816663 24280400890062979276224995)
                ·
                  refine ⟨36420601335094468914337493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24280400890062979276224995 36420601335094468914337493)
                  ·
                    refine ⟨853607843791276615179785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 36420601335094468914337493 853607843791276615179785)
                    ·
                      rfl

theorem cell23_4987186_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 5, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 5, 1, 1, 1, 1, 7].length) (baseStart_4987186 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4987186 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4987186 prefixEnd_4987186 := by exact prefixLift 4987186
  have htrace : WordTrace (prefixWord ++ tailWord_4987186) baseStart_4987186 baseEnd_4987186 := by
    simpa [prefixWord, tailWord_4987186, baseEnd_4987186] using wordTrace_append hprefix tailTrace_4987186
  have hstable : (prefixWord ++ tailWord_4987186).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4987186).length < 2 ^ (prefixWord ++ tailWord_4987186).sum := by decide
  have hdescent : baseEnd_4987186 < baseStart_4987186 := by decide
  rcases family_descends (prefixWord ++ tailWord_4987186) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4987216 : List Nat := [2, 1, 1, 1, 1, 6, 1, 3, 3, 4]
def baseStart_4987216 : Nat := 118140960795 + 4987216 * 2 ^ 59
def prefixEnd_4987216 : Nat := 4983230072969 + 3 ^ 40 * 4987216 * 2
def baseEnd_4987216 : Nat := 853612978597821576054739

theorem tailTrace_4987216 : CollatzResearch.WordTrace tailWord_4987216 prefixEnd_4987216 853612978597821576054739 := by
  unfold tailWord_4987216
  simp only [CollatzResearch.WordTrace]
  refine ⟨90949355550087827763366751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 121265807400117103684489001 90949355550087827763366751)
  ·
    refine ⟨136424033325131741645050127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90949355550087827763366751 136424033325131741645050127)
    ·
      refine ⟨204636049987697612467575191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 136424033325131741645050127 204636049987697612467575191)
      ·
        refine ⟨306954074981546418701362787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 204636049987697612467575191 306954074981546418701362787)
        ·
          refine ⟨460431112472319628052044181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 306954074981546418701362787 460431112472319628052044181)
          ·
            refine ⟨21582708397139982564939571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 460431112472319628052044181 21582708397139982564939571)
            ·
              refine ⟨32374062595709973847409357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21582708397139982564939571 32374062595709973847409357)
              ·
                refine ⟨12140273473391240192778509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 32374062595709973847409357 12140273473391240192778509)
                ·
                  refine ⟨4552602552521715072291941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12140273473391240192778509 4552602552521715072291941)
                  ·
                    refine ⟨853612978597821576054739, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4552602552521715072291941 853612978597821576054739)
                    ·
                      rfl

theorem cell23_4987216_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 6, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 6, 1, 3, 3, 4].length) (baseStart_4987216 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4987216 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4987216 prefixEnd_4987216 := by exact prefixLift 4987216
  have htrace : WordTrace (prefixWord ++ tailWord_4987216) baseStart_4987216 baseEnd_4987216 := by
    simpa [prefixWord, tailWord_4987216, baseEnd_4987216] using wordTrace_append hprefix tailTrace_4987216
  have hstable : (prefixWord ++ tailWord_4987216).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4987216).length < 2 ^ (prefixWord ++ tailWord_4987216).sum := by decide
  have hdescent : baseEnd_4987216 < baseStart_4987216 := by decide
  rcases family_descends (prefixWord ++ tailWord_4987216) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4987250 : List Nat := [3, 2, 1, 2, 1, 3, 3, 3, 1, 4]
def baseStart_4987250 : Nat := 118140960795 + 4987250 * 2 ^ 59
def prefixEnd_4987250 : Nat := 4983230072969 + 3 ^ 40 * 4987250 * 2
def baseEnd_4987250 : Nat := 853618798045239198379687

theorem tailTrace_4987250 : CollatzResearch.WordTrace tailWord_4987250 prefixEnd_4987250 853618798045239198379687 := by
  unfold tailWord_4987250
  simp only [CollatzResearch.WordTrace]
  refine ⟨45474987795513119833367801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 121266634121368319555647469 45474987795513119833367801)
  ·
    refine ⟨34106240846634839875025851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45474987795513119833367801 34106240846634839875025851)
    ·
      refine ⟨51159361269952259812538777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34106240846634839875025851 51159361269952259812538777)
      ·
        refine ⟨38369520952464194859404083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 51159361269952259812538777 38369520952464194859404083)
        ·
          refine ⟨57554281428696292289106125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38369520952464194859404083 57554281428696292289106125)
          ·
            refine ⟨21582855535761109608414797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 57554281428696292289106125 21582855535761109608414797)
            ·
              refine ⟨8093570825910416103155549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21582855535761109608414797 8093570825910416103155549)
              ·
                refine ⟨3035089059716406038683331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8093570825910416103155549 3035089059716406038683331)
                ·
                  refine ⟨4552633589574609058024997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3035089059716406038683331 4552633589574609058024997)
                  ·
                    refine ⟨853618798045239198379687, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4552633589574609058024997 853618798045239198379687)
                    ·
                      rfl

theorem cell23_4987250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 3, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 3, 3, 3, 1, 4].length) (baseStart_4987250 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4987250 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4987250 prefixEnd_4987250 := by exact prefixLift 4987250
  have htrace : WordTrace (prefixWord ++ tailWord_4987250) baseStart_4987250 baseEnd_4987250 := by
    simpa [prefixWord, tailWord_4987250, baseEnd_4987250] using wordTrace_append hprefix tailTrace_4987250
  have hstable : (prefixWord ++ tailWord_4987250).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4987250).length < 2 ^ (prefixWord ++ tailWord_4987250).sum := by decide
  have hdescent : baseEnd_4987250 < baseStart_4987250 := by decide
  rcases family_descends (prefixWord ++ tailWord_4987250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4987267 : List Nat := [1, 1, 1, 3, 6, 1, 3, 2, 1, 4]
def baseStart_4987267 : Nat := 118140960795 + 4987267 * 2 ^ 59
def prefixEnd_4987267 : Nat := 4983230072969 + 3 ^ 40 * 4987267 * 2
def baseEnd_4987267 : Nat := 853621707768948009542161

theorem tailTrace_4987267 : CollatzResearch.WordTrace tailWord_4987267 prefixEnd_4987267 853621707768948009542161 := by
  unfold tailWord_4987267
  simp only [CollatzResearch.WordTrace]
  refine ⟨181900571222990891236840055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121267047481993927491226703 181900571222990891236840055)
  ·
    refine ⟨272850856834486336855260083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 181900571222990891236840055 272850856834486336855260083)
    ·
      refine ⟨409276285251729505282890125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 272850856834486336855260083 409276285251729505282890125)
      ·
        refine ⟨153478606969398564481083797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 409276285251729505282890125 153478606969398564481083797)
        ·
          refine ⟨7194309701690557710050803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 153478606969398564481083797 7194309701690557710050803)
          ·
            refine ⟨10791464552535836565076205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7194309701690557710050803 10791464552535836565076205)
            ·
              refine ⟨4046799207200938711903577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10791464552535836565076205 4046799207200938711903577)
              ·
                refine ⟨3035099405400704033927683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4046799207200938711903577 3035099405400704033927683)
                ·
                  refine ⟨4552649108101056050891525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3035099405400704033927683 4552649108101056050891525)
                  ·
                    refine ⟨853621707768948009542161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4552649108101056050891525 853621707768948009542161)
                    ·
                      rfl

theorem cell23_4987267_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 6, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 6, 1, 3, 2, 1, 4].length) (baseStart_4987267 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4987267 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4987267 prefixEnd_4987267 := by exact prefixLift 4987267
  have htrace : WordTrace (prefixWord ++ tailWord_4987267) baseStart_4987267 baseEnd_4987267 := by
    simpa [prefixWord, tailWord_4987267, baseEnd_4987267] using wordTrace_append hprefix tailTrace_4987267
  have hstable : (prefixWord ++ tailWord_4987267).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4987267).length < 2 ^ (prefixWord ++ tailWord_4987267).sum := by decide
  have hdescent : baseEnd_4987267 < baseStart_4987267 := by decide
  rcases family_descends (prefixWord ++ tailWord_4987267) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4987269 : List Nat := [1, 3, 1, 1, 3, 1, 1, 2, 2, 1, 7]
def baseStart_4987269 : Nat := 118140960795 + 4987269 * 2 ^ 59
def prefixEnd_4987269 : Nat := 4983230072969 + 3 ^ 40 * 4987269 * 2
def baseEnd_4987269 : Nat := 2560866150268153020801473

theorem tailTrace_4987269 : CollatzResearch.WordTrace tailWord_4987269 prefixEnd_4987269 2560866150268153020801473 := by
  unfold tailWord_4987269
  simp only [CollatzResearch.WordTrace]
  refine ⟨181900644168983645578412861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121267096112655763718941907 181900644168983645578412861)
  ·
    refine ⟨68212741563368867091904823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 181900644168983645578412861 68212741563368867091904823)
    ·
      refine ⟨102319112345053300637857235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68212741563368867091904823 102319112345053300637857235)
      ·
        refine ⟨153478668517579950956785853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 102319112345053300637857235 153478668517579950956785853)
        ·
          refine ⟨57554500694092481608794695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 153478668517579950956785853 57554500694092481608794695)
          ·
            refine ⟨86331751041138722413192043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 57554500694092481608794695 86331751041138722413192043)
            ·
              refine ⟨129497626561708083619788065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 86331751041138722413192043 129497626561708083619788065)
              ·
                refine ⟨97123219921281062714841049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 129497626561708083619788065 97123219921281062714841049)
                ·
                  refine ⟨72842414940960797036130787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 97123219921281062714841049 72842414940960797036130787)
                  ·
                    refine ⟨109263622411441195554196181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 72842414940960797036130787 109263622411441195554196181)
                    ·
                      refine ⟨2560866150268153020801473, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 109263622411441195554196181 2560866150268153020801473)
                      ·
                        rfl

theorem cell23_4987269_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 1, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 1, 2, 2, 1, 7].length) (baseStart_4987269 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4987269 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4987269 prefixEnd_4987269 := by exact prefixLift 4987269
  have htrace : WordTrace (prefixWord ++ tailWord_4987269) baseStart_4987269 baseEnd_4987269 := by
    simpa [prefixWord, tailWord_4987269, baseEnd_4987269] using wordTrace_append hprefix tailTrace_4987269
  have hstable : (prefixWord ++ tailWord_4987269).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4987269).length < 2 ^ (prefixWord ++ tailWord_4987269).sum := by decide
  have hdescent : baseEnd_4987269 < baseStart_4987269 := by decide
  rcases family_descends (prefixWord ++ tailWord_4987269) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4987293 : List Nat := [1, 4, 2, 1, 4, 1, 1, 1, 3, 5]
def baseStart_4987293 : Nat := 118140960795 + 4987293 * 2 ^ 59
def prefixEnd_4987293 : Nat := 4983230072969 + 3 ^ 40 * 4987293 * 2
def baseEnd_4987293 : Nat := 853626157934620308967121

theorem tailTrace_4987293 : CollatzResearch.WordTrace tailWord_4987293 prefixEnd_4987293 853626157934620308967121 := by
  unfold tailWord_4987293
  simp only [CollatzResearch.WordTrace]
  refine ⟨181901519520896697677286533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121267679680597798451524355 181901519520896697677286533)
  ·
    refine ⟨34106534910168130814491225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 181901519520896697677286533 34106534910168130814491225)
    ·
      refine ⟨25579901182626098110868419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34106534910168130814491225 25579901182626098110868419)
      ·
        refine ⟨38369851773939147166302629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25579901182626098110868419 38369851773939147166302629)
        ·
          refine ⟨7194347207613590093681743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 38369851773939147166302629 7194347207613590093681743)
          ·
            refine ⟨10791520811420385140522615, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7194347207613590093681743 10791520811420385140522615)
            ·
              refine ⟨16187281217130577710783923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10791520811420385140522615 16187281217130577710783923)
              ·
                refine ⟨24280921825695866566175885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16187281217130577710783923 24280921825695866566175885)
                ·
                  refine ⟨9105345684635949962315957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 24280921825695866566175885 9105345684635949962315957)
                  ·
                    refine ⟨853626157934620308967121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9105345684635949962315957 853626157934620308967121)
                    ·
                      rfl

theorem cell23_4987293_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 4, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 4, 1, 1, 1, 3, 5].length) (baseStart_4987293 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4987293 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4987293 prefixEnd_4987293 := by exact prefixLift 4987293
  have htrace : WordTrace (prefixWord ++ tailWord_4987293) baseStart_4987293 baseEnd_4987293 := by
    simpa [prefixWord, tailWord_4987293, baseEnd_4987293] using wordTrace_append hprefix tailTrace_4987293
  have hstable : (prefixWord ++ tailWord_4987293).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4987293).length < 2 ^ (prefixWord ++ tailWord_4987293).sum := by decide
  have hdescent : baseEnd_4987293 < baseStart_4987293 := by decide
  rcases family_descends (prefixWord ++ tailWord_4987293) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4987319 : List Nat := [1, 1, 3, 1, 3, 14]
def baseStart_4987319 : Nat := 118140960795 + 4987319 * 2 ^ 59
def prefixEnd_4987319 : Nat := 4983230072969 + 3 ^ 40 * 4987319 * 2
def baseEnd_4987319 : Nat := 10538649482719661832001

theorem tailTrace_4987319 : CollatzResearch.WordTrace tailWord_4987319 prefixEnd_4987319 10538649482719661832001 := by
  unfold tailWord_4987319
  simp only [CollatzResearch.WordTrace]
  refine ⟨181902467818802504117733011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121268311879201669411822007 181902467818802504117733011)
  ·
    refine ⟨272853701728203756176599517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 181902467818802504117733011 272853701728203756176599517)
    ·
      refine ⟨102320138148076408566224819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 272853701728203756176599517 102320138148076408566224819)
      ·
        refine ⟨153480207222114612849337229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 102320138148076408566224819 153480207222114612849337229)
        ·
          refine ⟨57555077708292979818501461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 153480207222114612849337229 57555077708292979818501461)
          ·
            refine ⟨10538649482719661832001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 14 57555077708292979818501461 10538649482719661832001)
            ·
              rfl

theorem cell23_4987319_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 14].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 14].length) (baseStart_4987319 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4987319 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4987319 prefixEnd_4987319 := by exact prefixLift 4987319
  have htrace : WordTrace (prefixWord ++ tailWord_4987319) baseStart_4987319 baseEnd_4987319 := by
    simpa [prefixWord, tailWord_4987319, baseEnd_4987319] using wordTrace_append hprefix tailTrace_4987319
  have hstable : (prefixWord ++ tailWord_4987319).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4987319).length < 2 ^ (prefixWord ++ tailWord_4987319).sum := by decide
  have hdescent : baseEnd_4987319 < baseStart_4987319 := by decide
  rcases family_descends (prefixWord ++ tailWord_4987319) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4987324 : List Nat := [2, 2, 2, 4, 1, 1, 4, 2, 1, 1, 3]
def baseStart_4987324 : Nat := 118140960795 + 4987324 * 2 ^ 59
def prefixEnd_4987324 : Nat := 4983230072969 + 3 ^ 40 * 4987324 * 2
def baseEnd_4987324 : Nat := 2560894391704150305613721

theorem tailTrace_4987324 : CollatzResearch.WordTrace tailWord_4987324 prefixEnd_4987324 2560894391704150305613721 := by
  unfold tailWord_4987324
  simp only [CollatzResearch.WordTrace]
  refine ⟨90951325091892194985832513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 121268433455856259981110017 90951325091892194985832513)
  ·
    refine ⟨68213493818919146239374385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 90951325091892194985832513 68213493818919146239374385)
    ·
      refine ⟨51160120364189359679530789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 68213493818919146239374385 51160120364189359679530789)
      ·
        refine ⟨9592522568285504939912023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 51160120364189359679530789 9592522568285504939912023)
        ·
          refine ⟨14388783852428257409868035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9592522568285504939912023 14388783852428257409868035)
          ·
            refine ⟨21583175778642386114802053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14388783852428257409868035 21583175778642386114802053)
            ·
              refine ⟨4046845458495447396525385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 21583175778642386114802053 4046845458495447396525385)
              ·
                refine ⟨3035134093871585547394039, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4046845458495447396525385 3035134093871585547394039)
                ·
                  refine ⟨4552701140807378321091059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3035134093871585547394039 4552701140807378321091059)
                  ·
                    refine ⟨6829051711211067481636589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4552701140807378321091059 6829051711211067481636589)
                    ·
                      refine ⟨2560894391704150305613721, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6829051711211067481636589 2560894391704150305613721)
                      ·
                        rfl

theorem cell23_4987324_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 1, 4, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 1, 4, 2, 1, 1, 3].length) (baseStart_4987324 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4987324 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4987324 prefixEnd_4987324 := by exact prefixLift 4987324
  have htrace : WordTrace (prefixWord ++ tailWord_4987324) baseStart_4987324 baseEnd_4987324 := by
    simpa [prefixWord, tailWord_4987324, baseEnd_4987324] using wordTrace_append hprefix tailTrace_4987324
  have hstable : (prefixWord ++ tailWord_4987324).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4987324).length < 2 ^ (prefixWord ++ tailWord_4987324).sum := by decide
  have hdescent : baseEnd_4987324 < baseStart_4987324 := by decide
  rcases family_descends (prefixWord ++ tailWord_4987324) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4987326 : List Nat := [4, 2, 1, 1, 1, 1, 2, 1, 3, 1, 6]
def baseStart_4987326 : Nat := 118140960795 + 4987326 * 2 ^ 59
def prefixEnd_4987326 : Nat := 4983230072969 + 3 ^ 40 * 4987326 * 2
def baseEnd_4987326 : Nat := 2560895418665459297788711

theorem tailTrace_4987326 : CollatzResearch.WordTrace tailWord_4987326 prefixEnd_4987326 2560895418665459297788711 := by
  unfold tailWord_4987326
  simp only [CollatzResearch.WordTrace]
  refine ⟨22737840391222143039154729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 121268482086518096208825221 22737840391222143039154729)
  ·
    refine ⟨17053380293416607279366047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22737840391222143039154729 17053380293416607279366047)
    ·
      refine ⟨25580070440124910919049071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17053380293416607279366047 25580070440124910919049071)
      ·
        refine ⟨38370105660187366378573607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25580070440124910919049071 38370105660187366378573607)
        ·
          refine ⟨57555158490281049567860411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38370105660187366378573607 57555158490281049567860411)
          ·
            refine ⟨86332737735421574351790617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 57555158490281049567860411 86332737735421574351790617)
            ·
              refine ⟨64749553301566180763842963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 86332737735421574351790617 64749553301566180763842963)
              ·
                refine ⟨97124329952349271145764445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 64749553301566180763842963 97124329952349271145764445)
                ·
                  refine ⟨36421623732130976679661667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 97124329952349271145764445 36421623732130976679661667)
                  ·
                    refine ⟨54632435598196465019492501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 36421623732130976679661667 54632435598196465019492501)
                    ·
                      refine ⟨2560895418665459297788711, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 54632435598196465019492501 2560895418665459297788711)
                      ·
                        rfl

theorem cell23_4987326_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 2, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 2, 1, 3, 1, 6].length) (baseStart_4987326 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4987326 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4987326 prefixEnd_4987326 := by exact prefixLift 4987326
  have htrace : WordTrace (prefixWord ++ tailWord_4987326) baseStart_4987326 baseEnd_4987326 := by
    simpa [prefixWord, tailWord_4987326, baseEnd_4987326] using wordTrace_append hprefix tailTrace_4987326
  have hstable : (prefixWord ++ tailWord_4987326).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4987326).length < 2 ^ (prefixWord ++ tailWord_4987326).sum := by decide
  have hdescent : baseEnd_4987326 < baseStart_4987326 := by decide
  rcases family_descends (prefixWord ++ tailWord_4987326) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4987336 : List Nat := [2, 1, 3, 1, 3, 2, 3, 8]
def baseStart_4987336 : Nat := 118140960795 + 4987336 * 2 ^ 59
def prefixEnd_4987336 : Nat := 4983230072969 + 3 ^ 40 * 4987336 * 2
def baseEnd_4987336 : Nat := 94848168647111268839395

theorem tailTrace_4987336 : CollatzResearch.WordTrace tailWord_4987336 prefixEnd_4987336 94848168647111268839395 := by
  unfold tailWord_4987336
  simp only [CollatzResearch.WordTrace]
  refine ⟨90951543929870458010550931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 121268725239827277347401241 90951543929870458010550931)
  ·
    refine ⟨136427315894805687015826397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90951543929870458010550931 136427315894805687015826397)
    ·
      refine ⟨51160243460552132630934899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 136427315894805687015826397 51160243460552132630934899)
      ·
        refine ⟨76740365190828198946402349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51160243460552132630934899 76740365190828198946402349)
        ·
          refine ⟨28777636946560574604900881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 76740365190828198946402349 28777636946560574604900881)
          ·
            refine ⟨21583227709920430953675661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28777636946560574604900881 21583227709920430953675661)
            ·
              refine ⟨8093710391220161607628373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21583227709920430953675661 8093710391220161607628373)
              ·
                refine ⟨94848168647111268839395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 8093710391220161607628373 94848168647111268839395)
                ·
                  rfl

theorem cell23_4987336_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 2, 3, 8].length) (baseStart_4987336 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4987336 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4987336 prefixEnd_4987336 := by exact prefixLift 4987336
  have htrace : WordTrace (prefixWord ++ tailWord_4987336) baseStart_4987336 baseEnd_4987336 := by
    simpa [prefixWord, tailWord_4987336, baseEnd_4987336] using wordTrace_append hprefix tailTrace_4987336
  have hstable : (prefixWord ++ tailWord_4987336).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4987336).length < 2 ^ (prefixWord ++ tailWord_4987336).sum := by decide
  have hdescent : baseEnd_4987336 < baseStart_4987336 := by decide
  rcases family_descends (prefixWord ++ tailWord_4987336) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4987350 : List Nat := [5, 2, 1, 1, 1, 1, 1, 3, 3, 2, 3]
def baseStart_4987350 : Nat := 118140960795 + 4987350 * 2 ^ 59
def prefixEnd_4987350 : Nat := 4983230072969 + 3 ^ 40 * 4987350 * 2
def baseEnd_4987350 : Nat := 2560907742201167203888601

theorem tailTrace_4987350 : CollatzResearch.WordTrace tailWord_4987350 prefixEnd_4987350 2560907742201167203888601 := by
  unfold tailWord_4987350
  simp only [CollatzResearch.WordTrace]
  refine ⟨11368974905105637275756969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 121269065654460130941407669 11368974905105637275756969)
  ·
    refine ⟨8526731178829227956817727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11368974905105637275756969 8526731178829227956817727)
    ·
      refine ⟨12790096768243841935226591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8526731178829227956817727 12790096768243841935226591)
      ·
        refine ⟨19185145152365762902839887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12790096768243841935226591 19185145152365762902839887)
        ·
          refine ⟨28777717728548644354259831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19185145152365762902839887 28777717728548644354259831)
          ·
            refine ⟨43166576592822966531389747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28777717728548644354259831 43166576592822966531389747)
            ·
              refine ⟨64749864889234449797084621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 43166576592822966531389747 64749864889234449797084621)
              ·
                refine ⟨24281199333462918673906733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 64749864889234449797084621 24281199333462918673906733)
                ·
                  refine ⟨9105449750048594502715025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 24281199333462918673906733 9105449750048594502715025)
                  ·
                    refine ⟨6829087312536445877036269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9105449750048594502715025 6829087312536445877036269)
                    ·
                      refine ⟨2560907742201167203888601, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6829087312536445877036269 2560907742201167203888601)
                      ·
                        rfl

theorem cell23_4987350_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 1, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 1, 3, 3, 2, 3].length) (baseStart_4987350 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4987350 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4987350 prefixEnd_4987350 := by exact prefixLift 4987350
  have htrace : WordTrace (prefixWord ++ tailWord_4987350) baseStart_4987350 baseEnd_4987350 := by
    simpa [prefixWord, tailWord_4987350, baseEnd_4987350] using wordTrace_append hprefix tailTrace_4987350
  have hstable : (prefixWord ++ tailWord_4987350).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4987350).length < 2 ^ (prefixWord ++ tailWord_4987350).sum := by decide
  have hdescent : baseEnd_4987350 < baseStart_4987350 := by decide
  rcases family_descends (prefixWord ++ tailWord_4987350) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4987386 : List Nat := [3, 1, 1, 1, 1, 2, 2, 3, 2, 3, 4]
def baseStart_4987386 : Nat := 118140960795 + 4987386 * 2 ^ 59
def prefixEnd_4987386 : Nat := 4983230072969 + 3 ^ 40 * 4987386 * 2
def baseEnd_4987386 : Nat := 2560926227504729063038435

theorem tailTrace_4987386 : CollatzResearch.WordTrace tailWord_4987386 prefixEnd_4987386 2560926227504729063038435 := by
  unfold tailWord_4987386
  simp only [CollatzResearch.WordTrace]
  refine ⟨45476227877389943640105503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 121269941006373183040281341 45476227877389943640105503)
  ·
    refine ⟨68214341816084915460158255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45476227877389943640105503 68214341816084915460158255)
    ·
      refine ⟨102321512724127373190237383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68214341816084915460158255 102321512724127373190237383)
      ·
        refine ⟨153482269086191059785356075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 102321512724127373190237383 153482269086191059785356075)
        ·
          refine ⟨230223403629286589678034113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 153482269086191059785356075 230223403629286589678034113)
          ·
            refine ⟨172667552721964942258525585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 230223403629286589678034113 172667552721964942258525585)
            ·
              refine ⟨129500664541473706693894189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 172667552721964942258525585 129500664541473706693894189)
              ·
                refine ⟨48562749203052640010210321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 129500664541473706693894189 48562749203052640010210321)
                ·
                  refine ⟨36422061902289480007657741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 48562749203052640010210321 36422061902289480007657741)
                  ·
                    refine ⟨13658273213358555002871653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 36422061902289480007657741 13658273213358555002871653)
                    ·
                      refine ⟨2560926227504729063038435, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13658273213358555002871653 2560926227504729063038435)
                      ·
                        rfl

theorem cell23_4987386_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 2, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 2, 3, 2, 3, 4].length) (baseStart_4987386 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4987386 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4987386 prefixEnd_4987386 := by exact prefixLift 4987386
  have htrace : WordTrace (prefixWord ++ tailWord_4987386) baseStart_4987386 baseEnd_4987386 := by
    simpa [prefixWord, tailWord_4987386, baseEnd_4987386] using wordTrace_append hprefix tailTrace_4987386
  have hstable : (prefixWord ++ tailWord_4987386).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4987386).length < 2 ^ (prefixWord ++ tailWord_4987386).sum := by decide
  have hdescent : baseEnd_4987386 < baseStart_4987386 := by decide
  rcases family_descends (prefixWord ++ tailWord_4987386) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4987394 : List Nat := [3, 4, 1, 2, 3, 1, 1, 1, 1, 2, 4]
def baseStart_4987394 : Nat := 118140960795 + 4987394 * 2 ^ 59
def prefixEnd_4987394 : Nat := 4983230072969 + 3 ^ 40 * 4987394 * 2
def baseEnd_4987394 : Nat := 2560930335349965031738399

theorem tailTrace_4987394 : CollatzResearch.WordTrace tailWord_4987394 prefixEnd_4987394 2560930335349965031738399 := by
  unfold tailWord_4987394
  simp only [CollatzResearch.WordTrace]
  refine ⟨45476300823382697981678309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 121270135529020527951142157 45476300823382697981678309)
  ·
    refine ⟨8526806404384255871564683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 45476300823382697981678309 8526806404384255871564683)
    ·
      refine ⟨12790209606576383807347025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8526806404384255871564683 12790209606576383807347025)
      ·
        refine ⟨9592657204932287855510269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12790209606576383807347025 9592657204932287855510269)
        ·
          refine ⟨3597246451849607945816351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9592657204932287855510269 3597246451849607945816351)
          ·
            refine ⟨5395869677774411918724527, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3597246451849607945816351 5395869677774411918724527)
            ·
              refine ⟨8093804516661617878086791, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5395869677774411918724527 8093804516661617878086791)
              ·
                refine ⟨12140706774992426817130187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8093804516661617878086791 12140706774992426817130187)
                ·
                  refine ⟨18211060162488640225695281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12140706774992426817130187 18211060162488640225695281)
                  ·
                    refine ⟨13658295121866480169271461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 18211060162488640225695281 13658295121866480169271461)
                    ·
                      refine ⟨2560930335349965031738399, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13658295121866480169271461 2560930335349965031738399)
                      ·
                        rfl

theorem cell23_4987394_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 3, 1, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 3, 1, 1, 1, 1, 2, 4].length) (baseStart_4987394 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4987394 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4987394 prefixEnd_4987394 := by exact prefixLift 4987394
  have htrace : WordTrace (prefixWord ++ tailWord_4987394) baseStart_4987394 baseEnd_4987394 := by
    simpa [prefixWord, tailWord_4987394, baseEnd_4987394] using wordTrace_append hprefix tailTrace_4987394
  have hstable : (prefixWord ++ tailWord_4987394).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4987394).length < 2 ^ (prefixWord ++ tailWord_4987394).sum := by decide
  have hdescent : baseEnd_4987394 < baseStart_4987394 := by decide
  rcases family_descends (prefixWord ++ tailWord_4987394) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4987456 : List Nat := [2, 1, 1, 2, 2, 2, 2, 1, 3, 7]
def baseStart_4987456 : Nat := 118140960795 + 4987456 * 2 ^ 59
def prefixEnd_4987456 : Nat := 4983230072969 + 3 ^ 40 * 4987456 * 2
def baseEnd_4987456 : Nat := 853654057050181263054371

theorem tailTrace_4987456 : CollatzResearch.WordTrace tailWord_4987456 prefixEnd_4987456 853654057050181263054371 := by
  unfold tailWord_4987456
  simp only [CollatzResearch.WordTrace]
  refine ⟨90953732309653088257735111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 121271643079537451010313481 90953732309653088257735111)
  ·
    refine ⟨136430598464479632386602667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90953732309653088257735111 136430598464479632386602667)
    ·
      refine ⟨204645897696719448579904001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 136430598464479632386602667 204645897696719448579904001)
      ·
        refine ⟨153484423272539586434928001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 204645897696719448579904001 153484423272539586434928001)
        ·
          refine ⟨115113317454404689826196001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 153484423272539586434928001 115113317454404689826196001)
          ·
            refine ⟨86334988090803517369647001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 115113317454404689826196001 86334988090803517369647001)
            ·
              refine ⟨64751241068102638027235251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 86334988090803517369647001 64751241068102638027235251)
              ·
                refine ⟨97126861602153957040852877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 64751241068102638027235251 97126861602153957040852877)
                ·
                  refine ⟨36422573100807733890319829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 97126861602153957040852877 36422573100807733890319829)
                  ·
                    refine ⟨853654057050181263054371, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 36422573100807733890319829 853654057050181263054371)
                    ·
                      rfl

theorem cell23_4987456_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 2, 1, 3, 7].length) (baseStart_4987456 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4987456 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4987456 prefixEnd_4987456 := by exact prefixLift 4987456
  have htrace : WordTrace (prefixWord ++ tailWord_4987456) baseStart_4987456 baseEnd_4987456 := by
    simpa [prefixWord, tailWord_4987456, baseEnd_4987456] using wordTrace_append hprefix tailTrace_4987456
  have hstable : (prefixWord ++ tailWord_4987456).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4987456).length < 2 ^ (prefixWord ++ tailWord_4987456).sum := by decide
  have hdescent : baseEnd_4987456 < baseStart_4987456 := by decide
  rcases family_descends (prefixWord ++ tailWord_4987456) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4987473 : List Nat := [1, 2, 2, 1, 3, 3, 1, 3, 2, 5]
def baseStart_4987473 : Nat := 118140960795 + 4987473 * 2 ^ 59
def prefixEnd_4987473 : Nat := 4983230072969 + 3 ^ 40 * 4987473 * 2
def baseEnd_4987473 : Nat := 853656966773890074216845

theorem tailTrace_4987473 : CollatzResearch.WordTrace tailWord_4987473 prefixEnd_4987473 853656966773890074216845 := by
  unfold tailWord_4987473
  simp only [CollatzResearch.WordTrace]
  refine ⟨181908084660244588418839073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121272056440163058945892715 181908084660244588418839073)
  ·
    refine ⟨136431063495183441314129305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 181908084660244588418839073 136431063495183441314129305)
    ·
      refine ⟨102323297621387580985596979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 136431063495183441314129305 102323297621387580985596979)
      ·
        refine ⟨153484946432081371478395469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 102323297621387580985596979 153484946432081371478395469)
        ·
          refine ⟨57556854912030514304398301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 153484946432081371478395469 57556854912030514304398301)
          ·
            refine ⟨21583820592011442864149363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 57556854912030514304398301 21583820592011442864149363)
            ·
              refine ⟨32375730888017164296224045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21583820592011442864149363 32375730888017164296224045)
              ·
                refine ⟨12140899083006436611084017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 32375730888017164296224045 12140899083006436611084017)
                ·
                  refine ⟨9105674312254827458313013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12140899083006436611084017 9105674312254827458313013)
                  ·
                    refine ⟨853656966773890074216845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9105674312254827458313013 853656966773890074216845)
                    ·
                      rfl

theorem cell23_4987473_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 3, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 3, 1, 3, 2, 5].length) (baseStart_4987473 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4987473 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4987473 prefixEnd_4987473 := by exact prefixLift 4987473
  have htrace : WordTrace (prefixWord ++ tailWord_4987473) baseStart_4987473 baseEnd_4987473 := by
    simpa [prefixWord, tailWord_4987473, baseEnd_4987473] using wordTrace_append hprefix tailTrace_4987473
  have hstable : (prefixWord ++ tailWord_4987473).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4987473).length < 2 ^ (prefixWord ++ tailWord_4987473).sum := by decide
  have hdescent : baseEnd_4987473 < baseStart_4987473 := by decide
  rcases family_descends (prefixWord ++ tailWord_4987473) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4987520 : List Nat := [2, 1, 1, 2, 1, 6, 1, 2, 3, 4]
def baseStart_4987520 : Nat := 118140960795 + 4987520 * 2 ^ 59
def prefixEnd_4987520 : Nat := 4983230072969 + 3 ^ 40 * 4987520 * 2
def baseEnd_4987520 : Nat := 853665011304143846254273

theorem tailTrace_4987520 : CollatzResearch.WordTrace tailWord_4987520 prefixEnd_4987520 853665011304143846254273 := by
  unfold tailWord_4987520
  simp only [CollatzResearch.WordTrace]
  refine ⟨90954899445537157722900007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 121273199260716210297200009 90954899445537157722900007)
  ·
    refine ⟨136432349168305736584350011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90954899445537157722900007 136432349168305736584350011)
    ·
      refine ⟨204648523752458604876525017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 136432349168305736584350011 204648523752458604876525017)
      ·
        refine ⟨153486392814343953657393763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 204648523752458604876525017 153486392814343953657393763)
        ·
          refine ⟨230229589221515930486090645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 153486392814343953657393763 230229589221515930486090645)
          ·
            refine ⟨10792011994758559241535499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 230229589221515930486090645 10792011994758559241535499)
            ·
              refine ⟨16188017992137838862303249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10792011994758559241535499 16188017992137838862303249)
              ·
                refine ⟨12141013494103379146727437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16188017992137838862303249 12141013494103379146727437)
                ·
                  refine ⟨4552880060288767180022789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12141013494103379146727437 4552880060288767180022789)
                  ·
                    refine ⟨853665011304143846254273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4552880060288767180022789 853665011304143846254273)
                    ·
                      rfl

theorem cell23_4987520_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 6, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 6, 1, 2, 3, 4].length) (baseStart_4987520 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4987520 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4987520 prefixEnd_4987520 := by exact prefixLift 4987520
  have htrace : WordTrace (prefixWord ++ tailWord_4987520) baseStart_4987520 baseEnd_4987520 := by
    simpa [prefixWord, tailWord_4987520, baseEnd_4987520] using wordTrace_append hprefix tailTrace_4987520
  have hstable : (prefixWord ++ tailWord_4987520).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4987520).length < 2 ^ (prefixWord ++ tailWord_4987520).sum := by decide
  have hdescent : baseEnd_4987520 < baseStart_4987520 := by decide
  rcases family_descends (prefixWord ++ tailWord_4987520) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4987540 : List Nat := [2, 4, 2, 2, 1, 1, 1, 1, 2, 1, 6]
def baseStart_4987540 : Nat := 118140960795 + 4987540 * 2 ^ 59
def prefixEnd_4987540 : Nat := 4983230072969 + 3 ^ 40 * 4987540 * 2
def baseEnd_4987540 : Nat := 2561005303525521460512727

theorem tailTrace_4987540 : CollatzResearch.WordTrace tailWord_4987540 prefixEnd_4987540 2561005303525521460512727 := by
  unfold tailWord_4987540
  simp only [CollatzResearch.WordTrace]
  refine ⟨90955264175500929430764037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 121273685567334572574352049 90955264175500929430764037)
  ·
    refine ⟨17054112032906424268268257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 90955264175500929430764037 17054112032906424268268257)
    ·
      refine ⟨12790584024679818201201193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17054112032906424268268257 12790584024679818201201193)
      ·
        refine ⟨9592938018509863650900895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12790584024679818201201193 9592938018509863650900895)
        ·
          refine ⟨14389407027764795476351343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9592938018509863650900895 14389407027764795476351343)
          ·
            refine ⟨21584110541647193214527015, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14389407027764795476351343 21584110541647193214527015)
            ·
              refine ⟨32376165812470789821790523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21584110541647193214527015 32376165812470789821790523)
              ·
                refine ⟨48564248718706184732685785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32376165812470789821790523 48564248718706184732685785)
                ·
                  refine ⟨36423186539029638549514339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 48564248718706184732685785 36423186539029638549514339)
                  ·
                    refine ⟨54634779808544457824271509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 36423186539029638549514339 54634779808544457824271509)
                    ·
                      refine ⟨2561005303525521460512727, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 54634779808544457824271509 2561005303525521460512727)
                      ·
                        rfl

theorem cell23_4987540_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 1, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 1, 1, 1, 2, 1, 6].length) (baseStart_4987540 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4987540 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4987540 prefixEnd_4987540 := by exact prefixLift 4987540
  have htrace : WordTrace (prefixWord ++ tailWord_4987540) baseStart_4987540 baseEnd_4987540 := by
    simpa [prefixWord, tailWord_4987540, baseEnd_4987540] using wordTrace_append hprefix tailTrace_4987540
  have hstable : (prefixWord ++ tailWord_4987540).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4987540).length < 2 ^ (prefixWord ++ tailWord_4987540).sum := by decide
  have hdescent : baseEnd_4987540 < baseStart_4987540 := by decide
  rcases family_descends (prefixWord ++ tailWord_4987540) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4987550 : List Nat := [4, 3, 1, 1, 1, 1, 3, 1, 8]
def baseStart_4987550 : Nat := 118140960795 + 4987550 * 2 ^ 59
def prefixEnd_4987550 : Nat := 4983230072969 + 3 ^ 40 * 4987550 * 2
def baseEnd_4987550 : Nat := 284556715370229602376409

theorem tailTrace_4987550 : CollatzResearch.WordTrace tailWord_4987550 prefixEnd_4987550 284556715370229602376409 := by
  unfold tailWord_4987550
  simp only [CollatzResearch.WordTrace]
  refine ⟨22738861635120703821174013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 121273928720643753712928069 22738861635120703821174013)
  ·
    refine ⟨8527073113170263932940255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 22738861635120703821174013 8527073113170263932940255)
    ·
      refine ⟨12790609669755395899410383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8527073113170263932940255 12790609669755395899410383)
      ·
        refine ⟨19185914504633093849115575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12790609669755395899410383 19185914504633093849115575)
        ·
          refine ⟨28778871756949640773673363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19185914504633093849115575 28778871756949640773673363)
          ·
            refine ⟨43168307635424461160510045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28778871756949640773673363 43168307635424461160510045)
            ·
              refine ⟨16188115363284172935191267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 43168307635424461160510045 16188115363284172935191267)
              ·
                refine ⟨24282173044926259402786901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16188115363284172935191267 24282173044926259402786901)
                ·
                  refine ⟨284556715370229602376409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 24282173044926259402786901 284556715370229602376409)
                  ·
                    rfl

theorem cell23_4987550_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 3, 1, 8].length) (baseStart_4987550 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4987550 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4987550 prefixEnd_4987550 := by exact prefixLift 4987550
  have htrace : WordTrace (prefixWord ++ tailWord_4987550) baseStart_4987550 baseEnd_4987550 := by
    simpa [prefixWord, tailWord_4987550, baseEnd_4987550] using wordTrace_append hprefix tailTrace_4987550
  have hstable : (prefixWord ++ tailWord_4987550).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4987550).length < 2 ^ (prefixWord ++ tailWord_4987550).sum := by decide
  have hdescent : baseEnd_4987550 < baseStart_4987550 := by decide
  rcases family_descends (prefixWord ++ tailWord_4987550) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4987610 : List Nat := [3, 1, 1, 2, 2, 2, 1, 3, 4, 4]
def baseStart_4987610 : Nat := 118140960795 + 4987610 * 2 ^ 59
def prefixEnd_4987610 : Nat := 4983230072969 + 3 ^ 40 * 4987610 * 2
def baseEnd_4987610 : Nat := 853680415723778728879135

theorem tailTrace_4987610 : CollatzResearch.WordTrace tailWord_4987610 prefixEnd_4987610 853680415723778728879135 := by
  unfold tailWord_4987610
  simp only [CollatzResearch.WordTrace]
  refine ⟨45478270365187065204144071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 121275387640498840544384189 45478270365187065204144071)
  ·
    refine ⟨68217405547780597806216107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45478270365187065204144071 68217405547780597806216107)
    ·
      refine ⟨102326108321670896709324161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68217405547780597806216107 102326108321670896709324161)
      ·
        refine ⟨76744581241253172531993121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 102326108321670896709324161 76744581241253172531993121)
        ·
          refine ⟨57558435930939879398994841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 76744581241253172531993121 57558435930939879398994841)
          ·
            refine ⟨43168826948204909549246131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 57558435930939879398994841 43168826948204909549246131)
            ·
              refine ⟨64753240422307364323869197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 43168826948204909549246131 64753240422307364323869197)
              ·
                refine ⟨24282465158365261621450949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 64753240422307364323869197 24282465158365261621450949)
                ·
                  refine ⟨4552962217193486554022053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 24282465158365261621450949 4552962217193486554022053)
                  ·
                    refine ⟨853680415723778728879135, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4552962217193486554022053 853680415723778728879135)
                    ·
                      rfl

theorem cell23_4987610_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 1, 3, 4, 4].length) (baseStart_4987610 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4987610 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4987610 prefixEnd_4987610 := by exact prefixLift 4987610
  have htrace : WordTrace (prefixWord ++ tailWord_4987610) baseStart_4987610 baseEnd_4987610 := by
    simpa [prefixWord, tailWord_4987610, baseEnd_4987610] using wordTrace_append hprefix tailTrace_4987610
  have hstable : (prefixWord ++ tailWord_4987610).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4987610).length < 2 ^ (prefixWord ++ tailWord_4987610).sum := by decide
  have hdescent : baseEnd_4987610 < baseStart_4987610 := by decide
  rcases family_descends (prefixWord ++ tailWord_4987610) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4987620 : List Nat := [2, 3, 1, 1, 1, 4, 2, 2, 1, 1, 5]
def baseStart_4987620 : Nat := 118140960795 + 4987620 * 2 ^ 59
def prefixEnd_4987620 : Nat := 4983230072969 + 3 ^ 40 * 4987620 * 2
def baseEnd_4987620 : Nat := 2561046381977881147512359

theorem tailTrace_4987620 : CollatzResearch.WordTrace tailWord_4987620 prefixEnd_4987620 2561046381977881147512359 := by
  unfold tailWord_4987620
  simp only [CollatzResearch.WordTrace]
  refine ⟨90956723095356016262220157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 121275630793808021682960209 90956723095356016262220157)
  ·
    refine ⟨34108771160758506098332559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 90956723095356016262220157 34108771160758506098332559)
    ·
      refine ⟨51163156741137759147498839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34108771160758506098332559 51163156741137759147498839)
      ·
        refine ⟨76744735111706638721248259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51163156741137759147498839 76744735111706638721248259)
        ·
          refine ⟨115117102667559958081872389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 76744735111706638721248259 115117102667559958081872389)
          ·
            refine ⟨21584456750167492140351073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 115117102667559958081872389 21584456750167492140351073)
            ·
              refine ⟨16188342562625619105263305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21584456750167492140351073 16188342562625619105263305)
              ·
                refine ⟨12141256921969214328947479, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16188342562625619105263305 12141256921969214328947479)
                ·
                  refine ⟨18211885382953821493421219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12141256921969214328947479 18211885382953821493421219)
                  ·
                    refine ⟨27317828074430732240131829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 18211885382953821493421219 27317828074430732240131829)
                    ·
                      refine ⟨2561046381977881147512359, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 27317828074430732240131829 2561046381977881147512359)
                      ·
                        rfl

theorem cell23_4987620_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 4, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 4, 2, 2, 1, 1, 5].length) (baseStart_4987620 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4987620 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4987620 prefixEnd_4987620 := by exact prefixLift 4987620
  have htrace : WordTrace (prefixWord ++ tailWord_4987620) baseStart_4987620 baseEnd_4987620 := by
    simpa [prefixWord, tailWord_4987620, baseEnd_4987620] using wordTrace_append hprefix tailTrace_4987620
  have hstable : (prefixWord ++ tailWord_4987620).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4987620).length < 2 ^ (prefixWord ++ tailWord_4987620).sum := by decide
  have hdescent : baseEnd_4987620 < baseStart_4987620 := by decide
  rcases family_descends (prefixWord ++ tailWord_4987620) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4987630 : List Nat := [4, 1, 2, 1, 1, 3, 2, 1, 1, 1, 6]
def baseStart_4987630 : Nat := 118140960795 + 4987630 * 2 ^ 59
def prefixEnd_4987630 : Nat := 4983230072969 + 3 ^ 40 * 4987630 * 2
def baseEnd_4987630 : Nat := 2561051516784426108387313

theorem tailTrace_4987630 : CollatzResearch.WordTrace tailWord_4987630 prefixEnd_4987630 2561051516784426108387313 := by
  unfold tailWord_4987630
  simp only [CollatzResearch.WordTrace]
  refine ⟨22739226365084475529038043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 121275873947117202821536229 22739226365084475529038043)
  ·
    refine ⟨34108839547626713293557065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22739226365084475529038043 34108839547626713293557065)
    ·
      refine ⟨25581629660720034970167799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34108839547626713293557065 25581629660720034970167799)
      ·
        refine ⟨38372444491080052455251699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25581629660720034970167799 38372444491080052455251699)
        ·
          refine ⟨57558666736620078682877549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38372444491080052455251699 57558666736620078682877549)
          ·
            refine ⟨21584500026232529506079081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 57558666736620078682877549 21584500026232529506079081)
            ·
              refine ⟨16188375019674397129559311, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21584500026232529506079081 16188375019674397129559311)
              ·
                refine ⟨24282562529511595694338967, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16188375019674397129559311 24282562529511595694338967)
                ·
                  refine ⟨36423843794267393541508451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24282562529511595694338967 36423843794267393541508451)
                  ·
                    refine ⟨54635765691401090312262677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 36423843794267393541508451 54635765691401090312262677)
                    ·
                      refine ⟨2561051516784426108387313, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 54635765691401090312262677 2561051516784426108387313)
                      ·
                        rfl

theorem cell23_4987630_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 3, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 3, 2, 1, 1, 1, 6].length) (baseStart_4987630 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4987630 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4987630 prefixEnd_4987630 := by exact prefixLift 4987630
  have htrace : WordTrace (prefixWord ++ tailWord_4987630) baseStart_4987630 baseEnd_4987630 := by
    simpa [prefixWord, tailWord_4987630, baseEnd_4987630] using wordTrace_append hprefix tailTrace_4987630
  have hstable : (prefixWord ++ tailWord_4987630).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4987630).length < 2 ^ (prefixWord ++ tailWord_4987630).sum := by decide
  have hdescent : baseEnd_4987630 < baseStart_4987630 := by decide
  rcases family_descends (prefixWord ++ tailWord_4987630) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4987634 : List Nat := [3, 2, 1, 3, 1, 4, 1, 2, 1, 1, 4]
def baseStart_4987634 : Nat := 118140960795 + 4987634 * 2 ^ 59
def prefixEnd_4987634 : Nat := 4983230072969 + 3 ^ 40 * 4987634 * 2
def baseEnd_4987634 : Nat := 2561053570707044092737295

theorem tailTrace_4987634 : CollatzResearch.WordTrace tailWord_4987634 prefixEnd_4987634 2561053570707044092737295 := by
  unfold tailWord_4987634
  simp only [CollatzResearch.WordTrace]
  refine ⟨45478489203165328228862489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 121275971208440875276966637 45478489203165328228862489)
  ·
    refine ⟨34108866902373996171646867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45478489203165328228862489 34108866902373996171646867)
    ·
      refine ⟨51163300353560994257470301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34108866902373996171646867 51163300353560994257470301)
      ·
        refine ⟨19186237632585372846551363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 51163300353560994257470301 19186237632585372846551363)
        ·
          refine ⟨28779356448878059269827045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19186237632585372846551363 28779356448878059269827045)
          ·
            refine ⟨5396129334164636113092571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 28779356448878059269827045 5396129334164636113092571)
            ·
              refine ⟨8094194001246954169638857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5396129334164636113092571 8094194001246954169638857)
              ·
                refine ⟨6070645500935215627229143, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8094194001246954169638857 6070645500935215627229143)
                ·
                  refine ⟨9105968251402823440843715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6070645500935215627229143 9105968251402823440843715)
                  ·
                    refine ⟨13658952377104235161265573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9105968251402823440843715 13658952377104235161265573)
                    ·
                      refine ⟨2561053570707044092737295, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13658952377104235161265573 2561053570707044092737295)
                      ·
                        rfl

theorem cell23_4987634_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 4, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 4, 1, 2, 1, 1, 4].length) (baseStart_4987634 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4987634 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4987634 prefixEnd_4987634 := by exact prefixLift 4987634
  have htrace : WordTrace (prefixWord ++ tailWord_4987634) baseStart_4987634 baseEnd_4987634 := by
    simpa [prefixWord, tailWord_4987634, baseEnd_4987634] using wordTrace_append hprefix tailTrace_4987634
  have hstable : (prefixWord ++ tailWord_4987634).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4987634).length < 2 ^ (prefixWord ++ tailWord_4987634).sum := by decide
  have hdescent : baseEnd_4987634 < baseStart_4987634 := by decide
  rcases family_descends (prefixWord ++ tailWord_4987634) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4987653 : List Nat := [1, 3, 1, 1, 2, 1, 1, 2, 4, 7]
def baseStart_4987653 : Nat := 118140960795 + 4987653 * 2 ^ 59
def prefixEnd_4987653 : Nat := 4983230072969 + 3 ^ 40 * 4987653 * 2
def baseEnd_4987653 : Nat := 853687775613159839466569

theorem tailTrace_4987653 : CollatzResearch.WordTrace tailWord_4987653 prefixEnd_4987653 853687775613159839466569 := by
  unfold tailWord_4987653
  simp only [CollatzResearch.WordTrace]
  refine ⟨181914649799592479160391613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121276433199728319440261075 181914649799592479160391613)
  ·
    refine ⟨68217993674847179685146855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 181914649799592479160391613 68217993674847179685146855)
    ·
      refine ⟨102326990512270769527720283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68217993674847179685146855 102326990512270769527720283)
      ·
        refine ⟨153490485768406154291580425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 102326990512270769527720283 153490485768406154291580425)
        ·
          refine ⟨115117864326304615718685319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 153490485768406154291580425 115117864326304615718685319)
          ·
            refine ⟨172676796489456923578027979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 115117864326304615718685319 172676796489456923578027979)
            ·
              refine ⟨259015194734185385367041969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 172676796489456923578027979 259015194734185385367041969)
              ·
                refine ⟨194261396050639039025281477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 259015194734185385367041969 194261396050639039025281477)
                ·
                  refine ⟨36424011759494819817240277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 194261396050639039025281477 36424011759494819817240277)
                  ·
                    refine ⟨853687775613159839466569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 36424011759494819817240277 853687775613159839466569)
                    ·
                      rfl

theorem cell23_4987653_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 1, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 1, 2, 4, 7].length) (baseStart_4987653 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4987653 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4987653 prefixEnd_4987653 := by exact prefixLift 4987653
  have htrace : WordTrace (prefixWord ++ tailWord_4987653) baseStart_4987653 baseEnd_4987653 := by
    simpa [prefixWord, tailWord_4987653, baseEnd_4987653] using wordTrace_append hprefix tailTrace_4987653
  have hstable : (prefixWord ++ tailWord_4987653).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4987653).length < 2 ^ (prefixWord ++ tailWord_4987653).sum := by decide
  have hdescent : baseEnd_4987653 < baseStart_4987653 := by decide
  rcases family_descends (prefixWord ++ tailWord_4987653) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4987684 : List Nat := [2, 3, 1, 3, 3, 1, 2, 1, 1, 3, 3]
def baseStart_4987684 : Nat := 118140960795 + 4987684 * 2 ^ 59
def prefixEnd_4987684 : Nat := 4983230072969 + 3 ^ 40 * 4987684 * 2
def baseEnd_4987684 : Nat := 2561079244739768897112065

theorem tailTrace_4987684 : CollatzResearch.WordTrace tailWord_4987684 prefixEnd_4987684 2561079244739768897112065 := by
  unfold tailWord_4987684
  simp only [CollatzResearch.WordTrace]
  refine ⟨90957890231240085727385053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 121277186974986780969846737 90957890231240085727385053)
  ·
    refine ⟨34109208836715032147769395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 90957890231240085727385053 34109208836715032147769395)
    ·
      refine ⟨51163813255072548221654093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34109208836715032147769395 51163813255072548221654093)
      ·
        refine ⟨19186429970652205583120285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 51163813255072548221654093 19186429970652205583120285)
        ·
          refine ⟨7194911238994577093670107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19186429970652205583120285 7194911238994577093670107)
          ·
            refine ⟨10792366858491865640505161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7194911238994577093670107 10792366858491865640505161)
            ·
              refine ⟨8094275143868899230378871, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10792366858491865640505161 8094275143868899230378871)
              ·
                refine ⟨12141412715803348845568307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8094275143868899230378871 12141412715803348845568307)
                ·
                  refine ⟨18212119073705023268352461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12141412715803348845568307 18212119073705023268352461)
                  ·
                    refine ⟨6829544652639383725632173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 18212119073705023268352461 6829544652639383725632173)
                    ·
                      refine ⟨2561079244739768897112065, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6829544652639383725632173 2561079244739768897112065)
                      ·
                        rfl

theorem cell23_4987684_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 3, 1, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 3, 1, 2, 1, 1, 3, 3].length) (baseStart_4987684 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4987684 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4987684 prefixEnd_4987684 := by exact prefixLift 4987684
  have htrace : WordTrace (prefixWord ++ tailWord_4987684) baseStart_4987684 baseEnd_4987684 := by
    simpa [prefixWord, tailWord_4987684, baseEnd_4987684] using wordTrace_append hprefix tailTrace_4987684
  have hstable : (prefixWord ++ tailWord_4987684).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4987684).length < 2 ^ (prefixWord ++ tailWord_4987684).sum := by decide
  have hdescent : baseEnd_4987684 < baseStart_4987684 := by decide
  rcases family_descends (prefixWord ++ tailWord_4987684) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4987711 : List Nat := [1, 1, 2, 2, 5, 1, 4, 1, 1, 3, 2]
def baseStart_4987711 : Nat := 118140960795 + 4987711 * 2 ^ 59
def prefixEnd_4987711 : Nat := 4983230072969 + 3 ^ 40 * 4987711 * 2
def baseEnd_4987711 : Nat := 2561093108717440291474441

theorem tailTrace_4987711 : CollatzResearch.WordTrace tailWord_4987711 prefixEnd_4987711 2561093108717440291474441 := by
  unfold tailWord_4987711
  simp only [CollatzResearch.WordTrace]
  refine ⟨181916765233382355066002987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121277843488921570044001991 181916765233382355066002987)
  ·
    refine ⟨272875147850073532599004481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 181916765233382355066002987 272875147850073532599004481)
    ·
      refine ⟨204656360887555149449253361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 272875147850073532599004481 204656360887555149449253361)
      ·
        refine ⟨153492270665666362086940021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 204656360887555149449253361 153492270665666362086940021)
        ·
          refine ⟨14389900374906221445650627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 153492270665666362086940021 14389900374906221445650627)
          ·
            refine ⟨21584850562359332168475941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14389900374906221445650627 21584850562359332168475941)
            ·
              refine ⟨4047159480442374781589239, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 21584850562359332168475941 4047159480442374781589239)
              ·
                refine ⟨6070739220663562172383859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4047159480442374781589239 6070739220663562172383859)
                ·
                  refine ⟨9106108830995343258575789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6070739220663562172383859 9106108830995343258575789)
                  ·
                    refine ⟨3414790811623253721965921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9106108830995343258575789 3414790811623253721965921)
                    ·
                      refine ⟨2561093108717440291474441, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3414790811623253721965921 2561093108717440291474441)
                      ·
                        rfl

theorem cell23_4987711_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 1, 4, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 1, 4, 1, 1, 3, 2].length) (baseStart_4987711 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4987711 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4987711 prefixEnd_4987711 := by exact prefixLift 4987711
  have htrace : WordTrace (prefixWord ++ tailWord_4987711) baseStart_4987711 baseEnd_4987711 := by
    simpa [prefixWord, tailWord_4987711, baseEnd_4987711] using wordTrace_append hprefix tailTrace_4987711
  have hstable : (prefixWord ++ tailWord_4987711).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4987711).length < 2 ^ (prefixWord ++ tailWord_4987711).sum := by decide
  have hdescent : baseEnd_4987711 < baseStart_4987711 := by decide
  rcases family_descends (prefixWord ++ tailWord_4987711) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4987718 : List Nat := [6, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3]
def baseStart_4987718 : Nat := 118140960795 + 4987718 * 2 ^ 59
def prefixEnd_4987718 : Nat := 4983230072969 + 3 ^ 40 * 4987718 * 2
def baseEnd_4987718 : Nat := 2561096703082021764086909

theorem tailTrace_4987718 : CollatzResearch.WordTrace tailWord_4987718 prefixEnd_4987718 2561096703082021764086909 := by
  unfold tailWord_4987718
  simp only [CollatzResearch.WordTrace]
  refine ⟨5684906892011156101922119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 121278013696237996841005205 5684906892011156101922119)
  ·
    refine ⟨8527360338016734152883179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5684906892011156101922119 8527360338016734152883179)
    ·
      refine ⟨12791040507025101229324769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8527360338016734152883179 12791040507025101229324769)
      ·
        refine ⟨9593280380268825921993577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12791040507025101229324769 9593280380268825921993577)
        ·
          refine ⟨7194960285201619441495183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9593280380268825921993577 7194960285201619441495183)
          ·
            refine ⟨10792440427802429162242775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7194960285201619441495183 10792440427802429162242775)
            ·
              refine ⟨16188660641703643743364163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10792440427802429162242775 16188660641703643743364163)
              ·
                refine ⟨24282990962555465615046245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16188660641703643743364163 24282990962555465615046245)
                ·
                  refine ⟨4553060805479149802821171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 24282990962555465615046245 4553060805479149802821171)
                  ·
                    refine ⟨6829591208218724704231757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4553060805479149802821171 6829591208218724704231757)
                    ·
                      refine ⟨2561096703082021764086909, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6829591208218724704231757 2561096703082021764086909)
                      ·
                        rfl

theorem cell23_4987718_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3].length) (baseStart_4987718 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4987718 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4987718 prefixEnd_4987718 := by exact prefixLift 4987718
  have htrace : WordTrace (prefixWord ++ tailWord_4987718) baseStart_4987718 baseEnd_4987718 := by
    simpa [prefixWord, tailWord_4987718, baseEnd_4987718] using wordTrace_append hprefix tailTrace_4987718
  have hstable : (prefixWord ++ tailWord_4987718).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4987718).length < 2 ^ (prefixWord ++ tailWord_4987718).sum := by decide
  have hdescent : baseEnd_4987718 < baseStart_4987718 := by decide
  rcases family_descends (prefixWord ++ tailWord_4987718) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4987720 : List Nat := [2, 1, 3, 1, 1, 3, 1, 1, 4, 2, 4]
def baseStart_4987720 : Nat := 118140960795 + 4987720 * 2 ^ 59
def prefixEnd_4987720 : Nat := 4983230072969 + 3 ^ 40 * 4987720 * 2
def baseEnd_4987720 : Nat := 2561097730043330756261899

theorem tailTrace_4987720 : CollatzResearch.WordTrace tailWord_4987720 prefixEnd_4987720 2561097730043330756261899 := by
  unfold tailWord_4987720
  simp only [CollatzResearch.WordTrace]
  refine ⟨90958546745174874801540307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 121278062326899833068720409 90958546745174874801540307)
  ·
    refine ⟨136437820117762312202310461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90958546745174874801540307 136437820117762312202310461)
    ·
      refine ⟨51164182544160867075866423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 136437820117762312202310461 51164182544160867075866423)
      ·
        refine ⟨76746273816241300613799635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51164182544160867075866423 76746273816241300613799635)
        ·
          refine ⟨115119410724361950920699453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 76746273816241300613799635 115119410724361950920699453)
          ·
            refine ⟨43169779021635731595262295, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 115119410724361950920699453 43169779021635731595262295)
            ·
              refine ⟨64754668532453597392893443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 43169779021635731595262295 64754668532453597392893443)
              ·
                refine ⟨97132002798680396089340165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 64754668532453597392893443 97132002798680396089340165)
                ·
                  refine ⟨18212250524752574266751281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 97132002798680396089340165 18212250524752574266751281)
                  ·
                    refine ⟨13659187893564430700063461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 18212250524752574266751281 13659187893564430700063461)
                    ·
                      refine ⟨2561097730043330756261899, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13659187893564430700063461 2561097730043330756261899)
                      ·
                        rfl

theorem cell23_4987720_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 1, 1, 4, 2, 4].length) (baseStart_4987720 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4987720 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4987720 prefixEnd_4987720 := by exact prefixLift 4987720
  have htrace : WordTrace (prefixWord ++ tailWord_4987720) baseStart_4987720 baseEnd_4987720 := by
    simpa [prefixWord, tailWord_4987720, baseEnd_4987720] using wordTrace_append hprefix tailTrace_4987720
  have hstable : (prefixWord ++ tailWord_4987720).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4987720).length < 2 ^ (prefixWord ++ tailWord_4987720).sum := by decide
  have hdescent : baseEnd_4987720 < baseStart_4987720 := by decide
  rcases family_descends (prefixWord ++ tailWord_4987720) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4987760 : List Nat := [2, 1, 1, 1, 4, 1, 4, 1, 1, 7]
def baseStart_4987760 : Nat := 118140960795 + 4987760 * 2 ^ 59
def prefixEnd_4987760 : Nat := 4983230072969 + 3 ^ 40 * 4987760 * 2
def baseEnd_4987760 : Nat := 853706089756503533253905

theorem tailTrace_4987760 : CollatzResearch.WordTrace tailWord_4987760 prefixEnd_4987760 853706089756503533253905 := by
  unfold tailWord_4987760
  simp only [CollatzResearch.WordTrace]
  refine ⟨90959276205102418217268367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 121279034940136557623024489 90959276205102418217268367)
  ·
    refine ⟨136438914307653627325902551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90959276205102418217268367 136438914307653627325902551)
    ·
      refine ⟨204658371461480440988853827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 136438914307653627325902551 204658371461480440988853827)
      ·
        refine ⟨306987557192220661483280741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 204658371461480440988853827 306987557192220661483280741)
        ·
          refine ⟨57560166973541374028115139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 306987557192220661483280741 57560166973541374028115139)
          ·
            refine ⟨86340250460312061042172709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 57560166973541374028115139 86340250460312061042172709)
            ·
              refine ⟨16188796961308511445407383, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 86340250460312061042172709 16188796961308511445407383)
              ·
                refine ⟨24283195441962767168111075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16188796961308511445407383 24283195441962767168111075)
                ·
                  refine ⟨36424793162944150752166613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24283195441962767168111075 36424793162944150752166613)
                  ·
                    refine ⟨853706089756503533253905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 36424793162944150752166613 853706089756503533253905)
                    ·
                      rfl

theorem cell23_4987760_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 4, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 4, 1, 1, 7].length) (baseStart_4987760 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4987760 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4987760 prefixEnd_4987760 := by exact prefixLift 4987760
  have htrace : WordTrace (prefixWord ++ tailWord_4987760) baseStart_4987760 baseEnd_4987760 := by
    simpa [prefixWord, tailWord_4987760, baseEnd_4987760] using wordTrace_append hprefix tailTrace_4987760
  have hstable : (prefixWord ++ tailWord_4987760).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4987760).length < 2 ^ (prefixWord ++ tailWord_4987760).sum := by decide
  have hdescent : baseEnd_4987760 < baseStart_4987760 := by decide
  rcases family_descends (prefixWord ++ tailWord_4987760) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4987770 : List Nat := [3, 1, 1, 1, 1, 1, 3, 4, 1, 2, 5]
def baseStart_4987770 : Nat := 118140960795 + 4987770 * 2 ^ 59
def prefixEnd_4987770 : Nat := 4983230072969 + 3 ^ 40 * 4987770 * 2
def baseEnd_4987770 : Nat := 2561123404076055560636669

theorem tailTrace_4987770 : CollatzResearch.WordTrace tailWord_4987770 prefixEnd_4987770 2561123404076055560636669 := by
  unfold tailWord_4987770
  simp only [CollatzResearch.WordTrace]
  refine ⟨45479729285042152035600191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 121279278093445738761600509 45479729285042152035600191)
  ·
    refine ⟨68219593927563228053400287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45479729285042152035600191 68219593927563228053400287)
    ·
      refine ⟨102329390891344842080100431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68219593927563228053400287 102329390891344842080100431)
      ·
        refine ⟨153494086337017263120150647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 102329390891344842080100431 153494086337017263120150647)
        ·
          refine ⟨230241129505525894680225971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 153494086337017263120150647 230241129505525894680225971)
          ·
            refine ⟨345361694258288842020338957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 230241129505525894680225971 345361694258288842020338957)
            ·
              refine ⟨129510635346858315757627109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 345361694258288842020338957 129510635346858315757627109)
              ·
                refine ⟨24283244127535934204555083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 129510635346858315757627109 24283244127535934204555083)
                ·
                  refine ⟨36424866191303901306832625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24283244127535934204555083 36424866191303901306832625)
                  ·
                    refine ⟨27318649643477925980124469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 36424866191303901306832625 27318649643477925980124469)
                    ·
                      refine ⟨2561123404076055560636669, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 27318649643477925980124469 2561123404076055560636669)
                      ·
                        rfl

theorem cell23_4987770_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 3, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 3, 4, 1, 2, 5].length) (baseStart_4987770 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4987770 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4987770 prefixEnd_4987770 := by exact prefixLift 4987770
  have htrace : WordTrace (prefixWord ++ tailWord_4987770) baseStart_4987770 baseEnd_4987770 := by
    simpa [prefixWord, tailWord_4987770, baseEnd_4987770] using wordTrace_append hprefix tailTrace_4987770
  have hstable : (prefixWord ++ tailWord_4987770).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4987770).length < 2 ^ (prefixWord ++ tailWord_4987770).sum := by decide
  have hdescent : baseEnd_4987770 < baseStart_4987770 := by decide
  rcases family_descends (prefixWord ++ tailWord_4987770) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4987864 : List Nat := [2, 1, 2, 2, 2, 3, 1, 1, 5, 1, 3]
def baseStart_4987864 : Nat := 118140960795 + 4987864 * 2 ^ 59
def prefixEnd_4987864 : Nat := 4983230072969 + 3 ^ 40 * 4987864 * 2
def baseEnd_4987864 : Nat := 2561171671257578192861237

theorem tailTrace_4987864 : CollatzResearch.WordTrace tailWord_4987864 prefixEnd_4987864 2561171671257578192861237 := by
  unfold tailWord_4987864
  simp only [CollatzResearch.WordTrace]
  refine ⟨90961172800914031098161323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 121281563734552041464215097 90961172800914031098161323)
  ·
    refine ⟨136441759201371046647241985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90961172800914031098161323 136441759201371046647241985)
    ·
      refine ⟨102331319401028284985431489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 136441759201371046647241985 102331319401028284985431489)
      ·
        refine ⟨76748489550771213739073617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 102331319401028284985431489 76748489550771213739073617)
        ·
          refine ⟨57561367163078410304305213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 76748489550771213739073617 57561367163078410304305213)
          ·
            refine ⟨21585512686154403864114455, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 57561367163078410304305213 21585512686154403864114455)
            ·
              refine ⟨32378269029231605796171683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21585512686154403864114455 32378269029231605796171683)
              ·
                refine ⟨48567403543847408694257525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32378269029231605796171683 48567403543847408694257525)
                ·
                  refine ⟨4553194082235694565086643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 48567403543847408694257525 4553194082235694565086643)
                  ·
                    refine ⟨6829791123353541847629965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4553194082235694565086643 6829791123353541847629965)
                    ·
                      refine ⟨2561171671257578192861237, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6829791123353541847629965 2561171671257578192861237)
                      ·
                        rfl

theorem cell23_4987864_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 3, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 3, 1, 1, 5, 1, 3].length) (baseStart_4987864 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4987864 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4987864 prefixEnd_4987864 := by exact prefixLift 4987864
  have htrace : WordTrace (prefixWord ++ tailWord_4987864) baseStart_4987864 baseEnd_4987864 := by
    simpa [prefixWord, tailWord_4987864, baseEnd_4987864] using wordTrace_append hprefix tailTrace_4987864
  have hstable : (prefixWord ++ tailWord_4987864).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4987864).length < 2 ^ (prefixWord ++ tailWord_4987864).sum := by decide
  have hdescent : baseEnd_4987864 < baseStart_4987864 := by decide
  rcases family_descends (prefixWord ++ tailWord_4987864) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4987892 : List Nat := [2, 6, 2, 1, 1, 1, 2, 1, 3, 4]
def baseStart_4987892 : Nat := 118140960795 + 4987892 * 2 ^ 59
def prefixEnd_4987892 : Nat := 4983230072969 + 3 ^ 40 * 4987892 * 2
def baseEnd_4987892 : Nat := 853728682905301361103703

theorem tailTrace_4987892 : CollatzResearch.WordTrace tailWord_4987892 prefixEnd_4987892 853728682905301361103703 := by
  unfold tailWord_4987892
  simp only [CollatzResearch.WordTrace]
  refine ⟨90961683422863311489170965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 121282244563817748652227953 90961683422863311489170965)
  ·
    refine ⟨4263828910446717726054889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 90961683422863311489170965 4263828910446717726054889)
    ·
      refine ⟨3197871682835038294541167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4263828910446717726054889 3197871682835038294541167)
      ·
        refine ⟨4796807524252557441811751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3197871682835038294541167 4796807524252557441811751)
        ·
          refine ⟨7195211286378836162717627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4796807524252557441811751 7195211286378836162717627)
          ·
            refine ⟨10792816929568254244076441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7195211286378836162717627 10792816929568254244076441)
            ·
              refine ⟨8094612697176190683057331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10792816929568254244076441 8094612697176190683057331)
              ·
                refine ⟨12141919045764286024585997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8094612697176190683057331 12141919045764286024585997)
                ·
                  refine ⟨4553219642161607259219749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12141919045764286024585997 4553219642161607259219749)
                  ·
                    refine ⟨853728682905301361103703, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4553219642161607259219749 853728682905301361103703)
                    ·
                      rfl

theorem cell23_4987892_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 2, 1, 1, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 2, 1, 1, 1, 2, 1, 3, 4].length) (baseStart_4987892 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4987892 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4987892 prefixEnd_4987892 := by exact prefixLift 4987892
  have htrace : WordTrace (prefixWord ++ tailWord_4987892) baseStart_4987892 baseEnd_4987892 := by
    simpa [prefixWord, tailWord_4987892, baseEnd_4987892] using wordTrace_append hprefix tailTrace_4987892
  have hstable : (prefixWord ++ tailWord_4987892).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4987892).length < 2 ^ (prefixWord ++ tailWord_4987892).sum := by decide
  have hdescent : baseEnd_4987892 < baseStart_4987892 := by decide
  rcases family_descends (prefixWord ++ tailWord_4987892) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4987914 : List Nat := [3, 1, 2, 2, 3, 1, 3, 1, 1, 6]
def baseStart_4987914 : Nat := 118140960795 + 4987914 * 2 ^ 59
def prefixEnd_4987914 : Nat := 4983230072969 + 3 ^ 40 * 4987914 * 2
def baseEnd_4987914 : Nat := 853732448430100999078669

theorem tailTrace_4987914 : CollatzResearch.WordTrace tailWord_4987914 prefixEnd_4987914 853732448430100999078669 := by
  unfold tailWord_4987914
  simp only [CollatzResearch.WordTrace]
  refine ⟨45481042312911730183910699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 121282779501097947157095197 45481042312911730183910699)
  ·
    refine ⟨68221563469367595275866049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45481042312911730183910699 68221563469367595275866049)
    ·
      refine ⟨51166172602025696456899537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 68221563469367595275866049 51166172602025696456899537)
      ·
        refine ⟨38374629451519272342674653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 51166172602025696456899537 38374629451519272342674653)
        ·
          refine ⟨14390486044319727128502995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 38374629451519272342674653 14390486044319727128502995)
          ·
            refine ⟨21585729066479590692754493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14390486044319727128502995 21585729066479590692754493)
            ·
              refine ⟨8094648399929846509782935, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21585729066479590692754493 8094648399929846509782935)
              ·
                refine ⟨12141972599894769764674403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8094648399929846509782935 12141972599894769764674403)
                ·
                  refine ⟨18212958899842154647011605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12141972599894769764674403 18212958899842154647011605)
                  ·
                    refine ⟨853732448430100999078669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 18212958899842154647011605 853732448430100999078669)
                    ·
                      rfl

theorem cell23_4987914_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 1, 3, 1, 1, 6].length) (baseStart_4987914 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4987914 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4987914 prefixEnd_4987914 := by exact prefixLift 4987914
  have htrace : WordTrace (prefixWord ++ tailWord_4987914) baseStart_4987914 baseEnd_4987914 := by
    simpa [prefixWord, tailWord_4987914, baseEnd_4987914] using wordTrace_append hprefix tailTrace_4987914
  have hstable : (prefixWord ++ tailWord_4987914).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4987914).length < 2 ^ (prefixWord ++ tailWord_4987914).sum := by decide
  have hdescent : baseEnd_4987914 < baseStart_4987914 := by decide
  rcases family_descends (prefixWord ++ tailWord_4987914) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4987932 : List Nat := [2, 2, 3, 1, 5, 1, 1, 3, 1, 1, 3]
def baseStart_4987932 : Nat := 118140960795 + 4987932 * 2 ^ 59
def prefixEnd_4987932 : Nat := 4983230072969 + 3 ^ 40 * 4987932 * 2
def baseEnd_4987932 : Nat := 2561206587942083926810925

theorem tailTrace_4987932 : CollatzResearch.WordTrace tailWord_4987932 prefixEnd_4987932 2561206587942083926810925 := by
  unfold tailWord_4987932
  simp only [CollatzResearch.WordTrace]
  refine ⟨90962412882790854904899025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 121283217177054473206532033 90962412882790854904899025)
  ·
    refine ⟨68221809662093141178674269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 90962412882790854904899025 68221809662093141178674269)
    ·
      refine ⟨25583178623284927942002851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 68221809662093141178674269 25583178623284927942002851)
      ·
        refine ⟨38374767934927391913004277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25583178623284927942002851 38374767934927391913004277)
        ·
          refine ⟨3597634493899442991844151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 38374767934927391913004277 3597634493899442991844151)
          ·
            refine ⟨5396451740849164487766227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3597634493899442991844151 5396451740849164487766227)
            ·
              refine ⟨8094677611273746731649341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5396451740849164487766227 8094677611273746731649341)
              ·
                refine ⟨3035504104227655024368503, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8094677611273746731649341 3035504104227655024368503)
                ·
                  refine ⟨4553256156341482536552755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3035504104227655024368503 4553256156341482536552755)
                  ·
                    refine ⟨6829884234512223804829133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4553256156341482536552755 6829884234512223804829133)
                    ·
                      refine ⟨2561206587942083926810925, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6829884234512223804829133 2561206587942083926810925)
                      ·
                        rfl

theorem cell23_4987932_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 5, 1, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 5, 1, 1, 3, 1, 1, 3].length) (baseStart_4987932 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4987932 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4987932 prefixEnd_4987932 := by exact prefixLift 4987932
  have htrace : WordTrace (prefixWord ++ tailWord_4987932) baseStart_4987932 baseEnd_4987932 := by
    simpa [prefixWord, tailWord_4987932, baseEnd_4987932] using wordTrace_append hprefix tailTrace_4987932
  have hstable : (prefixWord ++ tailWord_4987932).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4987932).length < 2 ^ (prefixWord ++ tailWord_4987932).sum := by decide
  have hdescent : baseEnd_4987932 < baseStart_4987932 := by decide
  rcases family_descends (prefixWord ++ tailWord_4987932) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4987957 : List Nat := [1, 3, 3, 1, 1, 1, 1, 3, 2, 7]
def baseStart_4987957 : Nat := 118140960795 + 4987957 * 2 ^ 59
def prefixEnd_4987957 : Nat := 4983230072969 + 3 ^ 40 * 4987957 * 2
def baseEnd_4987957 : Nat := 853739808319482109666103

theorem tailTrace_4987957 : CollatzResearch.WordTrace tailWord_4987957 prefixEnd_4987957 853739808319482109666103 := by
  unfold tailWord_4987957
  simp only [CollatzResearch.WordTrace]
  refine ⟨181925737590491139079458125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121283825060327426052972083 181925737590491139079458125)
  ·
    refine ⟨68222151596434177154796797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 181925737590491139079458125 68222151596434177154796797)
    ·
      refine ⟨25583306848662816433048799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 68222151596434177154796797 25583306848662816433048799)
      ·
        refine ⟨38374960272994224649573199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25583306848662816433048799 38374960272994224649573199)
        ·
          refine ⟨57562440409491336974359799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38374960272994224649573199 57562440409491336974359799)
          ·
            refine ⟨86343660614237005461539699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 57562440409491336974359799 86343660614237005461539699)
            ·
              refine ⟨129515490921355508192309549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 86343660614237005461539699 129515490921355508192309549)
              ·
                refine ⟨48568309095508315572116081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 129515490921355508192309549 48568309095508315572116081)
                ·
                  refine ⟨36426231821631236679087061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 48568309095508315572116081 36426231821631236679087061)
                  ·
                    refine ⟨853739808319482109666103, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 36426231821631236679087061 853739808319482109666103)
                    ·
                      rfl

theorem cell23_4987957_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 1, 3, 2, 7].length) (baseStart_4987957 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4987957 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4987957 prefixEnd_4987957 := by exact prefixLift 4987957
  have htrace : WordTrace (prefixWord ++ tailWord_4987957) baseStart_4987957 baseEnd_4987957 := by
    simpa [prefixWord, tailWord_4987957, baseEnd_4987957] using wordTrace_append hprefix tailTrace_4987957
  have hstable : (prefixWord ++ tailWord_4987957).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4987957).length < 2 ^ (prefixWord ++ tailWord_4987957).sum := by decide
  have hdescent : baseEnd_4987957 < baseStart_4987957 := by decide
  rcases family_descends (prefixWord ++ tailWord_4987957) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4987971 : List Nat := [1, 1, 1, 3, 1, 2, 5, 3, 2, 1, 3]
def baseStart_4987971 : Nat := 118140960795 + 4987971 * 2 ^ 59
def prefixEnd_4987971 : Nat := 4983230072969 + 3 ^ 40 * 4987971 * 2
def baseEnd_4987971 : Nat := 2561226613687609274223245

theorem tailTrace_4987971 : CollatzResearch.WordTrace tailWord_4987971 prefixEnd_4987971 2561226613687609274223245 := by
  unfold tailWord_4987971
  simp only [CollatzResearch.WordTrace]
  refine ⟨181926248212440419470467767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121284165474960279646978511 181926248212440419470467767)
  ·
    refine ⟨272889372318660629205701651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 181926248212440419470467767 272889372318660629205701651)
    ·
      refine ⟨409334058477990943808552477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 272889372318660629205701651 409334058477990943808552477)
      ·
        refine ⟨153500271929246603928207179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 409334058477990943808552477 153500271929246603928207179)
        ·
          refine ⟨230250407893869905892310769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 153500271929246603928207179 230250407893869905892310769)
          ·
            refine ⟨172687805920402429419233077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 230250407893869905892310769 172687805920402429419233077)
            ·
              refine ⟨16189481805037727758053101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 172687805920402429419233077 16189481805037727758053101)
              ·
                refine ⟨6071055676889147909269913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16189481805037727758053101 6071055676889147909269913)
                ·
                  refine ⟨4553291757666860931952435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6071055676889147909269913 4553291757666860931952435)
                  ·
                    refine ⟨6829937636500291397928653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4553291757666860931952435 6829937636500291397928653)
                    ·
                      refine ⟨2561226613687609274223245, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6829937636500291397928653 2561226613687609274223245)
                      ·
                        rfl

theorem cell23_4987971_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 5, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 5, 3, 2, 1, 3].length) (baseStart_4987971 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4987971 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4987971 prefixEnd_4987971 := by exact prefixLift 4987971
  have htrace : WordTrace (prefixWord ++ tailWord_4987971) baseStart_4987971 baseEnd_4987971 := by
    simpa [prefixWord, tailWord_4987971, baseEnd_4987971] using wordTrace_append hprefix tailTrace_4987971
  have hstable : (prefixWord ++ tailWord_4987971).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4987971).length < 2 ^ (prefixWord ++ tailWord_4987971).sum := by decide
  have hdescent : baseEnd_4987971 < baseStart_4987971 := by decide
  rcases family_descends (prefixWord ++ tailWord_4987971) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4987977 : List Nat := [1, 2, 1, 1, 2, 2, 2, 1, 4, 3, 4]
def baseStart_4987977 : Nat := 118140960795 + 4987977 * 2 ^ 59
def prefixEnd_4987977 : Nat := 4983230072969 + 3 ^ 40 * 4987977 * 2
def baseEnd_4987977 : Nat := 2561229694571536250748217

theorem tailTrace_4987977 : CollatzResearch.WordTrace tailWord_4987977 prefixEnd_4987977 2561229694571536250748217 := by
  unfold tailWord_4987977
  simp only [CollatzResearch.WordTrace]
  refine ⟨181926467050418682495186185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121284311366945788330124123 181926467050418682495186185)
  ·
    refine ⟨136444850287814011871389639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 181926467050418682495186185 136444850287814011871389639)
    ·
      refine ⟨204667275431721017807084459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 136444850287814011871389639 204667275431721017807084459)
      ·
        refine ⟨307000913147581526710626689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 204667275431721017807084459 307000913147581526710626689)
        ·
          refine ⟨230250684860686145032970017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 307000913147581526710626689 230250684860686145032970017)
          ·
            refine ⟨172688013645514608774727513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 230250684860686145032970017 172688013645514608774727513)
            ·
              refine ⟨129516010234135956581045635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 172688013645514608774727513 129516010234135956581045635)
              ·
                refine ⟨194274015351203934871568453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 129516010234135956581045635 194274015351203934871568453)
                ·
                  refine ⟨36426377878350737788419085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 194274015351203934871568453 36426377878350737788419085)
                  ·
                    refine ⟨13659891704381526670657157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 36426377878350737788419085 13659891704381526670657157)
                    ·
                      refine ⟨2561229694571536250748217, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13659891704381526670657157 2561229694571536250748217)
                      ·
                        rfl

theorem cell23_4987977_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 2, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 2, 1, 4, 3, 4].length) (baseStart_4987977 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4987977 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4987977 prefixEnd_4987977 := by exact prefixLift 4987977
  have htrace : WordTrace (prefixWord ++ tailWord_4987977) baseStart_4987977 baseEnd_4987977 := by
    simpa [prefixWord, tailWord_4987977, baseEnd_4987977] using wordTrace_append hprefix tailTrace_4987977
  have hstable : (prefixWord ++ tailWord_4987977).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4987977).length < 2 ^ (prefixWord ++ tailWord_4987977).sum := by decide
  have hdescent : baseEnd_4987977 < baseStart_4987977 := by decide
  rcases family_descends (prefixWord ++ tailWord_4987977) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4988028 : List Nat := [2, 2, 2, 1, 1, 3, 1, 5, 2, 2, 2]
def baseStart_4988028 : Nat := 118140960795 + 4988028 * 2 ^ 59
def prefixEnd_4988028 : Nat := 4983230072969 + 3 ^ 40 * 4988028 * 2
def baseEnd_4988028 : Nat := 2561255882084915551210483

theorem tailTrace_4988028 : CollatzResearch.WordTrace tailWord_4988028 prefixEnd_4988028 2561255882084915551210483 := by
  unfold tailWord_4988028
  simp only [CollatzResearch.WordTrace]
  refine ⟨90964163586616959102646369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 121285551448822612136861825 90964163586616959102646369)
  ·
    refine ⟨68223122689962719326984777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 90964163586616959102646369 68223122689962719326984777)
    ·
      refine ⟨51167342017472039495238583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 68223122689962719326984777 51167342017472039495238583)
      ·
        refine ⟨76751013026208059242857875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51167342017472039495238583 76751013026208059242857875)
        ·
          refine ⟨115126519539312088864286813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 76751013026208059242857875 115126519539312088864286813)
          ·
            refine ⟨43172444827242033324107555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 115126519539312088864286813 43172444827242033324107555)
            ·
              refine ⟨64758667240863049986161333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 43172444827242033324107555 64758667240863049986161333)
              ·
                refine ⟨6071125053830910936202625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 64758667240863049986161333 6071125053830910936202625)
                ·
                  refine ⟨4553343790373183202151969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6071125053830910936202625 4553343790373183202151969)
                  ·
                    refine ⟨3415007842779887401613977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4553343790373183202151969 3415007842779887401613977)
                    ·
                      refine ⟨2561255882084915551210483, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3415007842779887401613977 2561255882084915551210483)
                      ·
                        rfl

theorem cell23_4988028_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 1, 5, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 1, 5, 2, 2, 2].length) (baseStart_4988028 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4988028 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4988028 prefixEnd_4988028 := by exact prefixLift 4988028
  have htrace : WordTrace (prefixWord ++ tailWord_4988028) baseStart_4988028 baseEnd_4988028 := by
    simpa [prefixWord, tailWord_4988028, baseEnd_4988028] using wordTrace_append hprefix tailTrace_4988028
  have hstable : (prefixWord ++ tailWord_4988028).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4988028).length < 2 ^ (prefixWord ++ tailWord_4988028).sum := by decide
  have hdescent : baseEnd_4988028 < baseStart_4988028 := by decide
  rcases family_descends (prefixWord ++ tailWord_4988028) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4988062 : List Nat := [4, 3, 1, 1, 2, 1, 3, 2, 2, 2, 2]
def baseStart_4988062 : Nat := 118140960795 + 4988062 * 2 ^ 59
def prefixEnd_4988062 : Nat := 4983230072969 + 3 ^ 40 * 4988062 * 2
def baseEnd_4988062 : Nat := 2561273340427168418185327

theorem tailTrace_4988062 : CollatzResearch.WordTrace tailWord_4988062 prefixEnd_4988062 2561273340427168418185327 := by
  unfold tailWord_4988062
  simp only [CollatzResearch.WordTrace]
  refine ⟨22741195906888842751503805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 121286378170073828008020293 22741195906888842751503805)
  ·
    refine ⟨8527948465083316031813927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 22741195906888842751503805 8527948465083316031813927)
    ·
      refine ⟨12791922697624974047720891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8527948465083316031813927 12791922697624974047720891)
      ·
        refine ⟨19187884046437461071581337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12791922697624974047720891 19187884046437461071581337)
        ·
          refine ⟨14390913034828095803686003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19187884046437461071581337 14390913034828095803686003)
          ·
            refine ⟨21586369552242143705529005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14390913034828095803686003 21586369552242143705529005)
            ·
              refine ⟨8094888582090803889573377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21586369552242143705529005 8094888582090803889573377)
              ·
                refine ⟨6071166436568102917180033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8094888582090803889573377 6071166436568102917180033)
                ·
                  refine ⟨4553374827426077187885025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6071166436568102917180033 4553374827426077187885025)
                  ·
                    refine ⟨3415031120569557890913769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4553374827426077187885025 3415031120569557890913769)
                    ·
                      refine ⟨2561273340427168418185327, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3415031120569557890913769 2561273340427168418185327)
                      ·
                        rfl

theorem cell23_4988062_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 1, 3, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 1, 3, 2, 2, 2, 2].length) (baseStart_4988062 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4988062 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4988062 prefixEnd_4988062 := by exact prefixLift 4988062
  have htrace : WordTrace (prefixWord ++ tailWord_4988062) baseStart_4988062 baseEnd_4988062 := by
    simpa [prefixWord, tailWord_4988062, baseEnd_4988062] using wordTrace_append hprefix tailTrace_4988062
  have hstable : (prefixWord ++ tailWord_4988062).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4988062).length < 2 ^ (prefixWord ++ tailWord_4988062).sum := by decide
  have hdescent : baseEnd_4988062 < baseStart_4988062 := by decide
  rcases family_descends (prefixWord ++ tailWord_4988062) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4988064 : List Nat := [2, 1, 1, 4, 2, 1, 2, 1, 4, 5]
def baseStart_4988064 : Nat := 118140960795 + 4988064 * 2 ^ 59
def prefixEnd_4988064 : Nat := 4983230072969 + 3 ^ 40 * 4988064 * 2
def baseEnd_4988064 : Nat := 853758122462825803453439

theorem tailTrace_4988064 : CollatzResearch.WordTrace tailWord_4988064 prefixEnd_4988064 853758122462825803453439 := by
  unfold tailWord_4988064
  simp only [CollatzResearch.WordTrace]
  refine ⟨90964820100551748176801623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 121286426800735664235735497 90964820100551748176801623)
  ·
    refine ⟨136447230150827622265202435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90964820100551748176801623 136447230150827622265202435)
    ·
      refine ⟨204670845226241433397803653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 136447230150827622265202435 204670845226241433397803653)
      ·
        refine ⟨38375783479920268762088185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 204670845226241433397803653 38375783479920268762088185)
        ·
          refine ⟨28781837609940201571566139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38375783479920268762088185 28781837609940201571566139)
          ·
            refine ⟨43172756414910302357349209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28781837609940201571566139 43172756414910302357349209)
            ·
              refine ⟨32379567311182726768011907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 43172756414910302357349209 32379567311182726768011907)
              ·
                refine ⟨48569350966774090152017861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32379567311182726768011907 48569350966774090152017861)
                ·
                  refine ⟨9106753306270141903503349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 48569350966774090152017861 9106753306270141903503349)
                  ·
                    refine ⟨853758122462825803453439, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9106753306270141903503349 853758122462825803453439)
                    ·
                      rfl

theorem cell23_4988064_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 2, 1, 4, 5].length) (baseStart_4988064 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4988064 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4988064 prefixEnd_4988064 := by exact prefixLift 4988064
  have htrace : WordTrace (prefixWord ++ tailWord_4988064) baseStart_4988064 baseEnd_4988064 := by
    simpa [prefixWord, tailWord_4988064, baseEnd_4988064] using wordTrace_append hprefix tailTrace_4988064
  have hstable : (prefixWord ++ tailWord_4988064).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4988064).length < 2 ^ (prefixWord ++ tailWord_4988064).sum := by decide
  have hdescent : baseEnd_4988064 < baseStart_4988064 := by decide
  rcases family_descends (prefixWord ++ tailWord_4988064) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4988128 : List Nat := [2, 1, 1, 3, 1, 6, 1, 1, 3, 4]
def baseStart_4988128 : Nat := 118140960795 + 4988128 * 2 ^ 59
def prefixEnd_4988128 : Nat := 4983230072969 + 3 ^ 40 * 4988128 * 2
def baseEnd_4988128 : Nat := 853769076716788386653341

theorem tailTrace_4988128 : CollatzResearch.WordTrace tailWord_4988128 prefixEnd_4988128 853769076716788386653341 := by
  unfold tailWord_4988128
  simp only [CollatzResearch.WordTrace]
  refine ⟨90965987236435817641966519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 121287982981914423522622025 90965987236435817641966519)
  ·
    refine ⟨136448980854653726462949779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90965987236435817641966519 136448980854653726462949779)
    ·
      refine ⟨204673471281980589694424669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 136448980854653726462949779 204673471281980589694424669)
      ·
        refine ⟨76752551730742721135409251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 204673471281980589694424669 76752551730742721135409251)
        ·
          refine ⟨115128827596114081703113877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 76752551730742721135409251 115128827596114081703113877)
          ·
            refine ⟨5396663793567847579833463, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 115128827596114081703113877 5396663793567847579833463)
            ·
              refine ⟨8094995690351771369750195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5396663793567847579833463 8094995690351771369750195)
              ·
                refine ⟨12142493535527657054625293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8094995690351771369750195 12142493535527657054625293)
                ·
                  refine ⟨4553435075822871395484485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12142493535527657054625293 4553435075822871395484485)
                  ·
                    refine ⟨853769076716788386653341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4553435075822871395484485 853769076716788386653341)
                    ·
                      rfl

theorem cell23_4988128_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 6, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 6, 1, 1, 3, 4].length) (baseStart_4988128 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4988128 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4988128 prefixEnd_4988128 := by exact prefixLift 4988128
  have htrace : WordTrace (prefixWord ++ tailWord_4988128) baseStart_4988128 baseEnd_4988128 := by
    simpa [prefixWord, tailWord_4988128, baseEnd_4988128] using wordTrace_append hprefix tailTrace_4988128
  have hstable : (prefixWord ++ tailWord_4988128).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4988128).length < 2 ^ (prefixWord ++ tailWord_4988128).sum := by decide
  have hdescent : baseEnd_4988128 < baseStart_4988128 := by decide
  rcases family_descends (prefixWord ++ tailWord_4988128) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4988225 : List Nat := [1, 2, 5, 2, 1, 2, 1, 3, 1, 1, 4]
def baseStart_4988225 : Nat := 118140960795 + 4988225 * 2 ^ 59
def prefixEnd_4988225 : Nat := 4983230072969 + 3 ^ 40 * 4988225 * 2
def baseEnd_4988225 : Nat := 2561357037773851280447077

theorem tailTrace_4988225 : CollatzResearch.WordTrace tailWord_4988225 prefixEnd_4988225 2561357037773851280447077 := by
  unfold tailWord_4988225
  simp only [CollatzResearch.WordTrace]
  refine ⟨181935512353520220850214129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121290341569013480566809419 181935512353520220850214129)
  ·
    refine ⟨136451634265140165637660597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 181935512353520220850214129 136451634265140165637660597)
    ·
      refine ⟨12792340712356890528530681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 136451634265140165637660597 12792340712356890528530681)
      ·
        refine ⟨9594255534267667896398011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12792340712356890528530681 9594255534267667896398011)
        ·
          refine ⟨14391383301401501844597017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9594255534267667896398011 14391383301401501844597017)
          ·
            refine ⟨10793537476051126383447763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14391383301401501844597017 10793537476051126383447763)
            ·
              refine ⟨16190306214076689575171645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10793537476051126383447763 16190306214076689575171645)
              ·
                refine ⟨6071364830278758590689367, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16190306214076689575171645 6071364830278758590689367)
                ·
                  refine ⟨9107047245418137886034051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6071364830278758590689367 9107047245418137886034051)
                  ·
                    refine ⟨13660570868127206829051077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9107047245418137886034051 13660570868127206829051077)
                    ·
                      refine ⟨2561357037773851280447077, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13660570868127206829051077 2561357037773851280447077)
                      ·
                        rfl

theorem cell23_4988225_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 2, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 2, 1, 3, 1, 1, 4].length) (baseStart_4988225 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4988225 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4988225 prefixEnd_4988225 := by exact prefixLift 4988225
  have htrace : WordTrace (prefixWord ++ tailWord_4988225) baseStart_4988225 baseEnd_4988225 := by
    simpa [prefixWord, tailWord_4988225, baseEnd_4988225] using wordTrace_append hprefix tailTrace_4988225
  have hstable : (prefixWord ++ tailWord_4988225).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4988225).length < 2 ^ (prefixWord ++ tailWord_4988225).sum := by decide
  have hdescent : baseEnd_4988225 < baseStart_4988225 := by decide
  rcases family_descends (prefixWord ++ tailWord_4988225) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4988285 : List Nat := [1, 4, 1, 1, 2, 2, 1, 5, 1, 3, 2]
def baseStart_4988285 : Nat := 118140960795 + 4988285 * 2 ^ 59
def prefixEnd_4988285 : Nat := 4983230072969 + 3 ^ 40 * 4988285 * 2
def baseEnd_4988285 : Nat := 2561387846613121045696801

theorem tailTrace_4988285 : CollatzResearch.WordTrace tailWord_4988285 prefixEnd_4988285 2561387846613121045696801 := by
  unfold tailWord_4988285
  simp only [CollatzResearch.WordTrace]
  refine ⟨181937700733302851097398309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121291800488868567398265539 181937700733302851097398309)
  ·
    refine ⟨34113318887494284580762183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 181937700733302851097398309 34113318887494284580762183)
    ·
      refine ⟨51169978331241426871143275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34113318887494284580762183 51169978331241426871143275)
      ·
        refine ⟨76754967496862140306714913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51169978331241426871143275 76754967496862140306714913)
        ·
          refine ⟨57566225622646605230036185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 76754967496862140306714913 57566225622646605230036185)
          ·
            refine ⟨43174669216984953922527139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 57566225622646605230036185 43174669216984953922527139)
            ·
              refine ⟨64762003825477430883790709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 43174669216984953922527139 64762003825477430883790709)
              ·
                refine ⟨6071437858638509145355379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 64762003825477430883790709 6071437858638509145355379)
                ·
                  refine ⟨9107156787957763718033069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6071437858638509145355379 9107156787957763718033069)
                  ·
                    refine ⟨3415183795484161394262401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9107156787957763718033069 3415183795484161394262401)
                    ·
                      refine ⟨2561387846613121045696801, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3415183795484161394262401 2561387846613121045696801)
                      ·
                        rfl

theorem cell23_4988285_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 1, 5, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 1, 5, 1, 3, 2].length) (baseStart_4988285 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4988285 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4988285 prefixEnd_4988285 := by exact prefixLift 4988285
  have htrace : WordTrace (prefixWord ++ tailWord_4988285) baseStart_4988285 baseEnd_4988285 := by
    simpa [prefixWord, tailWord_4988285, baseEnd_4988285] using wordTrace_append hprefix tailTrace_4988285
  have hstable : (prefixWord ++ tailWord_4988285).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4988285).length < 2 ^ (prefixWord ++ tailWord_4988285).sum := by decide
  have hdescent : baseEnd_4988285 < baseStart_4988285 := by decide
  rcases family_descends (prefixWord ++ tailWord_4988285) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4988311 : List Nat := [1, 1, 3, 3, 1, 1, 1, 3, 1, 4, 4]
def baseStart_4988311 : Nat := 118140960795 + 4988311 * 2 ^ 59
def prefixEnd_4988311 : Nat := 4983230072969 + 3 ^ 40 * 4988311 * 2
def baseEnd_4988311 : Nat := 2561401197110137943971681

theorem tailTrace_4988311 : CollatzResearch.WordTrace tailWord_4988311 prefixEnd_4988311 2561401197110137943971681 := by
  unfold tailWord_4988311
  simp only [CollatzResearch.WordTrace]
  refine ⟨181938649031208657537844787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121292432687472438358563191 181938649031208657537844787)
  ·
    refine ⟨272907973546812986306767181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 181938649031208657537844787 272907973546812986306767181)
    ·
      refine ⟨102340490080054869865037693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 272907973546812986306767181 102340490080054869865037693)
      ·
        refine ⟨38377683780020576199389135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 102340490080054869865037693 38377683780020576199389135)
        ·
          refine ⟨57566525670030864299083703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38377683780020576199389135 57566525670030864299083703)
          ·
            refine ⟨86349788505046296448625555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 57566525670030864299083703 86349788505046296448625555)
            ·
              refine ⟨129524682757569444672938333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 86349788505046296448625555 129524682757569444672938333)
              ·
                refine ⟨48571756034088541752351875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 129524682757569444672938333 48571756034088541752351875)
                ·
                  refine ⟨72857634051132812628527813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 48571756034088541752351875 72857634051132812628527813)
                  ·
                    refine ⟨13660806384587402367848965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 72857634051132812628527813 13660806384587402367848965)
                    ·
                      refine ⟨2561401197110137943971681, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13660806384587402367848965 2561401197110137943971681)
                      ·
                        rfl

theorem cell23_4988311_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 1, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 1, 3, 1, 4, 4].length) (baseStart_4988311 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4988311 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4988311 prefixEnd_4988311 := by exact prefixLift 4988311
  have htrace : WordTrace (prefixWord ++ tailWord_4988311) baseStart_4988311 baseEnd_4988311 := by
    simpa [prefixWord, tailWord_4988311, baseEnd_4988311] using wordTrace_append hprefix tailTrace_4988311
  have hstable : (prefixWord ++ tailWord_4988311).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4988311).length < 2 ^ (prefixWord ++ tailWord_4988311).sum := by decide
  have hdescent : baseEnd_4988311 < baseStart_4988311 := by decide
  rcases family_descends (prefixWord ++ tailWord_4988311) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4988355 : List Nat := [1, 1, 1, 3, 1, 1, 8, 2, 5]
def baseStart_4988355 : Nat := 118140960795 + 4988355 * 2 ^ 59
def prefixEnd_4988355 : Nat := 4983230072969 + 3 ^ 40 * 4988355 * 2
def baseEnd_4988355 : Nat := 284602643362103974646831

theorem tailTrace_4988355 : CollatzResearch.WordTrace tailWord_4988355 prefixEnd_4988355 284602643362103974646831 := by
  unfold tailWord_4988355
  simp only [CollatzResearch.WordTrace]
  refine ⟨181940253843049253052446519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121293502562032835368297679 181940253843049253052446519)
  ·
    refine ⟨272910380764573879578669779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 181940253843049253052446519 272910380764573879578669779)
    ·
      refine ⟨409365571146860819368004669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 272910380764573879578669779 409365571146860819368004669)
      ·
        refine ⟨153512089180072807263001751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 409365571146860819368004669 153512089180072807263001751)
        ·
          refine ⟨230268133770109210894502627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 153512089180072807263001751 230268133770109210894502627)
          ·
            refine ⟨345402200655163816341753941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 230268133770109210894502627 345402200655163816341753941)
            ·
              refine ⟨4047682038927700972754929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 345402200655163816341753941 4047682038927700972754929)
              ·
                refine ⟨3035761529195775729566197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4047682038927700972754929 3035761529195775729566197)
                ·
                  refine ⟨284602643362103974646831, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3035761529195775729566197 284602643362103974646831)
                  ·
                    rfl

theorem cell23_4988355_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 8, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 8, 2, 5].length) (baseStart_4988355 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4988355 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4988355 prefixEnd_4988355 := by exact prefixLift 4988355
  have htrace : WordTrace (prefixWord ++ tailWord_4988355) baseStart_4988355 baseEnd_4988355 := by
    simpa [prefixWord, tailWord_4988355, baseEnd_4988355] using wordTrace_append hprefix tailTrace_4988355
  have hstable : (prefixWord ++ tailWord_4988355).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4988355).length < 2 ^ (prefixWord ++ tailWord_4988355).sum := by decide
  have hdescent : baseEnd_4988355 < baseStart_4988355 := by decide
  rcases family_descends (prefixWord ++ tailWord_4988355) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4988385 : List Nat := [1, 2, 3, 1, 2, 5, 1, 1, 2, 5]
def baseStart_4988385 : Nat := 118140960795 + 4988385 * 2 ^ 59
def prefixEnd_4988385 : Nat := 4983230072969 + 3 ^ 40 * 4988385 * 2
def baseEnd_4988385 : Nat := 853813064892856884815447

theorem tailTrace_4988385 : CollatzResearch.WordTrace tailWord_4988385 prefixEnd_4988385 853813064892856884815447 := by
  unfold tailWord_4988385
  simp only [CollatzResearch.WordTrace]
  refine ⟨181941348032940568176038609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121294232021960378784025739 181941348032940568176038609)
  ·
    refine ⟨136456011024705426132028957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 181941348032940568176038609 136456011024705426132028957)
    ·
      refine ⟨51171004134264534799510859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 136456011024705426132028957 51171004134264534799510859)
      ·
        refine ⟨76756506201396802199266289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51171004134264534799510859 76756506201396802199266289)
        ·
          refine ⟨57567379651047601649449717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 76756506201396802199266289 57567379651047601649449717)
          ·
            refine ⟨5396941842285712654635911, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 57567379651047601649449717 5396941842285712654635911)
            ·
              refine ⟨8095412763428568981953867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5396941842285712654635911 8095412763428568981953867)
              ·
                refine ⟨12143119145142853472930801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8095412763428568981953867 12143119145142853472930801)
                ·
                  refine ⟨9107339358857140104698101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12143119145142853472930801 9107339358857140104698101)
                  ·
                    refine ⟨853813064892856884815447, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9107339358857140104698101 853813064892856884815447)
                    ·
                      rfl

theorem cell23_4988385_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 5, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 5, 1, 1, 2, 5].length) (baseStart_4988385 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4988385 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4988385 prefixEnd_4988385 := by exact prefixLift 4988385
  have htrace : WordTrace (prefixWord ++ tailWord_4988385) baseStart_4988385 baseEnd_4988385 := by
    simpa [prefixWord, tailWord_4988385, baseEnd_4988385] using wordTrace_append hprefix tailTrace_4988385
  have hstable : (prefixWord ++ tailWord_4988385).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4988385).length < 2 ^ (prefixWord ++ tailWord_4988385).sum := by decide
  have hdescent : baseEnd_4988385 < baseStart_4988385 := by decide
  rcases family_descends (prefixWord ++ tailWord_4988385) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4988411 : List Nat := [1, 1, 1, 1, 1, 3, 2, 5, 8]
def baseStart_4988411 : Nat := 118140960795 + 4988411 * 2 ^ 59
def prefixEnd_4988411 : Nat := 4983230072969 + 3 ^ 40 * 4988411 * 2
def baseEnd_4988411 : Nat := 284605838352843061413469

theorem tailTrace_4988411 : CollatzResearch.WordTrace tailWord_4988411 prefixEnd_4988411 284605838352843061413469 := by
  unfold tailWord_4988411
  simp only [CollatzResearch.WordTrace]
  refine ⟨181942296330846374616485087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121294864220564249744323391 181942296330846374616485087)
  ·
    refine ⟨272913444496269561924727631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 181942296330846374616485087 272913444496269561924727631)
    ·
      refine ⟨409370166744404342887091447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 272913444496269561924727631 409370166744404342887091447)
      ·
        refine ⟨614055250116606514330637171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 409370166744404342887091447 614055250116606514330637171)
        ·
          refine ⟨921082875174909771495955757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 614055250116606514330637171 921082875174909771495955757)
          ·
            refine ⟨345406078190591164310983409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 921082875174909771495955757 345406078190591164310983409)
            ·
              refine ⟨259054558642943373233237557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 345406078190591164310983409 259054558642943373233237557)
              ·
                refine ⟨24286364872775941240616021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 259054558642943373233237557 24286364872775941240616021)
                ·
                  refine ⟨284605838352843061413469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 24286364872775941240616021 284605838352843061413469)
                  ·
                    rfl

theorem cell23_4988411_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 2, 5, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 2, 5, 8].length) (baseStart_4988411 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4988411 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4988411 prefixEnd_4988411 := by exact prefixLift 4988411
  have htrace : WordTrace (prefixWord ++ tailWord_4988411) baseStart_4988411 baseEnd_4988411 := by
    simpa [prefixWord, tailWord_4988411, baseEnd_4988411] using wordTrace_append hprefix tailTrace_4988411
  have hstable : (prefixWord ++ tailWord_4988411).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4988411).length < 2 ^ (prefixWord ++ tailWord_4988411).sum := by decide
  have hdescent : baseEnd_4988411 < baseStart_4988411 := by decide
  rcases family_descends (prefixWord ++ tailWord_4988411) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4988431 : List Nat := [1, 1, 2, 1, 1, 1, 2, 2, 3, 1, 8]
def baseStart_4988431 : Nat := 118140960795 + 4988431 * 2 ^ 59
def prefixEnd_4988431 : Nat := 4983230072969 + 3 ^ 40 * 4988431 * 2
def baseEnd_4988431 : Nat := 2561462814788677474471129

theorem tailTrace_4988431 : CollatzResearch.WordTrace tailWord_4988431 prefixEnd_4988431 2561462814788677474471129 := by
  unfold tailWord_4988431
  simp only [CollatzResearch.WordTrace]
  refine ⟨181943025790773918032213147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121295350527182612021475431 181943025790773918032213147)
  ·
    refine ⟨272914538686160877048319721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 181943025790773918032213147 272914538686160877048319721)
    ·
      refine ⟨204685904014620657786239791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 272914538686160877048319721 204685904014620657786239791)
      ·
        refine ⟨307028856021930986679359687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 204685904014620657786239791 307028856021930986679359687)
        ·
          refine ⟨460543284032896480019039531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 307028856021930986679359687 460543284032896480019039531)
          ·
            refine ⟨690814926049344720028559297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 460543284032896480019039531 690814926049344720028559297)
            ·
              refine ⟨518111194537008540021419473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 690814926049344720028559297 518111194537008540021419473)
              ·
                refine ⟨388583395902756405016064605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 518111194537008540021419473 388583395902756405016064605)
                ·
                  refine ⟨145718773463533651881024227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 388583395902756405016064605 145718773463533651881024227)
                  ·
                    refine ⟨218578160195300477821536341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 145718773463533651881024227 218578160195300477821536341)
                    ·
                      refine ⟨2561462814788677474471129, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 218578160195300477821536341 2561462814788677474471129)
                      ·
                        rfl

theorem cell23_4988431_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 2, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 2, 3, 1, 8].length) (baseStart_4988431 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4988431 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4988431 prefixEnd_4988431 := by exact prefixLift 4988431
  have htrace : WordTrace (prefixWord ++ tailWord_4988431) baseStart_4988431 baseEnd_4988431 := by
    simpa [prefixWord, tailWord_4988431, baseEnd_4988431] using wordTrace_append hprefix tailTrace_4988431
  have hstable : (prefixWord ++ tailWord_4988431).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4988431).length < 2 ^ (prefixWord ++ tailWord_4988431).sum := by decide
  have hdescent : baseEnd_4988431 < baseStart_4988431 := by decide
  rcases family_descends (prefixWord ++ tailWord_4988431) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4988449 : List Nat := [1, 2, 3, 2, 2, 4, 1, 3, 1, 4]
def baseStart_4988449 : Nat := 118140960795 + 4988449 * 2 ^ 59
def prefixEnd_4988449 : Nat := 4983230072969 + 3 ^ 40 * 4988449 * 2
def baseEnd_4988449 : Nat := 853824019146819468015349

theorem tailTrace_4988449 : CollatzResearch.WordTrace tailWord_4988449 prefixEnd_4988449 853824019146819468015349 := by
  unfold tailWord_4988449
  simp only [CollatzResearch.WordTrace]
  refine ⟨181943682304708707106368401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121295788203139138070912267 181943682304708707106368401)
  ·
    refine ⟨136457761728531530329776301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 181943682304708707106368401 136457761728531530329776301)
    ·
      refine ⟨51171660648199323873666113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 136457761728531530329776301 51171660648199323873666113)
      ·
        refine ⟨38378745486149492905249585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 51171660648199323873666113 38378745486149492905249585)
        ·
          refine ⟨28784059114612119678937189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38378745486149492905249585 28784059114612119678937189)
          ·
            refine ⟨5397011083989772439800723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 28784059114612119678937189 5397011083989772439800723)
            ·
              refine ⟨8095516625984658659701085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5397011083989772439800723 8095516625984658659701085)
              ·
                refine ⟨3035818734744246997387907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8095516625984658659701085 3035818734744246997387907)
                ·
                  refine ⟨4553728102116370496081861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3035818734744246997387907 4553728102116370496081861)
                  ·
                    refine ⟨853824019146819468015349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4553728102116370496081861 853824019146819468015349)
                    ·
                      rfl

theorem cell23_4988449_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 4, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 4, 1, 3, 1, 4].length) (baseStart_4988449 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4988449 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4988449 prefixEnd_4988449 := by exact prefixLift 4988449
  have htrace : WordTrace (prefixWord ++ tailWord_4988449) baseStart_4988449 baseEnd_4988449 := by
    simpa [prefixWord, tailWord_4988449, baseEnd_4988449] using wordTrace_append hprefix tailTrace_4988449
  have hstable : (prefixWord ++ tailWord_4988449).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4988449).length < 2 ^ (prefixWord ++ tailWord_4988449).sum := by decide
  have hdescent : baseEnd_4988449 < baseStart_4988449 := by decide
  rcases family_descends (prefixWord ++ tailWord_4988449) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4988472 : List Nat := [2, 1, 2, 1, 4, 2, 3, 1, 3, 1, 3]
def baseStart_4988472 : Nat := 118140960795 + 4988472 * 2 ^ 59
def prefixEnd_4988472 : Nat := 4983230072969 + 3 ^ 40 * 4988472 * 2
def baseEnd_4988472 : Nat := 2561483867495511814058441

theorem tailTrace_4988472 : CollatzResearch.WordTrace tailWord_4988472 prefixEnd_4988472 2561483867495511814058441 := by
  unfold tailWord_4988472
  simp only [CollatzResearch.WordTrace]
  refine ⟨90972260591812691017227835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 121296347455750254689637113 90972260591812691017227835)
  ·
    refine ⟨136458390887719036525841753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90972260591812691017227835 136458390887719036525841753)
    ·
      refine ⟨102343793165789277394381315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 136458390887719036525841753 102343793165789277394381315)
      ·
        refine ⟨153515689748683916091571973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 102343793165789277394381315 153515689748683916091571973)
        ·
          refine ⟨28784191827878234267169745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 153515689748683916091571973 28784191827878234267169745)
          ·
            refine ⟨21588143870908675700377309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28784191827878234267169745 21588143870908675700377309)
            ·
              refine ⟨8095553951590753387641491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21588143870908675700377309 8095553951590753387641491)
              ·
                refine ⟨12143330927386130081462237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8095553951590753387641491 12143330927386130081462237)
                ·
                  refine ⟨4553749097769798780548339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12143330927386130081462237 4553749097769798780548339)
                  ·
                    refine ⟨6830623646654698170822509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4553749097769798780548339 6830623646654698170822509)
                    ·
                      refine ⟨2561483867495511814058441, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6830623646654698170822509 2561483867495511814058441)
                      ·
                        rfl

theorem cell23_4988472_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 2, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 2, 3, 1, 3, 1, 3].length) (baseStart_4988472 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4988472 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4988472 prefixEnd_4988472 := by exact prefixLift 4988472
  have htrace : WordTrace (prefixWord ++ tailWord_4988472) baseStart_4988472 baseEnd_4988472 := by
    simpa [prefixWord, tailWord_4988472, baseEnd_4988472] using wordTrace_append hprefix tailTrace_4988472
  have hstable : (prefixWord ++ tailWord_4988472).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4988472).length < 2 ^ (prefixWord ++ tailWord_4988472).sum := by decide
  have hdescent : baseEnd_4988472 < baseStart_4988472 := by decide
  rcases family_descends (prefixWord ++ tailWord_4988472) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4988492 : List Nat := [2, 2, 1, 3, 1, 5, 1, 2, 1, 5]
def baseStart_4988492 : Nat := 118140960795 + 4988492 * 2 ^ 59
def prefixEnd_4988492 : Nat := 4983230072969 + 3 ^ 40 * 4988492 * 2
def baseEnd_4988492 : Nat := 853831379036200578602783

theorem tailTrace_4988492 : CollatzResearch.WordTrace tailWord_4988492 prefixEnd_4988492 853831379036200578602783 := by
  unfold tailWord_4988492
  simp only [CollatzResearch.WordTrace]
  refine ⟨90972625321776462725091865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 121296833762368616966789153 90972625321776462725091865)
  ·
    refine ⟨68229468991332347043818899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 90972625321776462725091865 68229468991332347043818899)
    ·
      refine ⟨102344203486998520565728349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68229468991332347043818899 102344203486998520565728349)
      ·
        refine ⟨38379076307624445212148131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 102344203486998520565728349 38379076307624445212148131)
        ·
          refine ⟨57568614461436667818222197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38379076307624445212148131 57568614461436667818222197)
          ·
            refine ⟨5397057605759687607958331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 57568614461436667818222197 5397057605759687607958331)
            ·
              refine ⟨8095586408639531411937497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5397057605759687607958331 8095586408639531411937497)
              ·
                refine ⟨6071689806479648558953123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8095586408639531411937497 6071689806479648558953123)
                ·
                  refine ⟨9107534709719472838429685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6071689806479648558953123 9107534709719472838429685)
                  ·
                    refine ⟨853831379036200578602783, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9107534709719472838429685 853831379036200578602783)
                    ·
                      rfl

theorem cell23_4988492_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 5, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 5, 1, 2, 1, 5].length) (baseStart_4988492 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4988492 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4988492 prefixEnd_4988492 := by exact prefixLift 4988492
  have htrace : WordTrace (prefixWord ++ tailWord_4988492) baseStart_4988492 baseEnd_4988492 := by
    simpa [prefixWord, tailWord_4988492, baseEnd_4988492] using wordTrace_append hprefix tailTrace_4988492
  have hstable : (prefixWord ++ tailWord_4988492).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4988492).length < 2 ^ (prefixWord ++ tailWord_4988492).sum := by decide
  have hdescent : baseEnd_4988492 < baseStart_4988492 := by decide
  rcases family_descends (prefixWord ++ tailWord_4988492) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4988515 : List Nat := [1, 1, 1, 5, 1, 3, 3, 1, 1, 1, 5]
def baseStart_4988515 : Nat := 118140960795 + 4988515 * 2 ^ 59
def prefixEnd_4988515 : Nat := 4983230072969 + 3 ^ 40 * 4988515 * 2
def baseEnd_4988515 : Nat := 2561505947163655145820743

theorem tailTrace_4988515 : CollatzResearch.WordTrace tailWord_4988515 prefixEnd_4988515 2561505947163655145820743 := by
  unfold tailWord_4988515
  simp only [CollatzResearch.WordTrace]
  refine ⟨181946089522469600378270999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121297393014979733585513999 181946089522469600378270999)
  ·
    refine ⟨272919134283704400567406499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 181946089522469600378270999 272919134283704400567406499)
    ·
      refine ⟨409378701425556600851109749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 272919134283704400567406499 409378701425556600851109749)
      ·
        refine ⟨38379253258645931329791539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 409378701425556600851109749 38379253258645931329791539)
        ·
          refine ⟨57568879887968896994687309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38379253258645931329791539 57568879887968896994687309)
          ·
            refine ⟨21588329957988336373007741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 57568879887968896994687309 21588329957988336373007741)
            ·
              refine ⟨8095623734245626139877903, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21588329957988336373007741 8095623734245626139877903)
              ·
                refine ⟨12143435601368439209816855, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8095623734245626139877903 12143435601368439209816855)
                ·
                  refine ⟨18215153402052658814725283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12143435601368439209816855 18215153402052658814725283)
                  ·
                    refine ⟨27322730103078988222087925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 18215153402052658814725283 27322730103078988222087925)
                    ·
                      refine ⟨2561505947163655145820743, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 27322730103078988222087925 2561505947163655145820743)
                      ·
                        rfl

theorem cell23_4988515_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 3, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 3, 3, 1, 1, 1, 5].length) (baseStart_4988515 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4988515 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4988515 prefixEnd_4988515 := by exact prefixLift 4988515
  have htrace : WordTrace (prefixWord ++ tailWord_4988515) baseStart_4988515 baseEnd_4988515 := by
    simpa [prefixWord, tailWord_4988515, baseEnd_4988515] using wordTrace_append hprefix tailTrace_4988515
  have hstable : (prefixWord ++ tailWord_4988515).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4988515).length < 2 ^ (prefixWord ++ tailWord_4988515).sum := by decide
  have hdescent : baseEnd_4988515 < baseStart_4988515 := by decide
  rcases family_descends (prefixWord ++ tailWord_4988515) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4988522 : List Nat := [3, 1, 3, 2, 1, 2, 1, 4, 2, 4]
def baseStart_4988522 : Nat := 118140960795 + 4988522 * 2 ^ 59
def prefixEnd_4988522 : Nat := 4983230072969 + 3 ^ 40 * 4988522 * 2
def baseEnd_4988522 : Nat := 853836513842745539477737

theorem tailTrace_4988522 : CollatzResearch.WordTrace tailWord_4988522 prefixEnd_4988522 853836513842745539477737 := by
  unfold tailWord_4988522
  simp only [CollatzResearch.WordTrace]
  refine ⟨45486586208361060143443955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 121297563222296160382517213 45486586208361060143443955)
  ·
    refine ⟨68229879312541590215165933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45486586208361060143443955 68229879312541590215165933)
    ·
      refine ⟨25586204742203096330687225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 68229879312541590215165933 25586204742203096330687225)
      ·
        refine ⟨19189653556652322248015419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25586204742203096330687225 19189653556652322248015419)
        ·
          refine ⟨28784480334978483372023129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19189653556652322248015419 28784480334978483372023129)
          ·
            refine ⟨21588360251233862529017347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28784480334978483372023129 21588360251233862529017347)
            ·
              refine ⟨32382540376850793793526021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21588360251233862529017347 32382540376850793793526021)
              ·
                refine ⟨6071726320659523836286129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 32382540376850793793526021 6071726320659523836286129)
                ·
                  refine ⟨4553794740494642877214597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6071726320659523836286129 4553794740494642877214597)
                  ·
                    refine ⟨853836513842745539477737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4553794740494642877214597 853836513842745539477737)
                    ·
                      rfl

theorem cell23_4988522_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 2, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 2, 1, 4, 2, 4].length) (baseStart_4988522 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4988522 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4988522 prefixEnd_4988522 := by exact prefixLift 4988522
  have htrace : WordTrace (prefixWord ++ tailWord_4988522) baseStart_4988522 baseEnd_4988522 := by
    simpa [prefixWord, tailWord_4988522, baseEnd_4988522] using wordTrace_append hprefix tailTrace_4988522
  have hstable : (prefixWord ++ tailWord_4988522).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4988522).length < 2 ^ (prefixWord ++ tailWord_4988522).sum := by decide
  have hdescent : baseEnd_4988522 < baseStart_4988522 := by decide
  rcases family_descends (prefixWord ++ tailWord_4988522) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4988605 : List Nat := [1, 4, 1, 2, 1, 2, 2, 2, 2, 1, 5]
def baseStart_4988605 : Nat := 118140960795 + 4988605 * 2 ^ 59
def prefixEnd_4988605 : Nat := 4983230072969 + 3 ^ 40 * 4988605 * 2
def baseEnd_4988605 : Nat := 2561552160422559793695329

theorem tailTrace_4988605 : CollatzResearch.WordTrace tailWord_4988605 prefixEnd_4988605 2561552160422559793695329 := by
  unfold tailWord_4988605
  simp only [CollatzResearch.WordTrace]
  refine ⟨181949372092143545749047269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121299581394762363832698179 181949372092143545749047269)
  ·
    refine ⟨34115507267276914827946363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 181949372092143545749047269 34115507267276914827946363)
    ·
      refine ⟨51173260900915372241919545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34115507267276914827946363 51173260900915372241919545)
      ·
        refine ⟨38379945675686529181439659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 51173260900915372241919545 38379945675686529181439659)
        ·
          refine ⟨57569918513529793772159489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38379945675686529181439659 57569918513529793772159489)
          ·
            refine ⟨43177438885147345329119617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 57569918513529793772159489 43177438885147345329119617)
            ·
              refine ⟨32383079163860508996839713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 43177438885147345329119617 32383079163860508996839713)
              ·
                refine ⟨24287309372895381747629785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 32383079163860508996839713 24287309372895381747629785)
                ·
                  refine ⟨18215482029671536310722339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 24287309372895381747629785 18215482029671536310722339)
                  ·
                    refine ⟨27323223044507304466083509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 18215482029671536310722339 27323223044507304466083509)
                    ·
                      refine ⟨2561552160422559793695329, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 27323223044507304466083509 2561552160422559793695329)
                      ·
                        rfl

theorem cell23_4988605_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 2, 2, 2, 1, 5].length) (baseStart_4988605 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4988605 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4988605 prefixEnd_4988605 := by exact prefixLift 4988605
  have htrace : WordTrace (prefixWord ++ tailWord_4988605) baseStart_4988605 baseEnd_4988605 := by
    simpa [prefixWord, tailWord_4988605, baseEnd_4988605] using wordTrace_append hprefix tailTrace_4988605
  have hstable : (prefixWord ++ tailWord_4988605).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4988605).length < 2 ^ (prefixWord ++ tailWord_4988605).sum := by decide
  have hdescent : baseEnd_4988605 < baseStart_4988605 := by decide
  rcases family_descends (prefixWord ++ tailWord_4988605) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4988606 : List Nat := [4, 2, 1, 1, 2, 3, 2, 2, 1, 3, 2]
def baseStart_4988606 : Nat := 118140960795 + 4988606 * 2 ^ 59
def prefixEnd_4988606 : Nat := 4983230072969 + 3 ^ 40 * 4988606 * 2
def baseEnd_4988606 : Nat := 2561552673903214289782825

theorem tailTrace_4988606 : CollatzResearch.WordTrace tailWord_4988606 prefixEnd_4988606 2561552673903214289782825 := by
  unfold tailWord_4988606
  simp only [CollatzResearch.WordTrace]
  refine ⟨22743676070642490364979209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 121299605710093281946555781 22743676070642490364979209)
  ·
    refine ⟨17057757052981867773734407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22743676070642490364979209 17057757052981867773734407)
    ·
      refine ⟨25586635579472801660601611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17057757052981867773734407 25586635579472801660601611)
      ·
        refine ⟨38379953369209202490902417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25586635579472801660601611 38379953369209202490902417)
        ·
          refine ⟨28784965026906901868176813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38379953369209202490902417 28784965026906901868176813)
          ·
            refine ⟨10794361885090088200566305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 28784965026906901868176813 10794361885090088200566305)
            ·
              refine ⟨8095771413817566150424729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10794361885090088200566305 8095771413817566150424729)
              ·
                refine ⟨6071828560363174612818547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8095771413817566150424729 6071828560363174612818547)
                ·
                  refine ⟨9107742840544761919227821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6071828560363174612818547 9107742840544761919227821)
                  ·
                    refine ⟨3415403565204285719710433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9107742840544761919227821 3415403565204285719710433)
                    ·
                      refine ⟨2561552673903214289782825, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3415403565204285719710433 2561552673903214289782825)
                      ·
                        rfl

theorem cell23_4988606_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 3, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 3, 2, 2, 1, 3, 2].length) (baseStart_4988606 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4988606 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4988606 prefixEnd_4988606 := by exact prefixLift 4988606
  have htrace : WordTrace (prefixWord ++ tailWord_4988606) baseStart_4988606 baseEnd_4988606 := by
    simpa [prefixWord, tailWord_4988606, baseEnd_4988606] using wordTrace_append hprefix tailTrace_4988606
  have hstable : (prefixWord ++ tailWord_4988606).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4988606).length < 2 ^ (prefixWord ++ tailWord_4988606).sum := by decide
  have hdescent : baseEnd_4988606 < baseStart_4988606 := by decide
  rcases family_descends (prefixWord ++ tailWord_4988606) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4988653 : List Nat := [1, 5, 1, 2, 1, 2, 4, 1, 2, 2, 2]
def baseStart_4988653 : Nat := 118140960795 + 4988653 * 2 ^ 59
def prefixEnd_4988653 : Nat := 4983230072969 + 3 ^ 40 * 4988653 * 2
def baseEnd_4988653 : Nat := 2561576807493975605895109

theorem tailTrace_4988653 : CollatzResearch.WordTrace tailWord_4988653 prefixEnd_4988653 2561576807493975605895109 := by
  unfold tailWord_4988653
  simp only [CollatzResearch.WordTrace]
  refine ⟨181951122795969649946794613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121300748530646433297863075 181951122795969649946794613)
  ·
    refine ⟨17057917762122154682511995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 181951122795969649946794613 17057917762122154682511995)
    ·
      refine ⟨25586876643183232023767993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17057917762122154682511995 25586876643183232023767993)
      ·
        refine ⟨19190157482387424017825995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25586876643183232023767993 19190157482387424017825995)
        ·
          refine ⟨28785236223581136026738993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19190157482387424017825995 28785236223581136026738993)
          ·
            refine ⟨21588927167685852020054245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28785236223581136026738993 21588927167685852020054245)
            ·
              refine ⟨4047923843941097253760171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 21588927167685852020054245 4047923843941097253760171)
              ·
                refine ⟨6071885765911645880640257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4047923843941097253760171 6071885765911645880640257)
                ·
                  refine ⟨4553914324433734410480193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6071885765911645880640257 4553914324433734410480193)
                  ·
                    refine ⟨3415435743325300807860145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4553914324433734410480193 3415435743325300807860145)
                    ·
                      refine ⟨2561576807493975605895109, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3415435743325300807860145 2561576807493975605895109)
                      ·
                        rfl

theorem cell23_4988653_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 2, 4, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 2, 4, 1, 2, 2, 2].length) (baseStart_4988653 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4988653 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4988653 prefixEnd_4988653 := by exact prefixLift 4988653
  have htrace : WordTrace (prefixWord ++ tailWord_4988653) baseStart_4988653 baseEnd_4988653 := by
    simpa [prefixWord, tailWord_4988653, baseEnd_4988653] using wordTrace_append hprefix tailTrace_4988653
  have hstable : (prefixWord ++ tailWord_4988653).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4988653).length < 2 ^ (prefixWord ++ tailWord_4988653).sum := by decide
  have hdescent : baseEnd_4988653 < baseStart_4988653 := by decide
  rcases family_descends (prefixWord ++ tailWord_4988653) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4988655 : List Nat := [1, 1, 2, 1, 5, 1, 1, 2, 4, 5]
def baseStart_4988655 : Nat := 118140960795 + 4988655 * 2 ^ 59
def prefixEnd_4988655 : Nat := 4983230072969 + 3 ^ 40 * 4988655 * 2
def baseEnd_4988655 : Nat := 853859278151761532690033

theorem tailTrace_4988655 : CollatzResearch.WordTrace tailWord_4988655 prefixEnd_4988655 853859278151761532690033 := by
  unfold tailWord_4988655
  simp only [CollatzResearch.WordTrace]
  refine ⟨181951195741962404288367419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121300797161308269525578279 181951195741962404288367419)
  ·
    refine ⟨272926793612943606432551129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 181951195741962404288367419 272926793612943606432551129)
    ·
      refine ⟨204695095209707704824413347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 272926793612943606432551129 204695095209707704824413347)
      ·
        refine ⟨307042642814561557236620021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 204695095209707704824413347 307042642814561557236620021)
        ·
          refine ⟨28785247763865145990933127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 307042642814561557236620021 28785247763865145990933127)
          ·
            refine ⟨43177871645797718986399691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28785247763865145990933127 43177871645797718986399691)
            ·
              refine ⟨64766807468696578479599537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 43177871645797718986399691 64766807468696578479599537)
              ·
                refine ⟨48575105601522433859699653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 64766807468696578479599537 48575105601522433859699653)
                ·
                  refine ⟨9107832300285456348693685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 48575105601522433859699653 9107832300285456348693685)
                  ·
                    refine ⟨853859278151761532690033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9107832300285456348693685 853859278151761532690033)
                    ·
                      rfl

theorem cell23_4988655_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 1, 2, 4, 5].length) (baseStart_4988655 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4988655 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4988655 prefixEnd_4988655 := by exact prefixLift 4988655
  have htrace : WordTrace (prefixWord ++ tailWord_4988655) baseStart_4988655 baseEnd_4988655 := by
    simpa [prefixWord, tailWord_4988655, baseEnd_4988655] using wordTrace_append hprefix tailTrace_4988655
  have hstable : (prefixWord ++ tailWord_4988655).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4988655).length < 2 ^ (prefixWord ++ tailWord_4988655).sum := by decide
  have hdescent : baseEnd_4988655 < baseStart_4988655 := by decide
  rcases family_descends (prefixWord ++ tailWord_4988655) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4988675 : List Nat := [1, 1, 1, 3, 2, 2, 2, 3, 1, 3, 4]
def baseStart_4988675 : Nat := 118140960795 + 4988675 * 2 ^ 59
def prefixEnd_4988675 : Nat := 4983230072969 + 3 ^ 40 * 4988675 * 2
def baseEnd_4988675 : Nat := 2561588104068374519820007

theorem tailTrace_4988675 : CollatzResearch.WordTrace tailWord_4988675 prefixEnd_4988675 2561588104068374519820007 := by
  unfold tailWord_4988675
  simp only [CollatzResearch.WordTrace]
  refine ⟨181951925201889947704095479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121301283467926631802730319 181951925201889947704095479)
  ·
    refine ⟨272927887802834921556143219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 181951925201889947704095479 272927887802834921556143219)
    ·
      refine ⟨409391831704252382334214829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 272927887802834921556143219 409391831704252382334214829)
      ·
        refine ⟨153521936889094643375330561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 409391831704252382334214829 153521936889094643375330561)
        ·
          refine ⟨115141452666820982531497921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 153521936889094643375330561 115141452666820982531497921)
          ·
            refine ⟨86356089500115736898623441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 115141452666820982531497921 86356089500115736898623441)
            ·
              refine ⟨64767067125086802673967581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 86356089500115736898623441 64767067125086802673967581)
              ·
                refine ⟨24287650171907551002737843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 64767067125086802673967581 24287650171907551002737843)
                ·
                  refine ⟨36431475257861326504106765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24287650171907551002737843 36431475257861326504106765)
                  ·
                    refine ⟨13661803221697997439040037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 36431475257861326504106765 13661803221697997439040037)
                    ·
                      refine ⟨2561588104068374519820007, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13661803221697997439040037 2561588104068374519820007)
                      ·
                        rfl

theorem cell23_4988675_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 2, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 2, 3, 1, 3, 4].length) (baseStart_4988675 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4988675 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4988675 prefixEnd_4988675 := by exact prefixLift 4988675
  have htrace : WordTrace (prefixWord ++ tailWord_4988675) baseStart_4988675 baseEnd_4988675 := by
    simpa [prefixWord, tailWord_4988675, baseEnd_4988675] using wordTrace_append hprefix tailTrace_4988675
  have hstable : (prefixWord ++ tailWord_4988675).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4988675).length < 2 ^ (prefixWord ++ tailWord_4988675).sum := by decide
  have hdescent : baseEnd_4988675 < baseStart_4988675 := by decide
  rcases family_descends (prefixWord ++ tailWord_4988675) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4988709 : List Nat := [1, 3, 1, 2, 3, 3, 1, 1, 2, 4, 2]
def baseStart_4988709 : Nat := 118140960795 + 4988709 * 2 ^ 59
def prefixEnd_4988709 : Nat := 4983230072969 + 3 ^ 40 * 4988709 * 2
def baseEnd_4988709 : Nat := 2561605562410627386794851

theorem tailTrace_4988709 : CollatzResearch.WordTrace tailWord_4988709 prefixEnd_4988709 2561605562410627386794851 := by
  unfold tailWord_4988709
  simp only [CollatzResearch.WordTrace]
  refine ⟨181953165283766771510833181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121302110189177847673888787 181953165283766771510833181)
  ·
    refine ⟨68232436981412539316562443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 181953165283766771510833181 68232436981412539316562443)
    ·
      refine ⟨102348655472118808974843665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68232436981412539316562443 102348655472118808974843665)
      ·
        refine ⟨76761491604089106731132749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 102348655472118808974843665 76761491604089106731132749)
        ·
          refine ⟨28785559351533415024174781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 76761491604089106731132749 28785559351533415024174781)
          ·
            refine ⟨10794584756825030634065543, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 28785559351533415024174781 10794584756825030634065543)
            ·
              refine ⟨16191877135237545951098315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10794584756825030634065543 16191877135237545951098315)
              ·
                refine ⟨24287815702856318926647473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16191877135237545951098315 24287815702856318926647473)
                ·
                  refine ⟨18215861777142239194985605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 24287815702856318926647473 18215861777142239194985605)
                  ·
                    refine ⟨3415474083214169849059801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 18215861777142239194985605 3415474083214169849059801)
                    ·
                      refine ⟨2561605562410627386794851, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3415474083214169849059801 2561605562410627386794851)
                      ·
                        rfl

theorem cell23_4988709_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 3, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 3, 1, 1, 2, 4, 2].length) (baseStart_4988709 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4988709 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4988709 prefixEnd_4988709 := by exact prefixLift 4988709
  have htrace : WordTrace (prefixWord ++ tailWord_4988709) baseStart_4988709 baseEnd_4988709 := by
    simpa [prefixWord, tailWord_4988709, baseEnd_4988709] using wordTrace_append hprefix tailTrace_4988709
  have hstable : (prefixWord ++ tailWord_4988709).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4988709).length < 2 ^ (prefixWord ++ tailWord_4988709).sum := by decide
  have hdescent : baseEnd_4988709 < baseStart_4988709 := by decide
  rcases family_descends (prefixWord ++ tailWord_4988709) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4988726 : List Nat := [5, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4]
def baseStart_4988726 : Nat := 118140960795 + 4988726 * 2 ^ 59
def prefixEnd_4988726 : Nat := 4983230072969 + 3 ^ 40 * 4988726 * 2
def baseEnd_4988726 : Nat := 2561614291581753820282273

theorem tailTrace_4988726 : CollatzResearch.WordTrace tailWord_4988726 prefixEnd_4988726 2561614291581753820282273 := by
  unfold tailWord_4988726
  simp only [CollatzResearch.WordTrace]
  refine ⟨11372111582794073963387627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 121302523549803455609468021 11372111582794073963387627)
  ·
    refine ⟨17058167374191110945081441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11372111582794073963387627 17058167374191110945081441)
    ·
      refine ⟨12793625530643333208811081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17058167374191110945081441 12793625530643333208811081)
      ·
        refine ⟨9595219147982499906608311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12793625530643333208811081 9595219147982499906608311)
        ·
          refine ⟨14392828721973749859912467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9595219147982499906608311 14392828721973749859912467)
          ·
            refine ⟨21589243082960624789868701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14392828721973749859912467 21589243082960624789868701)
            ·
              refine ⟨8095966156110234296200763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21589243082960624789868701 8095966156110234296200763)
              ·
                refine ⟨12143949234165351444301145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8095966156110234296200763 12143949234165351444301145)
                ·
                  refine ⟨9107961925624013583225859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12143949234165351444301145 9107961925624013583225859)
                  ·
                    refine ⟨13661942888436020374838789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9107961925624013583225859 13661942888436020374838789)
                    ·
                      refine ⟨2561614291581753820282273, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13661942888436020374838789 2561614291581753820282273)
                      ·
                        rfl

theorem cell23_4988726_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4].length) (baseStart_4988726 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4988726 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4988726 prefixEnd_4988726 := by exact prefixLift 4988726
  have htrace : WordTrace (prefixWord ++ tailWord_4988726) baseStart_4988726 baseEnd_4988726 := by
    simpa [prefixWord, tailWord_4988726, baseEnd_4988726] using wordTrace_append hprefix tailTrace_4988726
  have hstable : (prefixWord ++ tailWord_4988726).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4988726).length < 2 ^ (prefixWord ++ tailWord_4988726).sum := by decide
  have hdescent : baseEnd_4988726 < baseStart_4988726 := by decide
  rcases family_descends (prefixWord ++ tailWord_4988726) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4988749 : List Nat := [1, 6, 1, 2, 1, 2, 1, 1, 8]
def baseStart_4988749 : Nat := 118140960795 + 4988749 * 2 ^ 59
def prefixEnd_4988749 : Nat := 4983230072969 + 3 ^ 40 * 4988749 * 2
def baseEnd_4988749 : Nat := 284625122404089692254963

theorem tailTrace_4988749 : CollatzResearch.WordTrace tailWord_4988749 prefixEnd_4988749 284625122404089692254963 := by
  unfold tailWord_4988749
  simp only [CollatzResearch.WordTrace]
  refine ⟨181954624203621858342289301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121303082802414572228192867 181954624203621858342289301)
  ·
    refine ⟨8529123009544774609794811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 181954624203621858342289301 8529123009544774609794811)
    ·
      refine ⟨12793684514317161914692217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8529123009544774609794811 12793684514317161914692217)
      ·
        refine ⟨9595263385737871436019163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12793684514317161914692217 9595263385737871436019163)
        ·
          refine ⟨14392895078606807154028745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9595263385737871436019163 14392895078606807154028745)
          ·
            refine ⟨10794671308955105365521559, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14392895078606807154028745 10794671308955105365521559)
            ·
              refine ⟨16192006963432658048282339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10794671308955105365521559 16192006963432658048282339)
              ·
                refine ⟨24288010445148987072423509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16192006963432658048282339 24288010445148987072423509)
                ·
                  refine ⟨284625122404089692254963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 24288010445148987072423509 284625122404089692254963)
                  ·
                    rfl

theorem cell23_4988749_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 2, 1, 1, 8].length) (baseStart_4988749 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4988749 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4988749 prefixEnd_4988749 := by exact prefixLift 4988749
  have htrace : WordTrace (prefixWord ++ tailWord_4988749) baseStart_4988749 baseEnd_4988749 := by
    simpa [prefixWord, tailWord_4988749, baseEnd_4988749] using wordTrace_append hprefix tailTrace_4988749
  have hstable : (prefixWord ++ tailWord_4988749).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4988749).length < 2 ^ (prefixWord ++ tailWord_4988749).sum := by decide
  have hdescent : baseEnd_4988749 < baseStart_4988749 := by decide
  rcases family_descends (prefixWord ++ tailWord_4988749) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4988809 : List Nat := [1, 2, 1, 1, 5, 1, 2, 4, 2, 4]
def baseStart_4988809 : Nat := 118140960795 + 4988809 * 2 ^ 59
def prefixEnd_4988809 : Nat := 4983230072969 + 3 ^ 40 * 4988809 * 2
def baseEnd_4988809 : Nat := 853885636825358998514797

theorem tailTrace_4988809 : CollatzResearch.WordTrace tailWord_4988809 prefixEnd_4988809 853885636825358998514797 := by
  unfold tailWord_4988809
  simp only [CollatzResearch.WordTrace]
  refine ⟨181956812583404488589473481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121304541722269659059648987 181956812583404488589473481)
  ·
    refine ⟨136467609437553366442105111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 181956812583404488589473481 136467609437553366442105111)
    ·
      refine ⟨204701414156330049663157667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 136467609437553366442105111 204701414156330049663157667)
      ·
        refine ⟨307052121234495074494736501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 204701414156330049663157667 307052121234495074494736501)
        ·
          refine ⟨28786136365733913233881547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 307052121234495074494736501 28786136365733913233881547)
          ·
            refine ⟨43179204548600869850822321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28786136365733913233881547 43179204548600869850822321)
            ·
              refine ⟨32384403411450652388116741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 43179204548600869850822321 32384403411450652388116741)
              ·
                refine ⟨6072075639646997322771889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 32384403411450652388116741 6072075639646997322771889)
                ·
                  refine ⟨4554056729735247992078917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6072075639646997322771889 4554056729735247992078917)
                  ·
                    refine ⟨853885636825358998514797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4554056729735247992078917 853885636825358998514797)
                    ·
                      rfl

theorem cell23_4988809_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 2, 4, 2, 4].length) (baseStart_4988809 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4988809 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4988809 prefixEnd_4988809 := by exact prefixLift 4988809
  have htrace : WordTrace (prefixWord ++ tailWord_4988809) baseStart_4988809 baseEnd_4988809 := by
    simpa [prefixWord, tailWord_4988809, baseEnd_4988809] using wordTrace_append hprefix tailTrace_4988809
  have hstable : (prefixWord ++ tailWord_4988809).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4988809).length < 2 ^ (prefixWord ++ tailWord_4988809).sum := by decide
  have hdescent : baseEnd_4988809 < baseStart_4988809 := by decide
  rcases family_descends (prefixWord ++ tailWord_4988809) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4988810 : List Nat := [3, 1, 2, 4, 3, 1, 1, 1, 3, 1, 3]
def baseStart_4988810 : Nat := 118140960795 + 4988810 * 2 ^ 59
def prefixEnd_4988810 : Nat := 4983230072969 + 3 ^ 40 * 4988810 * 2
def baseEnd_4988810 : Nat := 2561657423956731491631887

theorem tailTrace_4988810 : CollatzResearch.WordTrace tailWord_4988810 prefixEnd_4988810 2561657423956731491631887 := by
  unfold tailWord_4988810
  simp only [CollatzResearch.WordTrace]
  refine ⟨45489212264100216440064971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 121304566037600577173506589 45489212264100216440064971)
  ·
    refine ⟨68233818396150324660097457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45489212264100216440064971 68233818396150324660097457)
    ·
      refine ⟨51175363797112743495073093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 68233818396150324660097457 51175363797112743495073093)
      ·
        refine ⟨9595380711958639405326205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 51175363797112743495073093 9595380711958639405326205)
        ·
          refine ⟨3598267766984489776997327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9595380711958639405326205 3598267766984489776997327)
          ·
            refine ⟨5397401650476734665495991, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3598267766984489776997327 5397401650476734665495991)
            ·
              refine ⟨8096102475715101998243987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5397401650476734665495991 8096102475715101998243987)
              ·
                refine ⟨12144153713572652997365981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8096102475715101998243987 12144153713572652997365981)
                ·
                  refine ⟨4554057642589744874012243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12144153713572652997365981 4554057642589744874012243)
                  ·
                    refine ⟨6831086463884617311018365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4554057642589744874012243 6831086463884617311018365)
                    ·
                      refine ⟨2561657423956731491631887, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6831086463884617311018365 2561657423956731491631887)
                      ·
                        rfl

theorem cell23_4988810_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 3, 1, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 3, 1, 1, 1, 3, 1, 3].length) (baseStart_4988810 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4988810 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4988810 prefixEnd_4988810 := by exact prefixLift 4988810
  have htrace : WordTrace (prefixWord ++ tailWord_4988810) baseStart_4988810 baseEnd_4988810 := by
    simpa [prefixWord, tailWord_4988810, baseEnd_4988810] using wordTrace_append hprefix tailTrace_4988810
  have hstable : (prefixWord ++ tailWord_4988810).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4988810).length < 2 ^ (prefixWord ++ tailWord_4988810).sum := by decide
  have hdescent : baseEnd_4988810 < baseStart_4988810 := by decide
  rcases family_descends (prefixWord ++ tailWord_4988810) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4988826 : List Nat := [3, 1, 1, 4, 2, 2, 1, 3, 2, 4]
def baseStart_4988826 : Nat := 118140960795 + 4988826 * 2 ^ 59
def prefixEnd_4988826 : Nat := 4983230072969 + 3 ^ 40 * 4988826 * 2
def baseEnd_4988826 : Nat := 853888546549067809677271

theorem tailTrace_4988826 : CollatzResearch.WordTrace tailWord_4988826 prefixEnd_4988826 853888546549067809677271 := by
  unfold tailWord_4988826
  simp only [CollatzResearch.WordTrace]
  refine ⟨45489358156085725123210583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 121304955082895266995228221 45489358156085725123210583)
  ·
    refine ⟨68234037234128587684815875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45489358156085725123210583 68234037234128587684815875)
    ·
      refine ⟨102351055851192881527223813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68234037234128587684815875 102351055851192881527223813)
      ·
        refine ⟨19190822972098665286354465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 102351055851192881527223813 19190822972098665286354465)
        ·
          refine ⟨14393117229073998964765849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19190822972098665286354465 14393117229073998964765849)
          ·
            refine ⟨10794837921805499223574387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14393117229073998964765849 10794837921805499223574387)
            ·
              refine ⟨16192256882708248835361581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10794837921805499223574387 16192256882708248835361581)
              ·
                refine ⟨6072096331015593313260593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16192256882708248835361581 6072096331015593313260593)
                ·
                  refine ⟨4554072248261694984945445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6072096331015593313260593 4554072248261694984945445)
                  ·
                    refine ⟨853888546549067809677271, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4554072248261694984945445 853888546549067809677271)
                    ·
                      rfl

theorem cell23_4988826_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 2, 1, 3, 2, 4].length) (baseStart_4988826 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4988826 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4988826 prefixEnd_4988826 := by exact prefixLift 4988826
  have htrace : WordTrace (prefixWord ++ tailWord_4988826) baseStart_4988826 baseEnd_4988826 := by
    simpa [prefixWord, tailWord_4988826, baseEnd_4988826] using wordTrace_append hprefix tailTrace_4988826
  have hstable : (prefixWord ++ tailWord_4988826).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4988826).length < 2 ^ (prefixWord ++ tailWord_4988826).sum := by decide
  have hdescent : baseEnd_4988826 < baseStart_4988826 := by decide
  rcases family_descends (prefixWord ++ tailWord_4988826) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4988830 : List Nat := [4, 3, 1, 3, 1, 2, 1, 2, 1, 5]
def baseStart_4988830 : Nat := 118140960795 + 4988830 * 2 ^ 59
def prefixEnd_4988830 : Nat := 4983230072969 + 3 ^ 40 * 4988830 * 2
def baseEnd_4988830 : Nat := 853889231189940471127265

theorem tailTrace_4988830 : CollatzResearch.WordTrace tailWord_4988830 prefixEnd_4988830 853889231189940471127265 := by
  unfold tailWord_4988830
  simp only [CollatzResearch.WordTrace]
  refine ⟨22744697314541051146998493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 121305052344218939450658629 22744697314541051146998493)
  ·
    refine ⟨8529261492952894180124435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 22744697314541051146998493 8529261492952894180124435)
    ·
      refine ⟨12793892239429341270186653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8529261492952894180124435 12793892239429341270186653)
      ·
        refine ⟨4797709589786002976319995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12793892239429341270186653 4797709589786002976319995)
        ·
          refine ⟨7196564384679004464479993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4797709589786002976319995 7196564384679004464479993)
          ·
            refine ⟨5397423288509253348359995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7196564384679004464479993 5397423288509253348359995)
            ·
              refine ⟨8096134932763880022539993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5397423288509253348359995 8096134932763880022539993)
              ·
                refine ⟨6072101199572910016904995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8096134932763880022539993 6072101199572910016904995)
                ·
                  refine ⟨9108151799359365025357493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6072101199572910016904995 9108151799359365025357493)
                  ·
                    refine ⟨853889231189940471127265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9108151799359365025357493 853889231189940471127265)
                    ·
                      rfl

theorem cell23_4988830_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 3, 1, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 3, 1, 2, 1, 2, 1, 5].length) (baseStart_4988830 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4988830 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4988830 prefixEnd_4988830 := by exact prefixLift 4988830
  have htrace : WordTrace (prefixWord ++ tailWord_4988830) baseStart_4988830 baseEnd_4988830 := by
    simpa [prefixWord, tailWord_4988830, baseEnd_4988830] using wordTrace_append hprefix tailTrace_4988830
  have hstable : (prefixWord ++ tailWord_4988830).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4988830).length < 2 ^ (prefixWord ++ tailWord_4988830).sum := by decide
  have hdescent : baseEnd_4988830 < baseStart_4988830 := by decide
  rcases family_descends (prefixWord ++ tailWord_4988830) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4988833 : List Nat := [1, 2, 3, 4, 2, 2, 1, 2, 1, 1, 4]
def baseStart_4988833 : Nat := 118140960795 + 4988833 * 2 ^ 59
def prefixEnd_4988833 : Nat := 4983230072969 + 3 ^ 40 * 4988833 * 2
def baseEnd_4988833 : Nat := 2561669234011784901644281

theorem tailTrace_4988833 : CollatzResearch.WordTrace tailWord_4988833 prefixEnd_4988833 2561669234011784901644281 := by
  unfold tailWord_4988833
  simp only [CollatzResearch.WordTrace]
  refine ⟨181957687935317540688347153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121305125290211693792231435 181957687935317540688347153)
  ·
    refine ⟨136468265951488155516260365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 181957687935317540688347153 136468265951488155516260365)
    ·
      refine ⟨51175599731808058318597637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 136468265951488155516260365 51175599731808058318597637)
      ·
        refine ⟨9595424949714010934737057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 51175599731808058318597637 9595424949714010934737057)
        ·
          refine ⟨7196568712285508201052793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9595424949714010934737057 7196568712285508201052793)
          ·
            refine ⟨5397426534214131150789595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7196568712285508201052793 5397426534214131150789595)
            ·
              refine ⟨8096139801321196726184393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5397426534214131150789595 8096139801321196726184393)
              ·
                refine ⟨6072104850990897544638295, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8096139801321196726184393 6072104850990897544638295)
                ·
                  refine ⟨9108157276486346316957443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6072104850990897544638295 9108157276486346316957443)
                  ·
                    refine ⟨13662235914729519475436165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9108157276486346316957443 13662235914729519475436165)
                    ·
                      refine ⟨2561669234011784901644281, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13662235914729519475436165 2561669234011784901644281)
                      ·
                        rfl

theorem cell23_4988833_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 2, 2, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 2, 2, 1, 2, 1, 1, 4].length) (baseStart_4988833 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4988833 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4988833 prefixEnd_4988833 := by exact prefixLift 4988833
  have htrace : WordTrace (prefixWord ++ tailWord_4988833) baseStart_4988833 baseEnd_4988833 := by
    simpa [prefixWord, tailWord_4988833, baseEnd_4988833] using wordTrace_append hprefix tailTrace_4988833
  have hstable : (prefixWord ++ tailWord_4988833).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4988833).length < 2 ^ (prefixWord ++ tailWord_4988833).sum := by decide
  have hdescent : baseEnd_4988833 < baseStart_4988833 := by decide
  rcases family_descends (prefixWord ++ tailWord_4988833) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4988836 : List Nat := [2, 3, 1, 2, 1, 3, 3, 2, 1, 2, 3]
def baseStart_4988836 : Nat := 118140960795 + 4988836 * 2 ^ 59
def prefixEnd_4988836 : Nat := 4983230072969 + 3 ^ 40 * 4988836 * 2
def baseEnd_4988836 : Nat := 2561670774453748389906767

theorem tailTrace_4988836 : CollatzResearch.WordTrace tailWord_4988836 prefixEnd_4988836 2561670774453748389906767 := by
  unfold tailWord_4988836
  simp only [CollatzResearch.WordTrace]
  refine ⟨90978898677153336100353181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 121305198236204448133804241 90978898677153336100353181)
  ·
    refine ⟨34117087003932501037632443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 90978898677153336100353181 34117087003932501037632443)
    ·
      refine ⟨51175630505898751556448665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34117087003932501037632443 51175630505898751556448665)
      ·
        refine ⟨38381722879424063667336499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 51175630505898751556448665 38381722879424063667336499)
        ·
          refine ⟨57572584319136095501004749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38381722879424063667336499 57572584319136095501004749)
          ·
            refine ⟨21589719119676035812876781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 57572584319136095501004749 21589719119676035812876781)
            ·
              refine ⟨8096144669878513429828793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21589719119676035812876781 8096144669878513429828793)
              ·
                refine ⟨6072108502408885072371595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8096144669878513429828793 6072108502408885072371595)
                ·
                  refine ⟨9108162753613327608557393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6072108502408885072371595 9108162753613327608557393)
                  ·
                    refine ⟨6831122065209995706418045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9108162753613327608557393 6831122065209995706418045)
                    ·
                      refine ⟨2561670774453748389906767, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6831122065209995706418045 2561670774453748389906767)
                      ·
                        rfl

theorem cell23_4988836_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 3, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 3, 3, 2, 1, 2, 3].length) (baseStart_4988836 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4988836 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4988836 prefixEnd_4988836 := by exact prefixLift 4988836
  have htrace : WordTrace (prefixWord ++ tailWord_4988836) baseStart_4988836 baseEnd_4988836 := by
    simpa [prefixWord, tailWord_4988836, baseEnd_4988836] using wordTrace_append hprefix tailTrace_4988836
  have hstable : (prefixWord ++ tailWord_4988836).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4988836).length < 2 ^ (prefixWord ++ tailWord_4988836).sum := by decide
  have hdescent : baseEnd_4988836 < baseStart_4988836 := by decide
  rcases family_descends (prefixWord ++ tailWord_4988836) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4988849 : List Nat := [1, 2, 2, 4, 2, 1, 1, 1, 3, 3, 3]
def baseStart_4988849 : Nat := 118140960795 + 4988849 * 2 ^ 59
def prefixEnd_4988849 : Nat := 4983230072969 + 3 ^ 40 * 4988849 * 2
def baseEnd_4988849 : Nat := 2561677449702256839044207

theorem tailTrace_4988849 : CollatzResearch.WordTrace tailWord_4988849 prefixEnd_4988849 2561677449702256839044207 := by
  unfold tailWord_4988849
  simp only [CollatzResearch.WordTrace]
  refine ⟨181958271503259575420929601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121305514335506383613953067 181958271503259575420929601)
  ·
    refine ⟨136468703627444681565697201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 181958271503259575420929601 136468703627444681565697201)
    ·
      refine ⟨102351527720583511174272901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 136468703627444681565697201 102351527720583511174272901)
      ·
        refine ⟨19190911447609408345176169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 102351527720583511174272901 19190911447609408345176169)
        ·
          refine ⟨14393183585707056258882127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19190911447609408345176169 14393183585707056258882127)
          ·
            refine ⟨21589775378560584388323191, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14393183585707056258882127 21589775378560584388323191)
            ·
              refine ⟨32384663067840876582484787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21589775378560584388323191 32384663067840876582484787)
              ·
                refine ⟨48576994601761314873727181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32384663067840876582484787 48576994601761314873727181)
                ·
                  refine ⟨18216372975660493077647693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 48576994601761314873727181 18216372975660493077647693)
                  ·
                    refine ⟨6831139865872684904117885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 18216372975660493077647693 6831139865872684904117885)
                    ·
                      refine ⟨2561677449702256839044207, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6831139865872684904117885 2561677449702256839044207)
                      ·
                        rfl

theorem cell23_4988849_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 1, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 1, 1, 1, 3, 3, 3].length) (baseStart_4988849 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4988849 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4988849 prefixEnd_4988849 := by exact prefixLift 4988849
  have htrace : WordTrace (prefixWord ++ tailWord_4988849) baseStart_4988849 baseEnd_4988849 := by
    simpa [prefixWord, tailWord_4988849, baseEnd_4988849] using wordTrace_append hprefix tailTrace_4988849
  have hstable : (prefixWord ++ tailWord_4988849).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4988849).length < 2 ^ (prefixWord ++ tailWord_4988849).sum := by decide
  have hdescent : baseEnd_4988849 < baseStart_4988849 := by decide
  rcases family_descends (prefixWord ++ tailWord_4988849) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4988853 : List Nat := [1, 3, 3, 2, 1, 3, 3, 1, 1, 2, 3]
def baseStart_4988853 : Nat := 118140960795 + 4988853 * 2 ^ 59
def prefixEnd_4988853 : Nat := 4983230072969 + 3 ^ 40 * 4988853 * 2
def baseEnd_4988853 : Nat := 2561679503624874823394189

theorem tailTrace_4988853 : CollatzResearch.WordTrace tailWord_4988853 prefixEnd_4988853 2561679503624874823394189 := by
  unfold tailWord_4988853
  simp only [CollatzResearch.WordTrace]
  refine ⟨181958417395245084104075213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121305611596830056069383475 181958417395245084104075213)
  ·
    refine ⟨68234406523216906539028205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 181958417395245084104075213 68234406523216906539028205)
    ·
      refine ⟨25587902446206339952135577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 68234406523216906539028205 25587902446206339952135577)
      ·
        refine ⟨19190926834654754964101683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25587902446206339952135577 19190926834654754964101683)
        ·
          refine ⟨28786390251982132446152525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19190926834654754964101683 28786390251982132446152525)
          ·
            refine ⟨10794896344493299667307197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 28786390251982132446152525 10794896344493299667307197)
            ·
              refine ⟨4048086129184987375240199, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10794896344493299667307197 4048086129184987375240199)
              ·
                refine ⟨6072129193777481062860299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4048086129184987375240199 6072129193777481062860299)
                ·
                  refine ⟨9108193790666221594290449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6072129193777481062860299 9108193790666221594290449)
                  ·
                    refine ⟨6831145342999666195717837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9108193790666221594290449 6831145342999666195717837)
                    ·
                      refine ⟨2561679503624874823394189, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6831145342999666195717837 2561679503624874823394189)
                      ·
                        rfl

theorem cell23_4988853_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 3, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 3, 3, 1, 1, 2, 3].length) (baseStart_4988853 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4988853 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4988853 prefixEnd_4988853 := by exact prefixLift 4988853
  have htrace : WordTrace (prefixWord ++ tailWord_4988853) baseStart_4988853 baseEnd_4988853 := by
    simpa [prefixWord, tailWord_4988853, baseEnd_4988853] using wordTrace_append hprefix tailTrace_4988853
  have hstable : (prefixWord ++ tailWord_4988853).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4988853).length < 2 ^ (prefixWord ++ tailWord_4988853).sum := by decide
  have hdescent : baseEnd_4988853 < baseStart_4988853 := by decide
  rcases family_descends (prefixWord ++ tailWord_4988853) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4988859 : List Nat := [1, 1, 1, 1, 1, 2, 2, 4, 5, 3, 2]
def baseStart_4988859 : Nat := 118140960795 + 4988859 * 2 ^ 59
def prefixEnd_4988859 : Nat := 4983230072969 + 3 ^ 40 * 4988859 * 2
def baseEnd_4988859 : Nat := 2561682584508801799919161

theorem tailTrace_4988859 : CollatzResearch.WordTrace tailWord_4988859 prefixEnd_4988859 2561682584508801799919161 := by
  unfold tailWord_4988859
  simp only [CollatzResearch.WordTrace]
  refine ⟨181958636233223347128793631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121305757488815564752529087 181958636233223347128793631)
  ·
    refine ⟨272937954349835020693190447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 181958636233223347128793631 272937954349835020693190447)
    ·
      refine ⟨409406931524752531039785671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 272937954349835020693190447 409406931524752531039785671)
      ·
        refine ⟨614110397287128796559678507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 409406931524752531039785671 614110397287128796559678507)
        ·
          refine ⟨921165595930693194839517761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 614110397287128796559678507 921165595930693194839517761)
          ·
            refine ⟨690874196948019896129638321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 921165595930693194839517761 690874196948019896129638321)
            ·
              refine ⟨518155647711014922097228741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 690874196948019896129638321 518155647711014922097228741)
              ·
                refine ⟨97154183945815297893230389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 518155647711014922097228741 97154183945815297893230389)
                ·
                  refine ⟨9108204744920184177490349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 97154183945815297893230389 9108204744920184177490349)
                  ·
                    refine ⟨3415576779345069066558881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9108204744920184177490349 3415576779345069066558881)
                    ·
                      refine ⟨2561682584508801799919161, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3415576779345069066558881 2561682584508801799919161)
                      ·
                        rfl

theorem cell23_4988859_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 4, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 4, 5, 3, 2].length) (baseStart_4988859 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4988859 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4988859 prefixEnd_4988859 := by exact prefixLift 4988859
  have htrace : WordTrace (prefixWord ++ tailWord_4988859) baseStart_4988859 baseEnd_4988859 := by
    simpa [prefixWord, tailWord_4988859, baseEnd_4988859] using wordTrace_append hprefix tailTrace_4988859
  have hstable : (prefixWord ++ tailWord_4988859).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4988859).length < 2 ^ (prefixWord ++ tailWord_4988859).sum := by decide
  have hdescent : baseEnd_4988859 < baseStart_4988859 := by decide
  rcases family_descends (prefixWord ++ tailWord_4988859) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4988876 : List Nat := [2, 2, 1, 4, 1, 2, 1, 2, 3, 3, 2]
def baseStart_4988876 : Nat := 118140960795 + 4988876 * 2 ^ 59
def prefixEnd_4988876 : Nat := 4983230072969 + 3 ^ 40 * 4988876 * 2
def baseEnd_4988876 : Nat := 2561691313679928233406583

theorem tailTrace_4988876 : CollatzResearch.WordTrace tailWord_4988876 prefixEnd_4988876 2561691313679928233406583 := by
  unfold tailWord_4988876
  simp only [CollatzResearch.WordTrace]
  refine ⟨90979628137080879516081241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 121306170849441172688108321 90979628137080879516081241)
  ·
    refine ⟨68234721102810659637060931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 90979628137080879516081241 68234721102810659637060931)
    ·
      refine ⟨102352081654215989455591397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68234721102810659637060931 102352081654215989455591397)
      ·
        refine ⟨19191015310165498022923387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 102352081654215989455591397 19191015310165498022923387)
        ·
          refine ⟨28786522965248247034385081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19191015310165498022923387 28786522965248247034385081)
          ·
            refine ⟨21589892223936185275788811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28786522965248247034385081 21589892223936185275788811)
            ·
              refine ⟨32384838335904277913683217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21589892223936185275788811 32384838335904277913683217)
              ·
                refine ⟨24288628751928208435262413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 32384838335904277913683217 24288628751928208435262413)
                ·
                  refine ⟨9108235781973078163223405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 24288628751928208435262413 9108235781973078163223405)
                  ·
                    refine ⟨3415588418239904311208777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9108235781973078163223405 3415588418239904311208777)
                    ·
                      refine ⟨2561691313679928233406583, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3415588418239904311208777 2561691313679928233406583)
                      ·
                        rfl

theorem cell23_4988876_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 2, 1, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 2, 1, 2, 3, 3, 2].length) (baseStart_4988876 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4988876 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4988876 prefixEnd_4988876 := by exact prefixLift 4988876
  have htrace : WordTrace (prefixWord ++ tailWord_4988876) baseStart_4988876 baseEnd_4988876 := by
    simpa [prefixWord, tailWord_4988876, baseEnd_4988876] using wordTrace_append hprefix tailTrace_4988876
  have hstable : (prefixWord ++ tailWord_4988876).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4988876).length < 2 ^ (prefixWord ++ tailWord_4988876).sum := by decide
  have hdescent : baseEnd_4988876 < baseStart_4988876 := by decide
  rcases family_descends (prefixWord ++ tailWord_4988876) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4988906 : List Nat := [3, 1, 3, 1, 2, 1, 1, 4, 1, 4, 2]
def baseStart_4988906 : Nat := 118140960795 + 4988906 * 2 ^ 59
def prefixEnd_4988906 : Nat := 4983230072969 + 3 ^ 40 * 4988906 * 2
def baseEnd_4988906 : Nat := 2561706718099563116031445

theorem tailTrace_4988906 : CollatzResearch.WordTrace tailWord_4988906 prefixEnd_4988906 2561706718099563116031445 := by
  unfold tailWord_4988906
  simp only [CollatzResearch.WordTrace]
  refine ⟨45490087616013268538938643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 121306900309368716103836381 45490087616013268538938643)
  ·
    refine ⟨68235131424019902808407965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45490087616013268538938643 68235131424019902808407965)
    ·
      refine ⟨25588174284007463553152987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 68235131424019902808407965 25588174284007463553152987)
      ·
        refine ⟨38382261426011195329729481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25588174284007463553152987 38382261426011195329729481)
        ·
          refine ⟨28786696069508396497297111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38382261426011195329729481 28786696069508396497297111)
          ·
            refine ⟨43180044104262594745945667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28786696069508396497297111 43180044104262594745945667)
            ·
              refine ⟨64770066156393892118918501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 43180044104262594745945667 64770066156393892118918501)
              ·
                refine ⟨12144387404323854772297219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 64770066156393892118918501 12144387404323854772297219)
                ·
                  refine ⟨18216581106485782158445829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12144387404323854772297219 18216581106485782158445829)
                  ·
                    refine ⟨3415608957466084154708593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 18216581106485782158445829 3415608957466084154708593)
                    ·
                      refine ⟨2561706718099563116031445, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3415608957466084154708593 2561706718099563116031445)
                      ·
                        rfl

theorem cell23_4988906_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 1, 4, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 1, 4, 1, 4, 2].length) (baseStart_4988906 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4988906 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4988906 prefixEnd_4988906 := by exact prefixLift 4988906
  have htrace : WordTrace (prefixWord ++ tailWord_4988906) baseStart_4988906 baseEnd_4988906 := by
    simpa [prefixWord, tailWord_4988906, baseEnd_4988906] using wordTrace_append hprefix tailTrace_4988906
  have hstable : (prefixWord ++ tailWord_4988906).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4988906).length < 2 ^ (prefixWord ++ tailWord_4988906).sum := by decide
  have hdescent : baseEnd_4988906 < baseStart_4988906 := by decide
  rcases family_descends (prefixWord ++ tailWord_4988906) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4988910 : List Nat := [4, 1, 2, 1, 3, 1, 4, 1, 1, 3, 2]
def baseStart_4988910 : Nat := 118140960795 + 4988910 * 2 ^ 59
def prefixEnd_4988910 : Nat := 4983230072969 + 3 ^ 40 * 4988910 * 2
def baseEnd_4988910 : Nat := 2561708772022181100381427

theorem tailTrace_4988910 : CollatzResearch.WordTrace tailWord_4988910 prefixEnd_4988910 2561708772022181100381427 := by
  unfold tailWord_4988910
  simp only [CollatzResearch.WordTrace]
  refine ⟨22745062044504822854862523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 121306997570692388559266789 22745062044504822854862523)
  ·
    refine ⟨34117593066757234282293785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22745062044504822854862523 34117593066757234282293785)
    ·
      refine ⟨25588194800067925711720339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34117593066757234282293785 25588194800067925711720339)
      ·
        refine ⟨38382292200101888567580509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25588194800067925711720339 38382292200101888567580509)
        ·
          refine ⟨14393359575038208212842691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 38382292200101888567580509 14393359575038208212842691)
          ·
            refine ⟨21590039362557312319264037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14393359575038208212842691 21590039362557312319264037)
            ·
              refine ⟨4048132380479496059862007, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 21590039362557312319264037 4048132380479496059862007)
              ·
                refine ⟨6072198570719244089793011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4048132380479496059862007 6072198570719244089793011)
                ·
                  refine ⟨9108297856078866134689517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6072198570719244089793011 9108297856078866134689517)
                  ·
                    refine ⟨3415611696029574800508569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9108297856078866134689517 3415611696029574800508569)
                    ·
                      refine ⟨2561708772022181100381427, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3415611696029574800508569 2561708772022181100381427)
                      ·
                        rfl

theorem cell23_4988910_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 1, 4, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 1, 4, 1, 1, 3, 2].length) (baseStart_4988910 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4988910 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4988910 prefixEnd_4988910 := by exact prefixLift 4988910
  have htrace : WordTrace (prefixWord ++ tailWord_4988910) baseStart_4988910 baseEnd_4988910 := by
    simpa [prefixWord, tailWord_4988910, baseEnd_4988910] using wordTrace_append hprefix tailTrace_4988910
  have hstable : (prefixWord ++ tailWord_4988910).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4988910).length < 2 ^ (prefixWord ++ tailWord_4988910).sum := by decide
  have hdescent : baseEnd_4988910 < baseStart_4988910 := by decide
  rcases family_descends (prefixWord ++ tailWord_4988910) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4988923 : List Nat := [1, 1, 1, 1, 1, 3, 7, 2, 2, 2, 2]
def baseStart_4988923 : Nat := 118140960795 + 4988923 * 2 ^ 59
def prefixEnd_4988923 : Nat := 4983230072969 + 3 ^ 40 * 4988923 * 2
def baseEnd_4988923 : Nat := 2561715447270689549518867

theorem tailTrace_4988923 : CollatzResearch.WordTrace tailWord_4988923 prefixEnd_4988923 2561715447270689549518867 := by
  unfold tailWord_4988923
  simp only [CollatzResearch.WordTrace]
  refine ⟨181960970504991486059123423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121307313669994324039415615 181960970504991486059123423)
  ·
    refine ⟨272941455757487229088685135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 181960970504991486059123423 272941455757487229088685135)
    ·
      refine ⟨409412183636230843633027703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 272941455757487229088685135 409412183636230843633027703)
      ·
        refine ⟨614118275454346265449541555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 409412183636230843633027703 614118275454346265449541555)
        ·
          refine ⟨921177413181519398174312333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 614118275454346265449541555 921177413181519398174312333)
          ·
            refine ⟨345441529943069774315367125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 921177413181519398174312333 345441529943069774315367125)
            ·
              refine ⟨8096285858040697835516417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 345441529943069774315367125 8096285858040697835516417)
              ·
                refine ⟨6072214393530523376637313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8096285858040697835516417 6072214393530523376637313)
                ·
                  refine ⟨4554160795147892532477985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6072214393530523376637313 4554160795147892532477985)
                  ·
                    refine ⟨3415620596360919399358489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4554160795147892532477985 3415620596360919399358489)
                    ·
                      refine ⟨2561715447270689549518867, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3415620596360919399358489 2561715447270689549518867)
                      ·
                        rfl

theorem cell23_4988923_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 7, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 7, 2, 2, 2, 2].length) (baseStart_4988923 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4988923 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4988923 prefixEnd_4988923 := by exact prefixLift 4988923
  have htrace : WordTrace (prefixWord ++ tailWord_4988923) baseStart_4988923 baseEnd_4988923 := by
    simpa [prefixWord, tailWord_4988923, baseEnd_4988923] using wordTrace_append hprefix tailTrace_4988923
  have hstable : (prefixWord ++ tailWord_4988923).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4988923).length < 2 ^ (prefixWord ++ tailWord_4988923).sum := by decide
  have hdescent : baseEnd_4988923 < baseStart_4988923 := by decide
  rcases family_descends (prefixWord ++ tailWord_4988923) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4988929 : List Nat := [1, 2, 4, 1, 2, 1, 4, 1, 7]
def baseStart_4988929 : Nat := 118140960795 + 4988929 * 2 ^ 59
def prefixEnd_4988929 : Nat := 4983230072969 + 3 ^ 40 * 4988929 * 2
def baseEnd_4988929 : Nat := 284635392017179614004871

theorem tailTrace_4988929 : CollatzResearch.WordTrace tailWord_4988929 prefixEnd_4988929 284635392017179614004871 := by
  unfold tailWord_4988929
  simp only [CollatzResearch.WordTrace]
  refine ⟨181961189342969749083841841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121307459561979832722561227 181961189342969749083841841)
  ·
    refine ⟨136470892007227311812881381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 181961189342969749083841841 136470892007227311812881381)
    ·
      refine ⟨25588292251355120964915259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 136470892007227311812881381 25588292251355120964915259)
      ·
        refine ⟨38382438377032681447372889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25588292251355120964915259 38382438377032681447372889)
        ·
          refine ⟨28786828782774511085529667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38382438377032681447372889 28786828782774511085529667)
          ·
            refine ⟨43180243174161766628294501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28786828782774511085529667 43180243174161766628294501)
            ·
              refine ⟨8096295595155331242805219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 43180243174161766628294501 8096295595155331242805219)
              ·
                refine ⟨12144443392732996864207829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8096295595155331242805219 12144443392732996864207829)
                ·
                  refine ⟨284635392017179614004871, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 12144443392732996864207829 284635392017179614004871)
                  ·
                    rfl

theorem cell23_4988929_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 4, 1, 7].length) (baseStart_4988929 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4988929 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4988929 prefixEnd_4988929 := by exact prefixLift 4988929
  have htrace : WordTrace (prefixWord ++ tailWord_4988929) baseStart_4988929 baseEnd_4988929 := by
    simpa [prefixWord, tailWord_4988929, baseEnd_4988929] using wordTrace_append hprefix tailTrace_4988929
  have hstable : (prefixWord ++ tailWord_4988929).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4988929).length < 2 ^ (prefixWord ++ tailWord_4988929).sum := by decide
  have hdescent : baseEnd_4988929 < baseStart_4988929 := by decide
  rcases family_descends (prefixWord ++ tailWord_4988929) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4988934 : List Nat := [6, 2, 1, 2, 1, 2, 1, 1, 1, 3, 3]
def baseStart_4988934 : Nat := 118140960795 + 4988934 * 2 ^ 59
def prefixEnd_4988934 : Nat := 4983230072969 + 3 ^ 40 * 4988934 * 2
def baseEnd_4988934 : Nat := 2561721095557889006481317

theorem tailTrace_4988934 : CollatzResearch.WordTrace tailWord_4988934 prefixEnd_4988934 2561721095557889006481317 := by
  unfold tailWord_4988934
  simp only [CollatzResearch.WordTrace]
  refine ⟨5686292865873488591805433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 121307581138634423291849237 5686292865873488591805433)
  ·
    refine ⟨4264719649405116443854075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5686292865873488591805433 4264719649405116443854075)
    ·
      refine ⟨6397079474107674665781113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4264719649405116443854075 6397079474107674665781113)
      ·
        refine ⟨4797809605580755999335835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6397079474107674665781113 4797809605580755999335835)
        ·
          refine ⟨7196714408371133999003753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4797809605580755999335835 7196714408371133999003753)
          ·
            refine ⟨5397535806278350499252815, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7196714408371133999003753 5397535806278350499252815)
            ·
              refine ⟨8096303709417525748879223, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5397535806278350499252815 8096303709417525748879223)
              ·
                refine ⟨12144455564126288623318835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8096303709417525748879223 12144455564126288623318835)
                ·
                  refine ⟨18216683346189432934978253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12144455564126288623318835 18216683346189432934978253)
                  ·
                    refine ⟨6831256254821037350616845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 18216683346189432934978253 6831256254821037350616845)
                    ·
                      refine ⟨2561721095557889006481317, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6831256254821037350616845 2561721095557889006481317)
                      ·
                        rfl

theorem cell23_4988934_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 2, 1, 2, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 2, 1, 2, 1, 1, 1, 3, 3].length) (baseStart_4988934 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4988934 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4988934 prefixEnd_4988934 := by exact prefixLift 4988934
  have htrace : WordTrace (prefixWord ++ tailWord_4988934) baseStart_4988934 baseEnd_4988934 := by
    simpa [prefixWord, tailWord_4988934, baseEnd_4988934] using wordTrace_append hprefix tailTrace_4988934
  have hstable : (prefixWord ++ tailWord_4988934).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4988934).length < 2 ^ (prefixWord ++ tailWord_4988934).sum := by decide
  have hdescent : baseEnd_4988934 < baseStart_4988934 := by decide
  rcases family_descends (prefixWord ++ tailWord_4988934) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4988939 : List Nat := [1, 1, 1, 1, 6, 1, 1, 3, 2, 3, 3]
def baseStart_4988939 : Nat := 118140960795 + 4988939 * 2 ^ 59
def prefixEnd_4988939 : Nat := 4983230072969 + 3 ^ 40 * 4988939 * 2
def baseEnd_4988939 : Nat := 2561723662961161486918793

theorem tailTrace_4988939 : CollatzResearch.WordTrace tailWord_4988939 prefixEnd_4988939 2561723662961161486918793 := by
  unfold tailWord_4988939
  simp only [CollatzResearch.WordTrace]
  refine ⟨181961554072933520791705871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121307702715289013861137247 181961554072933520791705871)
  ·
    refine ⟨272942331109400281187558807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 181961554072933520791705871 272942331109400281187558807)
    ·
      refine ⟨409413496664100421781338211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 272942331109400281187558807 409413496664100421781338211)
      ·
        refine ⟨614120244996150632672007317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 409413496664100421781338211 614120244996150632672007317)
        ·
          refine ⟨28786886484194560906500343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 614120244996150632672007317 28786886484194560906500343)
          ·
            refine ⟨43180329726291841359750515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28786886484194560906500343 43180329726291841359750515)
            ·
              refine ⟨64770494589437762039625773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 43180329726291841359750515 64770494589437762039625773)
              ·
                refine ⟨24288935471039160764859665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 64770494589437762039625773 24288935471039160764859665)
                ·
                  refine ⟨18216701603279370573644749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 24288935471039160764859665 18216701603279370573644749)
                  ·
                    refine ⟨6831263101229763965116781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 18216701603279370573644749 6831263101229763965116781)
                    ·
                      refine ⟨2561723662961161486918793, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6831263101229763965116781 2561723662961161486918793)
                      ·
                        rfl

theorem cell23_4988939_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 1, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 1, 3, 2, 3, 3].length) (baseStart_4988939 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4988939 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4988939 prefixEnd_4988939 := by exact prefixLift 4988939
  have htrace : WordTrace (prefixWord ++ tailWord_4988939) baseStart_4988939 baseEnd_4988939 := by
    simpa [prefixWord, tailWord_4988939, baseEnd_4988939] using wordTrace_append hprefix tailTrace_4988939
  have hstable : (prefixWord ++ tailWord_4988939).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4988939).length < 2 ^ (prefixWord ++ tailWord_4988939).sum := by decide
  have hdescent : baseEnd_4988939 < baseStart_4988939 := by decide
  rcases family_descends (prefixWord ++ tailWord_4988939) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4988940 : List Nat := [2, 2, 1, 2, 3, 1, 5, 1, 2, 2, 2]
def baseStart_4988940 : Nat := 118140960795 + 4988940 * 2 ^ 59
def prefixEnd_4988940 : Nat := 4983230072969 + 3 ^ 40 * 4988940 * 2
def baseEnd_4988940 : Nat := 2561724176441815983006289

theorem tailTrace_4988940 : CollatzResearch.WordTrace tailWord_4988940 prefixEnd_4988940 2561724176441815983006289 := by
  unfold tailWord_4988940
  simp only [CollatzResearch.WordTrace]
  refine ⟨90980795272964948981246137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 121307727030619931974994849 90980795272964948981246137)
  ·
    refine ⟨68235596454723711735934603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 90980795272964948981246137 68235596454723711735934603)
    ·
      refine ⟨102353394682085567603901905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68235596454723711735934603 102353394682085567603901905)
      ·
        refine ⟨76765046011564175702926429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 102353394682085567603901905 76765046011564175702926429)
        ·
          refine ⟨28786892254336565888597411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 76765046011564175702926429 28786892254336565888597411)
          ·
            refine ⟨43180338381504848832896117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28786892254336565888597411 43180338381504848832896117)
            ·
              refine ⟨4048156723266079578084011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 43180338381504848832896117 4048156723266079578084011)
              ·
                refine ⟨6072235084899119367126017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4048156723266079578084011 6072235084899119367126017)
                ·
                  refine ⟨4554176313674339525344513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6072235084899119367126017 4554176313674339525344513)
                  ·
                    refine ⟨3415632235255754644008385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4554176313674339525344513 3415632235255754644008385)
                    ·
                      refine ⟨2561724176441815983006289, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3415632235255754644008385 2561724176441815983006289)
                      ·
                        rfl

theorem cell23_4988940_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 5, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 5, 1, 2, 2, 2].length) (baseStart_4988940 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4988940 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4988940 prefixEnd_4988940 := by exact prefixLift 4988940
  have htrace : WordTrace (prefixWord ++ tailWord_4988940) baseStart_4988940 baseEnd_4988940 := by
    simpa [prefixWord, tailWord_4988940, baseEnd_4988940] using wordTrace_append hprefix tailTrace_4988940
  have hstable : (prefixWord ++ tailWord_4988940).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4988940).length < 2 ^ (prefixWord ++ tailWord_4988940).sum := by decide
  have hdescent : baseEnd_4988940 < baseStart_4988940 := by decide
  rcases family_descends (prefixWord ++ tailWord_4988940) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4988959 : List Nat := [1, 1, 2, 4, 1, 2, 2, 3, 2, 5]
def baseStart_4988959 : Nat := 118140960795 + 4988959 * 2 ^ 59
def prefixEnd_4988959 : Nat := 4983230072969 + 3 ^ 40 * 4988959 * 2
def baseEnd_4988959 : Nat := 853911310858083802889567

theorem tailTrace_4988959 : CollatzResearch.WordTrace tailWord_4988959 prefixEnd_4988959 853911310858083802889567 := by
  unfold tailWord_4988959
  simp only [CollatzResearch.WordTrace]
  refine ⟨181962283532861064207433931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121308189021907376138289287 181962283532861064207433931)
  ·
    refine ⟨272943425299291596311150897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 181962283532861064207433931 272943425299291596311150897)
    ·
      refine ⟨204707568974468697233363173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 272943425299291596311150897 204707568974468697233363173)
      ·
        refine ⟨38382669182712880731255595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 204707568974468697233363173 38382669182712880731255595)
        ·
          refine ⟨57574003774069321096883393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38382669182712880731255595 57574003774069321096883393)
          ·
            refine ⟨43180502830551990822662545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 57574003774069321096883393 43180502830551990822662545)
            ·
              refine ⟨32385377122913993116996909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 43180502830551990822662545 32385377122913993116996909)
              ·
                refine ⟨12144516421092747418873841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 32385377122913993116996909 12144516421092747418873841)
                ·
                  refine ⟨9108387315819560564155381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12144516421092747418873841 9108387315819560564155381)
                  ·
                    refine ⟨853911310858083802889567, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9108387315819560564155381 853911310858083802889567)
                    ·
                      rfl

theorem cell23_4988959_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 2, 3, 2, 5].length) (baseStart_4988959 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4988959 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4988959 prefixEnd_4988959 := by exact prefixLift 4988959
  have htrace : WordTrace (prefixWord ++ tailWord_4988959) baseStart_4988959 baseEnd_4988959 := by
    simpa [prefixWord, tailWord_4988959, baseEnd_4988959] using wordTrace_append hprefix tailTrace_4988959
  have hstable : (prefixWord ++ tailWord_4988959).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4988959).length < 2 ^ (prefixWord ++ tailWord_4988959).sum := by decide
  have hdescent : baseEnd_4988959 < baseStart_4988959 := by decide
  rcases family_descends (prefixWord ++ tailWord_4988959) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4988979 : List Nat := [1, 1, 1, 2, 4, 1, 3, 1, 4, 1, 4]
def baseStart_4988979 : Nat := 118140960795 + 4988979 * 2 ^ 59
def prefixEnd_4988979 : Nat := 4983230072969 + 3 ^ 40 * 4988979 * 2
def baseEnd_4988979 : Nat := 2561744202187341330418609

theorem tailTrace_4988979 : CollatzResearch.WordTrace tailWord_4988979 prefixEnd_4988979 2561744202187341330418609 := by
  unfold tailWord_4988979
  simp only [CollatzResearch.WordTrace]
  refine ⟨181963012992788607623161991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121308675328525738415441327 181963012992788607623161991)
  ·
    refine ⟨272944519489182911434742987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 181963012992788607623161991 272944519489182911434742987)
    ·
      refine ⟨409416779233774367152114481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 272944519489182911434742987 409416779233774367152114481)
      ·
        refine ⟨307062584425330775364085861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 409416779233774367152114481 307062584425330775364085861)
        ·
          refine ⟨57574234579749520380766099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 307062584425330775364085861 57574234579749520380766099)
          ·
            refine ⟨86361351869624280571149149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 57574234579749520380766099 86361351869624280571149149)
            ·
              refine ⟨32385506951109105214180931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 86361351869624280571149149 32385506951109105214180931)
              ·
                refine ⟨48578260426663657821271397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32385506951109105214180931 48578260426663657821271397)
                ·
                  refine ⟨9108423829999435841488387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 48578260426663657821271397 9108423829999435841488387)
                  ·
                    refine ⟨13662635744999153762232581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9108423829999435841488387 13662635744999153762232581)
                    ·
                      refine ⟨2561744202187341330418609, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13662635744999153762232581 2561744202187341330418609)
                      ·
                        rfl

theorem cell23_4988979_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 3, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 3, 1, 4, 1, 4].length) (baseStart_4988979 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4988979 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4988979 prefixEnd_4988979 := by exact prefixLift 4988979
  have htrace : WordTrace (prefixWord ++ tailWord_4988979) baseStart_4988979 baseEnd_4988979 := by
    simpa [prefixWord, tailWord_4988979, baseEnd_4988979] using wordTrace_append hprefix tailTrace_4988979
  have hstable : (prefixWord ++ tailWord_4988979).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4988979).length < 2 ^ (prefixWord ++ tailWord_4988979).sum := by decide
  have hdescent : baseEnd_4988979 < baseStart_4988979 := by decide
  rcases family_descends (prefixWord ++ tailWord_4988979) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4988980 : List Nat := [2, 5, 1, 2, 3, 1, 1, 1, 7]
def baseStart_4988980 : Nat := 118140960795 + 4988980 * 2 ^ 59
def prefixEnd_4988980 : Nat := 4983230072969 + 3 ^ 40 * 4988980 * 2
def baseEnd_4988980 : Nat := 284638301740888425167345

theorem tailTrace_4988980 : CollatzResearch.WordTrace tailWord_4988980 prefixEnd_4988980 284638301740888425167345 := by
  unfold tailWord_4988980
  simp only [CollatzResearch.WordTrace]
  refine ⟨90981524732892492396974197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 121308699643856656529298929 90981524732892492396974197)
  ·
    refine ⟨8529517943708671162216331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 90981524732892492396974197 8529517943708671162216331)
    ·
      refine ⟨12794276915563006743324497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8529517943708671162216331 12794276915563006743324497)
      ·
        refine ⟨9595707686672255057493373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12794276915563006743324497 9595707686672255057493373)
        ·
          refine ⟨3598390382502095646560015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9595707686672255057493373 3598390382502095646560015)
          ·
            refine ⟨5397585573753143469840023, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3598390382502095646560015 5397585573753143469840023)
            ·
              refine ⟨8096378360629715204760035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5397585573753143469840023 8096378360629715204760035)
              ·
                refine ⟨12144567540944572807140053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8096378360629715204760035 12144567540944572807140053)
                ·
                  refine ⟨284638301740888425167345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 12144567540944572807140053 284638301740888425167345)
                  ·
                    rfl

theorem cell23_4988980_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 3, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 3, 1, 1, 1, 7].length) (baseStart_4988980 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4988980 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4988980 prefixEnd_4988980 := by exact prefixLift 4988980
  have htrace : WordTrace (prefixWord ++ tailWord_4988980) baseStart_4988980 baseEnd_4988980 := by
    simpa [prefixWord, tailWord_4988980, baseEnd_4988980] using wordTrace_append hprefix tailTrace_4988980
  have hstable : (prefixWord ++ tailWord_4988980).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4988980).length < 2 ^ (prefixWord ++ tailWord_4988980).sum := by decide
  have hdescent : baseEnd_4988980 < baseStart_4988980 := by decide
  rcases family_descends (prefixWord ++ tailWord_4988980) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4989016 : List Nat := [2, 1, 2, 2, 1, 4, 1, 3, 2, 2, 3]
def baseStart_4989016 : Nat := 118140960795 + 4989016 * 2 ^ 59
def prefixEnd_4989016 : Nat := 4983230072969 + 3 ^ 40 * 4989016 * 2
def baseEnd_4989016 : Nat := 2561763200971557685655939

theorem tailTrace_4989016 : CollatzResearch.WordTrace tailWord_4989016 prefixEnd_4989016 2561763200971557685655939 := by
  unfold tailWord_4989016
  simp only [CollatzResearch.WordTrace]
  refine ⟨90982181246827281471129451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 121309574995769708628172601 90982181246827281471129451)
  ·
    refine ⟨136473271870240922206694177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90982181246827281471129451 136473271870240922206694177)
    ·
      refine ⟨102354953902680691655020633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 136473271870240922206694177 102354953902680691655020633)
      ·
        refine ⟨76766215427010518741265475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 102354953902680691655020633 76766215427010518741265475)
        ·
          refine ⟨115149323140515778111898213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 76766215427010518741265475 115149323140515778111898213)
          ·
            refine ⟨21590498088846708395980915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 115149323140515778111898213 21590498088846708395980915)
            ·
              refine ⟨32385747133270062593971373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21590498088846708395980915 32385747133270062593971373)
              ·
                refine ⟨12144655174976273472739265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 32385747133270062593971373 12144655174976273472739265)
                ·
                  refine ⟨9108491381232205104554449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12144655174976273472739265 9108491381232205104554449)
                  ·
                    refine ⟨6831368535924153828415837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9108491381232205104554449 6831368535924153828415837)
                    ·
                      refine ⟨2561763200971557685655939, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6831368535924153828415837 2561763200971557685655939)
                      ·
                        rfl

theorem cell23_4989016_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 4, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 4, 1, 3, 2, 2, 3].length) (baseStart_4989016 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4989016 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4989016 prefixEnd_4989016 := by exact prefixLift 4989016
  have htrace : WordTrace (prefixWord ++ tailWord_4989016) baseStart_4989016 baseEnd_4989016 := by
    simpa [prefixWord, tailWord_4989016, baseEnd_4989016] using wordTrace_append hprefix tailTrace_4989016
  have hstable : (prefixWord ++ tailWord_4989016).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4989016).length < 2 ^ (prefixWord ++ tailWord_4989016).sum := by decide
  have hdescent : baseEnd_4989016 < baseStart_4989016 := by decide
  rcases family_descends (prefixWord ++ tailWord_4989016) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
