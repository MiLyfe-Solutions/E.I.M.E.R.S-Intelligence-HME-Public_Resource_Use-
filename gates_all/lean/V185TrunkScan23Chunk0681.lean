import V185TrunkScan23Chunk0680

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_4027012 : List Nat := [2, 3, 2, 1, 3, 1, 3, 2, 1, 5]
def baseStart_4027012 : Nat := 118140960795 + 4027012 * 2 ^ 59
def prefixEnd_4027012 : Nat := 4983230072969 + 3 ^ 40 * 4027012 * 2
def baseEnd_4027012 : Nat := 689264252474567843576705

theorem tailTrace_4027012 : CollatzResearch.WordTrace tailWord_4027012 prefixEnd_4027012 689264252474567843576705 := by
  unfold tailWord_4027012
  simp only [CollatzResearch.WordTrace]
  refine ⟨73438597043415378869713645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97918129391220505159618193 73438597043415378869713645)
  ·
    refine ⟨27539473891280767076142617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 73438597043415378869713645 27539473891280767076142617)
    ·
      refine ⟨20654605418460575307106963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27539473891280767076142617 20654605418460575307106963)
      ·
        refine ⟨30981908127690862960660445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20654605418460575307106963 30981908127690862960660445)
        ·
          refine ⟨11618215547884073610247667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30981908127690862960660445 11618215547884073610247667)
          ·
            refine ⟨17427323321826110415371501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11618215547884073610247667 17427323321826110415371501)
            ·
              refine ⟨6535246245684791405764313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17427323321826110415371501 6535246245684791405764313)
              ·
                refine ⟨4901434684263593554323235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6535246245684791405764313 4901434684263593554323235)
                ·
                  refine ⟨7352152026395390331484853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4901434684263593554323235 7352152026395390331484853)
                  ·
                    refine ⟨689264252474567843576705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7352152026395390331484853 689264252474567843576705)
                    ·
                      rfl

theorem cell23_4027012_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 1, 3, 2, 1, 5].length) (baseStart_4027012 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4027012 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4027012 prefixEnd_4027012 := by exact prefixLift 4027012
  have htrace : WordTrace (prefixWord ++ tailWord_4027012) baseStart_4027012 baseEnd_4027012 := by
    simpa [prefixWord, tailWord_4027012, baseEnd_4027012] using wordTrace_append hprefix tailTrace_4027012
  have hstable : (prefixWord ++ tailWord_4027012).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4027012).length < 2 ^ (prefixWord ++ tailWord_4027012).sum := by decide
  have hdescent : baseEnd_4027012 < baseStart_4027012 := by decide
  rcases family_descends (prefixWord ++ tailWord_4027012) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4027015 : List Nat := [1, 1, 4, 2, 1, 2, 3, 1, 3, 1, 4]
def baseStart_4027015 : Nat := 118140960795 + 4027015 * 2 ^ 59
def prefixEnd_4027015 : Nat := 4983230072969 + 3 ^ 40 * 4027015 * 2
def baseEnd_4027015 : Nat := 2067794297865667018992601

theorem tailTrace_4027015 : CollatzResearch.WordTrace tailWord_4027015 prefixEnd_4027015 2067794297865667018992601 := by
  unfold tailWord_4027015
  simp only [CollatzResearch.WordTrace]
  refine ⟨146877303505819889251786499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97918202337213259501190999 146877303505819889251786499)
  ·
    refine ⟨220315955258729833877679749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146877303505819889251786499 220315955258729833877679749)
    ·
      refine ⟨41309241611011843852064953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 220315955258729833877679749 41309241611011843852064953)
      ·
        refine ⟨30981931208258882889048715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41309241611011843852064953 30981931208258882889048715)
        ·
          refine ⟨46472896812388324333573073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30981931208258882889048715 46472896812388324333573073)
          ·
            refine ⟨34854672609291243250179805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46472896812388324333573073 34854672609291243250179805)
            ·
              refine ⟨13070502228484216218817427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34854672609291243250179805 13070502228484216218817427)
              ·
                refine ⟨19605753342726324328226141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13070502228484216218817427 19605753342726324328226141)
                ·
                  refine ⟨7352157503522371623084803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19605753342726324328226141 7352157503522371623084803)
                  ·
                    refine ⟨11028236255283557434627205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7352157503522371623084803 11028236255283557434627205)
                    ·
                      refine ⟨2067794297865667018992601, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11028236255283557434627205 2067794297865667018992601)
                      ·
                        rfl

theorem cell23_4027015_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 3, 1, 3, 1, 4].length) (baseStart_4027015 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4027015 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4027015 prefixEnd_4027015 := by exact prefixLift 4027015
  have htrace : WordTrace (prefixWord ++ tailWord_4027015) baseStart_4027015 baseEnd_4027015 := by
    simpa [prefixWord, tailWord_4027015, baseEnd_4027015] using wordTrace_append hprefix tailTrace_4027015
  have hstable : (prefixWord ++ tailWord_4027015).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4027015).length < 2 ^ (prefixWord ++ tailWord_4027015).sum := by decide
  have hdescent : baseEnd_4027015 < baseStart_4027015 := by decide
  rcases family_descends (prefixWord ++ tailWord_4027015) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4027055 : List Nat := [1, 1, 2, 1, 2, 7, 1, 8]
def baseStart_4027055 : Nat := 118140960795 + 4027055 * 2 ^ 59
def prefixEnd_4027055 : Nat := 4983230072969 + 3 ^ 40 * 4027055 * 2
def baseEnd_4027055 : Nat := 76585734707105439351571

theorem tailTrace_4027055 : CollatzResearch.WordTrace tailWord_4027055 prefixEnd_4027055 76585734707105439351571 := by
  unfold tailWord_4027055
  simp only [CollatzResearch.WordTrace]
  refine ⟨146878762425674976083242619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97919174950449984055495079 146878762425674976083242619)
  ·
    refine ⟨220318143638512464124863929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146878762425674976083242619 220318143638512464124863929)
    ·
      refine ⟨165238607728884348093647947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 220318143638512464124863929 165238607728884348093647947)
      ·
        refine ⟨247857911593326522140471921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 165238607728884348093647947 247857911593326522140471921)
        ·
          refine ⟨185893433694994891605353941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 247857911593326522140471921 185893433694994891605353941)
          ·
            refine ⟨4356877352226442772000483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 185893433694994891605353941 4356877352226442772000483)
            ·
              refine ⟨6535316028339664158000725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4356877352226442772000483 6535316028339664158000725)
              ·
                refine ⟨76585734707105439351571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 6535316028339664158000725 76585734707105439351571)
                ·
                  rfl

theorem cell23_4027055_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 7, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 7, 1, 8].length) (baseStart_4027055 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4027055 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4027055 prefixEnd_4027055 := by exact prefixLift 4027055
  have htrace : WordTrace (prefixWord ++ tailWord_4027055) baseStart_4027055 baseEnd_4027055 := by
    simpa [prefixWord, tailWord_4027055, baseEnd_4027055] using wordTrace_append hprefix tailTrace_4027055
  have hstable : (prefixWord ++ tailWord_4027055).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4027055).length < 2 ^ (prefixWord ++ tailWord_4027055).sum := by decide
  have hdescent : baseEnd_4027055 < baseStart_4027055 := by decide
  rcases family_descends (prefixWord ++ tailWord_4027055) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4027082 : List Nat := [3, 1, 2, 1, 4, 1, 2, 2, 1, 3, 3]
def baseStart_4027082 : Nat := 118140960795 + 4027082 * 2 ^ 59
def prefixEnd_4027082 : Nat := 4983230072969 + 3 ^ 40 * 4027082 * 2
def baseEnd_4027082 : Nat := 2067828701069518256854793

theorem tailTrace_4027082 : CollatzResearch.WordTrace tailWord_4027082 prefixEnd_4027082 2067828701069518256854793 := by
  unfold tailWord_4027082
  simp only [CollatzResearch.WordTrace]
  refine ⟨36719936799144289923618875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 97919831464384773129650333 36719936799144289923618875)
  ·
    refine ⟨55079905198716434885428313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36719936799144289923618875 55079905198716434885428313)
    ·
      refine ⟨41309928899037326164071235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55079905198716434885428313 41309928899037326164071235)
      ·
        refine ⟨61964893348555989246106853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41309928899037326164071235 61964893348555989246106853)
        ·
          refine ⟨11618417502854247983645035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 61964893348555989246106853 11618417502854247983645035)
          ·
            refine ⟨17427626254281371975467553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11618417502854247983645035 17427626254281371975467553)
            ·
              refine ⟨13070719690711028981600665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17427626254281371975467553 13070719690711028981600665)
              ·
                refine ⟨9803039768033271736200499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13070719690711028981600665 9803039768033271736200499)
                ·
                  refine ⟨14704559652049907604300749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9803039768033271736200499 14704559652049907604300749)
                  ·
                    refine ⟨5514209869518715351612781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14704559652049907604300749 5514209869518715351612781)
                    ·
                      refine ⟨2067828701069518256854793, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5514209869518715351612781 2067828701069518256854793)
                      ·
                        rfl

theorem cell23_4027082_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 1, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 1, 2, 2, 1, 3, 3].length) (baseStart_4027082 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4027082 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4027082 prefixEnd_4027082 := by exact prefixLift 4027082
  have htrace : WordTrace (prefixWord ++ tailWord_4027082) baseStart_4027082 baseEnd_4027082 := by
    simpa [prefixWord, tailWord_4027082, baseEnd_4027082] using wordTrace_append hprefix tailTrace_4027082
  have hstable : (prefixWord ++ tailWord_4027082).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4027082).length < 2 ^ (prefixWord ++ tailWord_4027082).sum := by decide
  have hdescent : baseEnd_4027082 < baseStart_4027082 := by decide
  rcases family_descends (prefixWord ++ tailWord_4027082) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4027086 : List Nat := [4, 1, 1, 1, 3, 4, 2, 1, 1, 2, 3]
def baseStart_4027086 : Nat := 118140960795 + 4027086 * 2 ^ 59
def prefixEnd_4027086 : Nat := 4983230072969 + 3 ^ 40 * 4027086 * 2
def baseEnd_4027086 : Nat := 2067830754992136241204775

theorem tailTrace_4027086 : CollatzResearch.WordTrace tailWord_4027086 prefixEnd_4027086 2067830754992136241204775 := by
  unfold tailWord_4027086
  simp only [CollatzResearch.WordTrace]
  refine ⟨18359986636070333547202639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 97919928725708445585080741 18359986636070333547202639)
  ·
    refine ⟨27539979954105500320803959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18359986636070333547202639 27539979954105500320803959)
    ·
      refine ⟨41309969931158250481205939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27539979954105500320803959 41309969931158250481205939)
      ·
        refine ⟨61964954896737375721808909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41309969931158250481205939 61964954896737375721808909)
        ·
          refine ⟨23236858086276515895678341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 61964954896737375721808909 23236858086276515895678341)
          ·
            refine ⟨4356910891176846730439689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 23236858086276515895678341 4356910891176846730439689)
            ·
              refine ⟨3267683168382635047829767, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4356910891176846730439689 3267683168382635047829767)
              ·
                refine ⟨4901524752573952571744651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3267683168382635047829767 4901524752573952571744651)
                ·
                  refine ⟨7352287128860928857616977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4901524752573952571744651 7352287128860928857616977)
                  ·
                    refine ⟨5514215346645696643212733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7352287128860928857616977 5514215346645696643212733)
                    ·
                      refine ⟨2067830754992136241204775, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5514215346645696643212733 2067830754992136241204775)
                      ·
                        rfl

theorem cell23_4027086_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 4, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 4, 2, 1, 1, 2, 3].length) (baseStart_4027086 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4027086 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4027086 prefixEnd_4027086 := by exact prefixLift 4027086
  have htrace : WordTrace (prefixWord ++ tailWord_4027086) baseStart_4027086 baseEnd_4027086 := by
    simpa [prefixWord, tailWord_4027086, baseEnd_4027086] using wordTrace_append hprefix tailTrace_4027086
  have hstable : (prefixWord ++ tailWord_4027086).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4027086).length < 2 ^ (prefixWord ++ tailWord_4027086).sum := by decide
  have hdescent : baseEnd_4027086 < baseStart_4027086 := by decide
  rcases family_descends (prefixWord ++ tailWord_4027086) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4027093 : List Nat := [1, 3, 2, 5, 2, 1, 1, 2, 2, 4]
def baseStart_4027093 : Nat := 118140960795 + 4027093 * 2 ^ 59
def prefixEnd_4027093 : Nat := 4983230072969 + 3 ^ 40 * 4027093 * 2
def baseEnd_4027093 : Nat := 689278116452239237939081

theorem tailTrace_4027093 : CollatzResearch.WordTrace tailWord_4027093 prefixEnd_4027093 689278116452239237939081 := by
  unfold tailWord_4027093
  simp only [CollatzResearch.WordTrace]
  refine ⟨146880148399537308573125933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97920098933024872382083955 146880148399537308573125933)
  ·
    refine ⟨55080055649826490714922225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 146880148399537308573125933 55080055649826490714922225)
    ·
      refine ⟨41310041737369868036191669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55080055649826490714922225 41310041737369868036191669)
      ·
        refine ⟨3872816412878425128392969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 41310041737369868036191669 3872816412878425128392969)
        ·
          refine ⟨2904612309658818846294727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3872816412878425128392969 2904612309658818846294727)
          ·
            refine ⟨4356918464488228269442091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2904612309658818846294727 4356918464488228269442091)
            ·
              refine ⟨6535377696732342404163137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4356918464488228269442091 6535377696732342404163137)
              ·
                refine ⟨4901533272549256803122353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6535377696732342404163137 4901533272549256803122353)
                ·
                  refine ⟨3676149954411942602341765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4901533272549256803122353 3676149954411942602341765)
                  ·
                    refine ⟨689278116452239237939081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3676149954411942602341765 689278116452239237939081)
                    ·
                      rfl

theorem cell23_4027093_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 5, 2, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 5, 2, 1, 1, 2, 2, 4].length) (baseStart_4027093 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4027093 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4027093 prefixEnd_4027093 := by exact prefixLift 4027093
  have htrace : WordTrace (prefixWord ++ tailWord_4027093) baseStart_4027093 baseEnd_4027093 := by
    simpa [prefixWord, tailWord_4027093, baseEnd_4027093] using wordTrace_append hprefix tailTrace_4027093
  have hstable : (prefixWord ++ tailWord_4027093).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4027093).length < 2 ^ (prefixWord ++ tailWord_4027093).sum := by decide
  have hdescent : baseEnd_4027093 < baseStart_4027093 := by decide
  rcases family_descends (prefixWord ++ tailWord_4027093) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4027126 : List Nat := [5, 1, 1, 1, 1, 2, 4, 2, 1, 3, 2]
def baseStart_4027126 : Nat := 118140960795 + 4027126 * 2 ^ 59
def prefixEnd_4027126 : Nat := 4983230072969 + 3 ^ 40 * 4027126 * 2
def baseEnd_4027126 : Nat := 2067851294218316084704591

theorem tailTrace_4027126 : CollatzResearch.WordTrace tailWord_4027126 prefixEnd_4027126 2067851294218316084704591 := by
  unfold tailWord_4027126
  simp only [CollatzResearch.WordTrace]
  refine ⟨9180084500526109700567327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 97920901338945170139384821 9180084500526109700567327)
  ·
    refine ⟨13770126750789164550850991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9180084500526109700567327 13770126750789164550850991)
    ·
      refine ⟨20655190126183746826276487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13770126750789164550850991 20655190126183746826276487)
      ·
        refine ⟨30982785189275620239414731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20655190126183746826276487 30982785189275620239414731)
        ·
          refine ⟨46474177783913430359122097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30982785189275620239414731 46474177783913430359122097)
          ·
            refine ⟨34855633337935072769341573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46474177783913430359122097 34855633337935072769341573)
            ·
              refine ⟨6535431250862826144251545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 34855633337935072769341573 6535431250862826144251545)
              ·
                refine ⟨4901573438147119608188659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6535431250862826144251545 4901573438147119608188659)
                ·
                  refine ⟨7352360157220679412282989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4901573438147119608188659 7352360157220679412282989)
                  ·
                    refine ⟨2757135058957754779606121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7352360157220679412282989 2757135058957754779606121)
                    ·
                      refine ⟨2067851294218316084704591, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2757135058957754779606121 2067851294218316084704591)
                      ·
                        rfl

theorem cell23_4027126_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 4, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 4, 2, 1, 3, 2].length) (baseStart_4027126 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4027126 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4027126 prefixEnd_4027126 := by exact prefixLift 4027126
  have htrace : WordTrace (prefixWord ++ tailWord_4027126) baseStart_4027126 baseEnd_4027126 := by
    simpa [prefixWord, tailWord_4027126, baseEnd_4027126] using wordTrace_append hprefix tailTrace_4027126
  have hstable : (prefixWord ++ tailWord_4027126).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4027126).length < 2 ^ (prefixWord ++ tailWord_4027126).sum := by decide
  have hdescent : baseEnd_4027126 < baseStart_4027126 := by decide
  rcases family_descends (prefixWord ++ tailWord_4027126) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4027185 : List Nat := [1, 2, 2, 3, 2, 1, 1, 2, 1, 1, 7]
def baseStart_4027185 : Nat := 118140960795 + 4027185 * 2 ^ 59
def prefixEnd_4027185 : Nat := 4983230072969 + 3 ^ 40 * 4027185 * 2
def baseEnd_4027185 : Nat := 2067881589576931353866819

theorem tailTrace_4027185 : CollatzResearch.WordTrace tailWord_4027185 prefixEnd_4027185 2067881589576931353866819 := by
  unfold tailWord_4027185
  simp only [CollatzResearch.WordTrace]
  refine ⟨146883503915204008285475009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97922335943469338856983339 146883503915204008285475009)
  ·
    refine ⟨110162627936403006214106257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 146883503915204008285475009 110162627936403006214106257)
    ·
      refine ⟨82621970952302254660579693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 110162627936403006214106257 82621970952302254660579693)
      ·
        refine ⟨30983239107113345497717385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 82621970952302254660579693 30983239107113345497717385)
        ·
          refine ⟨23237429330335009123288039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30983239107113345497717385 23237429330335009123288039)
          ·
            refine ⟨34856143995502513684932059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23237429330335009123288039 34856143995502513684932059)
            ·
              refine ⟨52284215993253770527398089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34856143995502513684932059 52284215993253770527398089)
              ·
                refine ⟨39213161994940327895548567, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 52284215993253770527398089 39213161994940327895548567)
                ·
                  refine ⟨58819742992410491843322851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39213161994940327895548567 58819742992410491843322851)
                  ·
                    refine ⟨88229614488615737764984277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 58819742992410491843322851 88229614488615737764984277)
                    ·
                      refine ⟨2067881589576931353866819, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 88229614488615737764984277 2067881589576931353866819)
                      ·
                        rfl

theorem cell23_4027185_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 1, 2, 1, 1, 7].length) (baseStart_4027185 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4027185 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4027185 prefixEnd_4027185 := by exact prefixLift 4027185
  have htrace : WordTrace (prefixWord ++ tailWord_4027185) baseStart_4027185 baseEnd_4027185 := by
    simpa [prefixWord, tailWord_4027185, baseEnd_4027185] using wordTrace_append hprefix tailTrace_4027185
  have hstable : (prefixWord ++ tailWord_4027185).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4027185).length < 2 ^ (prefixWord ++ tailWord_4027185).sum := by decide
  have hdescent : baseEnd_4027185 < baseStart_4027185 := by decide
  rcases family_descends (prefixWord ++ tailWord_4027185) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4027192 : List Nat := [2, 1, 2, 1, 3, 2, 4, 1, 2, 5]
def baseStart_4027192 : Nat := 118140960795 + 4027192 * 2 ^ 59
def prefixEnd_4027192 : Nat := 4983230072969 + 3 ^ 40 * 4027192 * 2
def baseEnd_4027192 : Nat := 689295061313837608826429

theorem tailTrace_4027192 : CollatzResearch.WordTrace tailWord_4027192 prefixEnd_4027192 689295061313837608826429 := by
  unfold tailWord_4027192
  simp only [CollatzResearch.WordTrace]
  refine ⟨73441879613089324240489915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97922506150785765653986553 73441879613089324240489915)
  ·
    refine ⟨110162819419633986360734873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73441879613089324240489915 110162819419633986360734873)
    ·
      refine ⟨82622114564725489770551155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 110162819419633986360734873 82622114564725489770551155)
      ·
        refine ⟨123933171847088234655826733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82622114564725489770551155 123933171847088234655826733)
        ·
          refine ⟨46474939442658087995935025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 123933171847088234655826733 46474939442658087995935025)
          ·
            refine ⟨34856204581993565996951269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46474939442658087995935025 34856204581993565996951269)
            ·
              refine ⟨6535538359123793624428363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 34856204581993565996951269 6535538359123793624428363)
              ·
                refine ⟨9803307538685690436642545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6535538359123793624428363 9803307538685690436642545)
                ·
                  refine ⟨7352480654014267827481909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9803307538685690436642545 7352480654014267827481909)
                  ·
                    refine ⟨689295061313837608826429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7352480654014267827481909 689295061313837608826429)
                    ·
                      rfl

theorem cell23_4027192_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 4, 1, 2, 5].length) (baseStart_4027192 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4027192 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4027192 prefixEnd_4027192 := by exact prefixLift 4027192
  have htrace : WordTrace (prefixWord ++ tailWord_4027192) baseStart_4027192 baseEnd_4027192 := by
    simpa [prefixWord, tailWord_4027192, baseEnd_4027192] using wordTrace_append hprefix tailTrace_4027192
  have hstable : (prefixWord ++ tailWord_4027192).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4027192).length < 2 ^ (prefixWord ++ tailWord_4027192).sum := by decide
  have hdescent : baseEnd_4027192 < baseStart_4027192 := by decide
  rcases family_descends (prefixWord ++ tailWord_4027192) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4027232 : List Nat := [2, 1, 1, 3, 3, 1, 2, 2, 1, 4, 3]
def baseStart_4027232 : Nat := 118140960795 + 4027232 * 2 ^ 59
def prefixEnd_4027232 : Nat := 4983230072969 + 3 ^ 40 * 4027232 * 2
def baseEnd_4027232 : Nat := 2067905723167692669979103

theorem tailTrace_4027232 : CollatzResearch.WordTrace tailWord_4027232 prefixEnd_4027232 2067905723167692669979103 := by
  unfold tailWord_4027232
  simp only [CollatzResearch.WordTrace]
  refine ⟨73442609073016867656217975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97923478764022490208290633 73442609073016867656217975)
  ·
    refine ⟨110163913609525301484326963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73442609073016867656217975 110163913609525301484326963)
    ·
      refine ⟨165245870414287952226490445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110163913609525301484326963 165245870414287952226490445)
      ·
        refine ⟨61967201405357982084933917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 165245870414287952226490445 61967201405357982084933917)
        ·
          refine ⟨23237700527009243281850219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 61967201405357982084933917 23237700527009243281850219)
          ·
            refine ⟨34856550790513864922775329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23237700527009243281850219 34856550790513864922775329)
            ·
              refine ⟨26142413092885398692081497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34856550790513864922775329 26142413092885398692081497)
              ·
                refine ⟨19606809819664049019061123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26142413092885398692081497 19606809819664049019061123)
                ·
                  refine ⟨29410214729496073528591685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19606809819664049019061123 29410214729496073528591685)
                  ·
                    refine ⟨5514415261780513786610941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 29410214729496073528591685 5514415261780513786610941)
                    ·
                      refine ⟨2067905723167692669979103, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5514415261780513786610941 2067905723167692669979103)
                      ·
                        rfl

theorem cell23_4027232_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 2, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 2, 2, 1, 4, 3].length) (baseStart_4027232 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4027232 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4027232 prefixEnd_4027232 := by exact prefixLift 4027232
  have htrace : WordTrace (prefixWord ++ tailWord_4027232) baseStart_4027232 baseEnd_4027232 := by
    simpa [prefixWord, tailWord_4027232, baseEnd_4027232] using wordTrace_append hprefix tailTrace_4027232
  have hstable : (prefixWord ++ tailWord_4027232).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4027232).length < 2 ^ (prefixWord ++ tailWord_4027232).sum := by decide
  have hdescent : baseEnd_4027232 < baseStart_4027232 := by decide
  rcases family_descends (prefixWord ++ tailWord_4027232) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4027239 : List Nat := [1, 1, 5, 1, 2, 3, 1, 2, 3, 4]
def baseStart_4027239 : Nat := 118140960795 + 4027239 * 2 ^ 59
def prefixEnd_4027239 : Nat := 4983230072969 + 3 ^ 40 * 4027239 * 2
def baseEnd_4027239 : Nat := 689303105844091380863857

theorem tailTrace_4027239 : CollatzResearch.WordTrace tailWord_4027239 prefixEnd_4027239 689303105844091380863857 := by
  unfold tailWord_4027239
  simp only [CollatzResearch.WordTrace]
  refine ⟨146885473457008375507940771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97923648971338917005293847 146885473457008375507940771)
  ·
    refine ⟨220328210185512563261911157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146885473457008375507940771 220328210185512563261911157)
    ·
      refine ⟨20655769704891802805804171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 220328210185512563261911157 20655769704891802805804171)
      ·
        refine ⟨30983654557337704208706257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20655769704891802805804171 30983654557337704208706257)
        ·
          refine ⟨23237740918003278156529693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30983654557337704208706257 23237740918003278156529693)
          ·
            refine ⟨8714152844251229308698635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23237740918003278156529693 8714152844251229308698635)
            ·
              refine ⟨13071229266376843963047953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8714152844251229308698635 13071229266376843963047953)
              ·
                refine ⟨9803421949782632972285965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13071229266376843963047953 9803421949782632972285965)
                ·
                  refine ⟨3676283231168487364607237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9803421949782632972285965 3676283231168487364607237)
                  ·
                    refine ⟨689303105844091380863857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3676283231168487364607237 689303105844091380863857)
                    ·
                      rfl

theorem cell23_4027239_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 3, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 3, 1, 2, 3, 4].length) (baseStart_4027239 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4027239 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4027239 prefixEnd_4027239 := by exact prefixLift 4027239
  have htrace : WordTrace (prefixWord ++ tailWord_4027239) baseStart_4027239 baseEnd_4027239 := by
    simpa [prefixWord, tailWord_4027239, baseEnd_4027239] using wordTrace_append hprefix tailTrace_4027239
  have hstable : (prefixWord ++ tailWord_4027239).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4027239).length < 2 ^ (prefixWord ++ tailWord_4027239).sum := by decide
  have hdescent : baseEnd_4027239 < baseStart_4027239 := by decide
  rcases family_descends (prefixWord ++ tailWord_4027239) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4027249 : List Nat := [1, 2, 2, 2, 1, 4, 3, 1, 2, 2, 3]
def baseStart_4027249 : Nat := 118140960795 + 4027249 * 2 ^ 59
def prefixEnd_4027249 : Nat := 4983230072969 + 3 ^ 40 * 4027249 * 2
def baseEnd_4027249 : Nat := 2067914452338819103466525

theorem tailTrace_4027249 : CollatzResearch.WordTrace tailWord_4027249 prefixEnd_4027249 2067914452338819103466525 := by
  unfold tailWord_4027249
  simp only [CollatzResearch.WordTrace]
  refine ⟨146885838186972147215804801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97923892124648098143869867 146885838186972147215804801)
  ·
    refine ⟨110164378640229110411853601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 146885838186972147215804801 110164378640229110411853601)
    ·
      refine ⟨82623283980171832808890201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 110164378640229110411853601 82623283980171832808890201)
      ·
        refine ⟨61967462985128874606667651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 82623283980171832808890201 61967462985128874606667651)
        ·
          refine ⟨92951194477693311910001477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61967462985128874606667651 92951194477693311910001477)
          ·
            refine ⟨17428348964567495983125277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 92951194477693311910001477 17428348964567495983125277)
            ·
              refine ⟨6535630861712810993671979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17428348964567495983125277 6535630861712810993671979)
              ·
                refine ⟨9803446292569216490507969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6535630861712810993671979 9803446292569216490507969)
                ·
                  refine ⟨7352584719426912367880977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9803446292569216490507969 7352584719426912367880977)
                  ·
                    refine ⟨5514438539570184275910733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7352584719426912367880977 5514438539570184275910733)
                    ·
                      refine ⟨2067914452338819103466525, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5514438539570184275910733 2067914452338819103466525)
                      ·
                        rfl

theorem cell23_4027249_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 4, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 4, 3, 1, 2, 2, 3].length) (baseStart_4027249 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4027249 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4027249 prefixEnd_4027249 := by exact prefixLift 4027249
  have htrace : WordTrace (prefixWord ++ tailWord_4027249) baseStart_4027249 baseEnd_4027249 := by
    simpa [prefixWord, tailWord_4027249, baseEnd_4027249] using wordTrace_append hprefix tailTrace_4027249
  have hstable : (prefixWord ++ tailWord_4027249).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4027249).length < 2 ^ (prefixWord ++ tailWord_4027249).sum := by decide
  have hdescent : baseEnd_4027249 < baseStart_4027249 := by decide
  rcases family_descends (prefixWord ++ tailWord_4027249) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4027255 : List Nat := [1, 1, 3, 1, 1, 2, 1, 2, 3, 2, 6]
def baseStart_4027255 : Nat := 118140960795 + 4027255 * 2 ^ 59
def prefixEnd_4027255 : Nat := 4983230072969 + 3 ^ 40 * 4027255 * 2
def baseEnd_4027255 : Nat := 2067917533222746079991497

theorem tailTrace_4027255 : CollatzResearch.WordTrace tailWord_4027255 prefixEnd_4027255 2067917533222746079991497 := by
  unfold tailWord_4027255
  simp only [CollatzResearch.WordTrace]
  refine ⟨146886057024950410240523219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97924038016633606827015479 146886057024950410240523219)
  ·
    refine ⟨220329085537425615360784829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146886057024950410240523219 220329085537425615360784829)
    ·
      refine ⟨82623407076534605760294311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 220329085537425615360784829 82623407076534605760294311)
      ·
        refine ⟨123935110614801908640441467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82623407076534605760294311 123935110614801908640441467)
        ·
          refine ⟨185902665922202862960662201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 123935110614801908640441467 185902665922202862960662201)
          ·
            refine ⟨139426999441652147220496651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 185902665922202862960662201 139426999441652147220496651)
            ·
              refine ⟨209140499162478220830744977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 139426999441652147220496651 209140499162478220830744977)
              ·
                refine ⟨156855374371858665623058733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 209140499162478220830744977 156855374371858665623058733)
                ·
                  refine ⟨58820765389446999608647025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 156855374371858665623058733 58820765389446999608647025)
                  ·
                    refine ⟨44115574042085249706485269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 58820765389446999608647025 44115574042085249706485269)
                    ·
                      refine ⟨2067917533222746079991497, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 44115574042085249706485269 2067917533222746079991497)
                      ·
                        rfl

theorem cell23_4027255_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 1, 2, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 1, 2, 3, 2, 6].length) (baseStart_4027255 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4027255 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4027255 prefixEnd_4027255 := by exact prefixLift 4027255
  have htrace : WordTrace (prefixWord ++ tailWord_4027255) baseStart_4027255 baseEnd_4027255 := by
    simpa [prefixWord, tailWord_4027255, baseEnd_4027255] using wordTrace_append hprefix tailTrace_4027255
  have hstable : (prefixWord ++ tailWord_4027255).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4027255).length < 2 ^ (prefixWord ++ tailWord_4027255).sum := by decide
  have hdescent : baseEnd_4027255 < baseStart_4027255 := by decide
  rcases family_descends (prefixWord ++ tailWord_4027255) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4027269 : List Nat := [1, 3, 1, 1, 3, 5, 1, 2, 6]
def baseStart_4027269 : Nat := 118140960795 + 4027269 * 2 ^ 59
def prefixEnd_4027269 : Nat := 4983230072969 + 3 ^ 40 * 4027269 * 2
def baseEnd_4027269 : Nat := 229769413550212113912937

theorem tailTrace_4027269 : CollatzResearch.WordTrace tailWord_4027269 prefixEnd_4027269 229769413550212113912937 := by
  unfold tailWord_4027269
  simp only [CollatzResearch.WordTrace]
  refine ⟨146886567646899690631532861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97924378431266460421021907 146886567646899690631532861)
  ·
    refine ⟨55082462867587383986824823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 146886567646899690631532861 55082462867587383986824823)
    ·
      refine ⟨82623694301381075980237235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55082462867587383986824823 82623694301381075980237235)
      ·
        refine ⟨123935541452071613970355853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82623694301381075980237235 123935541452071613970355853)
        ·
          refine ⟨46475828044526855238883445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 123935541452071613970355853 46475828044526855238883445)
          ·
            refine ⟨4357108879174392678645323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 46475828044526855238883445 4357108879174392678645323)
            ·
              refine ⟨6535663318761589017967985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4357108879174392678645323 6535663318761589017967985)
              ·
                refine ⟨4901747489071191763475989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6535663318761589017967985 4901747489071191763475989)
                ·
                  refine ⟨229769413550212113912937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4901747489071191763475989 229769413550212113912937)
                  ·
                    rfl

theorem cell23_4027269_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 5, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 5, 1, 2, 6].length) (baseStart_4027269 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4027269 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4027269 prefixEnd_4027269 := by exact prefixLift 4027269
  have htrace : WordTrace (prefixWord ++ tailWord_4027269) baseStart_4027269 baseEnd_4027269 := by
    simpa [prefixWord, tailWord_4027269, baseEnd_4027269] using wordTrace_append hprefix tailTrace_4027269
  have hstable : (prefixWord ++ tailWord_4027269).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4027269).length < 2 ^ (prefixWord ++ tailWord_4027269).sum := by decide
  have hdescent : baseEnd_4027269 < baseStart_4027269 := by decide
  rcases family_descends (prefixWord ++ tailWord_4027269) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4027272 : List Nat := [2, 1, 3, 3, 2, 1, 1, 1, 1, 2, 6]
def baseStart_4027272 : Nat := 118140960795 + 4027272 * 2 ^ 59
def prefixEnd_4027272 : Nat := 4983230072969 + 3 ^ 40 * 4027272 * 2
def baseEnd_4027272 : Nat := 2067926262393872513478919

theorem tailTrace_4027272 : CollatzResearch.WordTrace tailWord_4027272 prefixEnd_4027272 2067926262393872513478919 := by
  unfold tailWord_4027272
  simp only [CollatzResearch.WordTrace]
  refine ⟨73443338532944411071946035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97924451377259214762594713 73443338532944411071946035)
  ·
    refine ⟨110165007799416616607919053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73443338532944411071946035 110165007799416616607919053)
    ·
      refine ⟨41311877924781231227969645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 110165007799416616607919053 41311877924781231227969645)
      ·
        refine ⟨15491954221792961710488617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 41311877924781231227969645 15491954221792961710488617)
        ·
          refine ⟨11618965666344721282866463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15491954221792961710488617 11618965666344721282866463)
          ·
            refine ⟨17428448499517081924299695, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11618965666344721282866463 17428448499517081924299695)
            ·
              refine ⟨26142672749275622886449543, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17428448499517081924299695 26142672749275622886449543)
              ·
                refine ⟨39214009123913434329674315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26142672749275622886449543 39214009123913434329674315)
                ·
                  refine ⟨58821013685870151494511473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39214009123913434329674315 58821013685870151494511473)
                  ·
                    refine ⟨44115760264402613620883605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 58821013685870151494511473 44115760264402613620883605)
                    ·
                      refine ⟨2067926262393872513478919, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 44115760264402613620883605 2067926262393872513478919)
                      ·
                        rfl

theorem cell23_4027272_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 1, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 1, 1, 1, 1, 2, 6].length) (baseStart_4027272 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4027272 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4027272 prefixEnd_4027272 := by exact prefixLift 4027272
  have htrace : WordTrace (prefixWord ++ tailWord_4027272) baseStart_4027272 baseEnd_4027272 := by
    simpa [prefixWord, tailWord_4027272, baseEnd_4027272] using wordTrace_append hprefix tailTrace_4027272
  have hstable : (prefixWord ++ tailWord_4027272).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4027272).length < 2 ^ (prefixWord ++ tailWord_4027272).sum := by decide
  have hdescent : baseEnd_4027272 < baseStart_4027272 := by decide
  rcases family_descends (prefixWord ++ tailWord_4027272) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4027319 : List Nat := [1, 1, 3, 1, 3, 1, 4, 3, 1, 1, 4]
def baseStart_4027319 : Nat := 118140960795 + 4027319 * 2 ^ 59
def prefixEnd_4027319 : Nat := 4983230072969 + 3 ^ 40 * 4027319 * 2
def baseEnd_4027319 : Nat := 2067950395984633829591203

theorem tailTrace_4027319 : CollatzResearch.WordTrace tailWord_4027319 prefixEnd_4027319 2067950395984633829591203 := by
  unfold tailWord_4027319
  simp only [CollatzResearch.WordTrace]
  refine ⟨146888391296718549170853011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97925594197812366113902007 146888391296718549170853011)
  ·
    refine ⟨220332586945077823756279517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146888391296718549170853011 220332586945077823756279517)
    ·
      refine ⟨82624720104404183908604819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 220332586945077823756279517 82624720104404183908604819)
      ·
        refine ⟨123937080156606275862907229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82624720104404183908604819 123937080156606275862907229)
        ·
          refine ⟨46476405058727353448590211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 123937080156606275862907229 46476405058727353448590211)
          ·
            refine ⟨69714607588091030172885317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46476405058727353448590211 69714607588091030172885317)
            ·
              refine ⟨13071488922767068157415997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 69714607588091030172885317 13071488922767068157415997)
              ·
                refine ⟨4901808346037650559030999, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13071488922767068157415997 4901808346037650559030999)
                ·
                  refine ⟨7352712519056475838546499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4901808346037650559030999 7352712519056475838546499)
                  ·
                    refine ⟨11029068778584713757819749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7352712519056475838546499 11029068778584713757819749)
                    ·
                      refine ⟨2067950395984633829591203, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11029068778584713757819749 2067950395984633829591203)
                      ·
                        rfl

theorem cell23_4027319_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 4, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 4, 3, 1, 1, 4].length) (baseStart_4027319 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4027319 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4027319 prefixEnd_4027319 := by exact prefixLift 4027319
  have htrace : WordTrace (prefixWord ++ tailWord_4027319) baseStart_4027319 baseEnd_4027319 := by
    simpa [prefixWord, tailWord_4027319, baseEnd_4027319] using wordTrace_append hprefix tailTrace_4027319
  have hstable : (prefixWord ++ tailWord_4027319).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4027319).length < 2 ^ (prefixWord ++ tailWord_4027319).sum := by decide
  have hdescent : baseEnd_4027319 < baseStart_4027319 := by decide
  rcases family_descends (prefixWord ++ tailWord_4027319) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4027342 : List Nat := [4, 1, 1, 1, 2, 3, 1, 10]
def baseStart_4027342 : Nat := 118140960795 + 4027342 * 2 ^ 59
def prefixEnd_4027342 : Nat := 4983230072969 + 3 ^ 40 * 4027342 * 2
def baseEnd_4027342 : Nat := 76591192816284712577911

theorem tailTrace_4027342 : CollatzResearch.WordTrace tailWord_4027342 prefixEnd_4027342 76591192816284712577911 := by
  unfold tailWord_4027342
  simp only [CollatzResearch.WordTrace]
  refine ⟨18361153771954403012367535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 97926153450423482732626853 18361153771954403012367535)
  ·
    refine ⟨27541730657931604518551303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18361153771954403012367535 27541730657931604518551303)
    ·
      refine ⟨41312595986897406777826955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27541730657931604518551303 41312595986897406777826955)
      ·
        refine ⟨61968893980346110166740433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41312595986897406777826955 61968893980346110166740433)
        ·
          refine ⟨46476670485259582625055325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61968893980346110166740433 46476670485259582625055325)
          ·
            refine ⟨17428751431972343484395747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 46476670485259582625055325 17428751431972343484395747)
            ·
              refine ⟨26143127147958515226593621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17428751431972343484395747 26143127147958515226593621)
              ·
                refine ⟨76591192816284712577911, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 26143127147958515226593621 76591192816284712577911)
                ·
                  rfl

theorem cell23_4027342_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 3, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 3, 1, 10].length) (baseStart_4027342 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4027342 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4027342 prefixEnd_4027342 := by exact prefixLift 4027342
  have htrace : WordTrace (prefixWord ++ tailWord_4027342) baseStart_4027342 baseEnd_4027342 := by
    simpa [prefixWord, tailWord_4027342, baseEnd_4027342] using wordTrace_append hprefix tailTrace_4027342
  have hstable : (prefixWord ++ tailWord_4027342).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4027342).length < 2 ^ (prefixWord ++ tailWord_4027342).sum := by decide
  have hdescent : baseEnd_4027342 < baseStart_4027342 := by decide
  rcases family_descends (prefixWord ++ tailWord_4027342) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4027381 : List Nat := [1, 3, 5, 2, 2, 1, 2, 2, 1, 1, 3]
def baseStart_4027381 : Nat := 118140960795 + 4027381 * 2 ^ 59
def prefixEnd_4027381 : Nat := 4983230072969 + 3 ^ 40 * 4027381 * 2
def baseEnd_4027381 : Nat := 2067982231785212587015919

theorem tailTrace_4027381 : CollatzResearch.WordTrace tailWord_4027381 prefixEnd_4027381 2067982231785212587015919 := by
  unfold tailWord_4027381
  simp only [CollatzResearch.WordTrace]
  refine ⟨146890652622493933759609997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97927101748329289173073331 146890652622493933759609997)
  ·
    refine ⟨55083994733435225159853749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 146890652622493933759609997 55083994733435225159853749)
    ·
      refine ⟨5164124506259552358736289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 55083994733435225159853749 5164124506259552358736289)
      ·
        refine ⟨3873093379694664269052217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5164124506259552358736289 3873093379694664269052217)
        ·
          refine ⟨2904820034770998201789163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3873093379694664269052217 2904820034770998201789163)
          ·
            refine ⟨4357230052156497302683745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2904820034770998201789163 4357230052156497302683745)
            ·
              refine ⟨3267922539117372977012809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4357230052156497302683745 3267922539117372977012809)
              ·
                refine ⟨2450941904338029732759607, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3267922539117372977012809 2450941904338029732759607)
                ·
                  refine ⟨3676412856507044599139411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2450941904338029732759607 3676412856507044599139411)
                  ·
                    refine ⟨5514619284760566898709117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3676412856507044599139411 5514619284760566898709117)
                    ·
                      refine ⟨2067982231785212587015919, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5514619284760566898709117 2067982231785212587015919)
                      ·
                        rfl

theorem cell23_4027381_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 2, 2, 1, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 2, 2, 1, 2, 2, 1, 1, 3].length) (baseStart_4027381 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4027381 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4027381 prefixEnd_4027381 := by exact prefixLift 4027381
  have htrace : WordTrace (prefixWord ++ tailWord_4027381) baseStart_4027381 baseEnd_4027381 := by
    simpa [prefixWord, tailWord_4027381, baseEnd_4027381] using wordTrace_append hprefix tailTrace_4027381
  have hstable : (prefixWord ++ tailWord_4027381).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4027381).length < 2 ^ (prefixWord ++ tailWord_4027381).sum := by decide
  have hdescent : baseEnd_4027381 < baseStart_4027381 := by decide
  rcases family_descends (prefixWord ++ tailWord_4027381) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4027410 : List Nat := [3, 2, 5, 1, 1, 1, 3, 7]
def baseStart_4027410 : Nat := 118140960795 + 4027410 * 2 ^ 59
def prefixEnd_4027410 : Nat := 4983230072969 + 3 ^ 40 * 4027410 * 2
def baseEnd_4027410 : Nat := 76592486026821961983455

theorem tailTrace_4027410 : CollatzResearch.WordTrace tailWord_4027410 prefixEnd_4027410 76592486026821961983455 := by
  unfold tailWord_4027410
  simp only [CollatzResearch.WordTrace]
  refine ⟨36722927584847217928103921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 97927806892925914474943789 36722927584847217928103921)
  ·
    refine ⟨27542195688635413446077941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36722927584847217928103921 27542195688635413446077941)
    ·
      refine ⟨2582080845809570010569807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 27542195688635413446077941 2582080845809570010569807)
      ·
        refine ⟨3873121268714355015854711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2582080845809570010569807 3873121268714355015854711)
        ·
          refine ⟨5809681903071532523782067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3873121268714355015854711 5809681903071532523782067)
          ·
            refine ⟨8714522854607298785673101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5809681903071532523782067 8714522854607298785673101)
            ·
              refine ⟨3267946070477737044627413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8714522854607298785673101 3267946070477737044627413)
              ·
                refine ⟨76592486026821961983455, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3267946070477737044627413 76592486026821961983455)
                ·
                  rfl

theorem cell23_4027410_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 5, 1, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 5, 1, 1, 1, 3, 7].length) (baseStart_4027410 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4027410 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4027410 prefixEnd_4027410 := by exact prefixLift 4027410
  have htrace : WordTrace (prefixWord ++ tailWord_4027410) baseStart_4027410 baseEnd_4027410 := by
    simpa [prefixWord, tailWord_4027410, baseEnd_4027410] using wordTrace_append hprefix tailTrace_4027410
  have hstable : (prefixWord ++ tailWord_4027410).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4027410).length < 2 ^ (prefixWord ++ tailWord_4027410).sum := by decide
  have hdescent : baseEnd_4027410 < baseStart_4027410 := by decide
  rcases family_descends (prefixWord ++ tailWord_4027410) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4027449 : List Nat := [1, 2, 1, 5, 2, 1, 1, 3, 7]
def baseStart_4027449 : Nat := 118140960795 + 4027449 * 2 ^ 59
def prefixEnd_4027449 : Nat := 4983230072969 + 3 ^ 40 * 4027449 * 2
def baseEnd_4027449 : Nat := 229779683163302035662845

theorem tailTrace_4027449 : CollatzResearch.WordTrace tailWord_4027449 prefixEnd_4027449 229779683163302035662845 := by
  unfold tailWord_4027449
  simp only [CollatzResearch.WordTrace]
  refine ⟨146893132786247581373085401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97928755190831720915390267 146893132786247581373085401)
  ·
    refine ⟨110169849589685686029814051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 146893132786247581373085401 110169849589685686029814051)
    ·
      refine ⟨165254774384528529044721077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110169849589685686029814051 165254774384528529044721077)
      ·
        refine ⟨15492635098549549597942601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 165254774384528529044721077 15492635098549549597942601)
        ·
          refine ⟨11619476323912162198456951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15492635098549549597942601 11619476323912162198456951)
          ·
            refine ⟨17429214485868243297685427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11619476323912162198456951 17429214485868243297685427)
            ·
              refine ⟨26143821728802364946528141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17429214485868243297685427 26143821728802364946528141)
              ·
                refine ⟨9803933148300886854948053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26143821728802364946528141 9803933148300886854948053)
                ·
                  refine ⟨229779683163302035662845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 9803933148300886854948053 229779683163302035662845)
                  ·
                    rfl

theorem cell23_4027449_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 1, 1, 3, 7].length) (baseStart_4027449 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4027449 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4027449 prefixEnd_4027449 := by exact prefixLift 4027449
  have htrace : WordTrace (prefixWord ++ tailWord_4027449) baseStart_4027449 baseEnd_4027449 := by
    simpa [prefixWord, tailWord_4027449, baseEnd_4027449] using wordTrace_append hprefix tailTrace_4027449
  have hstable : (prefixWord ++ tailWord_4027449).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4027449).length < 2 ^ (prefixWord ++ tailWord_4027449).sum := by decide
  have hdescent : baseEnd_4027449 < baseStart_4027449 := by decide
  rcases family_descends (prefixWord ++ tailWord_4027449) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4027459 : List Nat := [1, 1, 1, 3, 1, 2, 3, 3, 2, 3, 3]
def baseStart_4027459 : Nat := 118140960795 + 4027459 * 2 ^ 59
def prefixEnd_4027459 : Nat := 4983230072969 + 3 ^ 40 * 4027459 * 2
def baseEnd_4027459 : Nat := 2068022283276263281840559

theorem tailTrace_4027459 : CollatzResearch.WordTrace tailWord_4027459 prefixEnd_4027459 2068022283276263281840559 := by
  unfold tailWord_4027459
  simp only [CollatzResearch.WordTrace]
  refine ⟨146893497516211353080949431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97928998344140902053966287 146893497516211353080949431)
  ·
    refine ⟨220340246274317029621424147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146893497516211353080949431 220340246274317029621424147)
    ·
      refine ⟨330510369411475544432136221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 220340246274317029621424147 330510369411475544432136221)
      ·
        refine ⟨123941388529303329162051083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 330510369411475544432136221 123941388529303329162051083)
        ·
          refine ⟨185912082793954993743076625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 123941388529303329162051083 185912082793954993743076625)
          ·
            refine ⟨139434062095466245307307469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 185912082793954993743076625 139434062095466245307307469)
            ·
              refine ⟨52287773285799841990240301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 139434062095466245307307469 52287773285799841990240301)
              ·
                refine ⟨19607914982174940746340113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 52287773285799841990240301 19607914982174940746340113)
                ·
                  refine ⟨14705936236631205559755085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19607914982174940746340113 14705936236631205559755085)
                  ·
                    refine ⟨5514726088736702084908157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14705936236631205559755085 5514726088736702084908157)
                    ·
                      refine ⟨2068022283276263281840559, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5514726088736702084908157 2068022283276263281840559)
                      ·
                        rfl

theorem cell23_4027459_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 3, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 3, 3, 2, 3, 3].length) (baseStart_4027459 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4027459 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4027459 prefixEnd_4027459 := by exact prefixLift 4027459
  have htrace : WordTrace (prefixWord ++ tailWord_4027459) baseStart_4027459 baseEnd_4027459 := by
    simpa [prefixWord, tailWord_4027459, baseEnd_4027459] using wordTrace_append hprefix tailTrace_4027459
  have hstable : (prefixWord ++ tailWord_4027459).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4027459).length < 2 ^ (prefixWord ++ tailWord_4027459).sum := by decide
  have hdescent : baseEnd_4027459 < baseStart_4027459 := by decide
  rcases family_descends (prefixWord ++ tailWord_4027459) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4027479 : List Nat := [1, 1, 3, 2, 2, 1, 1, 5, 2, 5]
def baseStart_4027479 : Nat := 118140960795 + 4027479 * 2 ^ 59
def prefixEnd_4027479 : Nat := 4983230072969 + 3 ^ 40 * 4027479 * 2
def baseEnd_4027479 : Nat := 689344184296451067863489

theorem tailTrace_4027479 : CollatzResearch.WordTrace tailWord_4027479 prefixEnd_4027479 689344184296451067863489 := by
  unfold tailWord_4027479
  simp only [CollatzResearch.WordTrace]
  refine ⟨146894226976138896496677491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97929484650759264331118327 146894226976138896496677491)
  ·
    refine ⟨220341340464208344745016237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146894226976138896496677491 220341340464208344745016237)
    ·
      refine ⟨82628002674078129279381089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 220341340464208344745016237 82628002674078129279381089)
      ·
        refine ⟨61971002005558596959535817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 82628002674078129279381089 61971002005558596959535817)
        ·
          refine ⟨46478251504168947719651863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61971002005558596959535817 46478251504168947719651863)
          ·
            refine ⟨69717377256253421579477795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46478251504168947719651863 69717377256253421579477795)
            ·
              refine ⟨104576065884380132369216693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 69717377256253421579477795 104576065884380132369216693)
              ·
                refine ⟨9804006176660637409614065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 104576065884380132369216693 9804006176660637409614065)
                ·
                  refine ⟨7353004632495478057210549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9804006176660637409614065 7353004632495478057210549)
                  ·
                    refine ⟨689344184296451067863489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7353004632495478057210549 689344184296451067863489)
                    ·
                      rfl

theorem cell23_4027479_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 1, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 1, 5, 2, 5].length) (baseStart_4027479 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4027479 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4027479 prefixEnd_4027479 := by exact prefixLift 4027479
  have htrace : WordTrace (prefixWord ++ tailWord_4027479) baseStart_4027479 baseEnd_4027479 := by
    simpa [prefixWord, tailWord_4027479, baseEnd_4027479] using wordTrace_append hprefix tailTrace_4027479
  have hstable : (prefixWord ++ tailWord_4027479).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4027479).length < 2 ^ (prefixWord ++ tailWord_4027479).sum := by decide
  have hdescent : baseEnd_4027479 < baseStart_4027479 := by decide
  rcases family_descends (prefixWord ++ tailWord_4027479) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4027516 : List Nat := [2, 2, 2, 1, 1, 3, 2, 1, 1, 6, 2]
def baseStart_4027516 : Nat := 118140960795 + 4027516 * 2 ^ 59
def prefixEnd_4027516 : Nat := 4983230072969 + 3 ^ 40 * 4027516 * 2
def baseEnd_4027516 : Nat := 2068051551673569558827797

theorem tailTrace_4027516 : CollatzResearch.WordTrace tailWord_4027516 prefixEnd_4027516 2068051551673569558827797 := by
  unfold tailWord_4027516
  simp only [CollatzResearch.WordTrace]
  refine ⟨73447788238502425907887201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97930384318003234543849601 73447788238502425907887201)
  ·
    refine ⟨55085841178876819430915401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73447788238502425907887201 55085841178876819430915401)
    ·
      refine ⟨41314380884157614573186551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55085841178876819430915401 41314380884157614573186551)
      ·
        refine ⟨61971571326236421859779827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41314380884157614573186551 61971571326236421859779827)
        ·
          refine ⟨92957356989354632789669741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61971571326236421859779827 92957356989354632789669741)
          ·
            refine ⟨34859008871007987296126153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 92957356989354632789669741 34859008871007987296126153)
            ·
              refine ⟨26144256653255990472094615, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34859008871007987296126153 26144256653255990472094615)
              ·
                refine ⟨39216384979883985708141923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26144256653255990472094615 39216384979883985708141923)
                ·
                  refine ⟨58824577469825978562212885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39216384979883985708141923 58824577469825978562212885)
                  ·
                    refine ⟨2757402068898092745103729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 58824577469825978562212885 2757402068898092745103729)
                    ·
                      refine ⟨2068051551673569558827797, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2757402068898092745103729 2068051551673569558827797)
                      ·
                        rfl

theorem cell23_4027516_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 2, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 2, 1, 1, 6, 2].length) (baseStart_4027516 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4027516 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4027516 prefixEnd_4027516 := by exact prefixLift 4027516
  have htrace : WordTrace (prefixWord ++ tailWord_4027516) baseStart_4027516 baseEnd_4027516 := by
    simpa [prefixWord, tailWord_4027516, baseEnd_4027516] using wordTrace_append hprefix tailTrace_4027516
  have hstable : (prefixWord ++ tailWord_4027516).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4027516).length < 2 ^ (prefixWord ++ tailWord_4027516).sum := by decide
  have hdescent : baseEnd_4027516 < baseStart_4027516 := by decide
  rcases family_descends (prefixWord ++ tailWord_4027516) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4027556 : List Nat := [2, 3, 1, 2, 3, 1, 1, 4, 6]
def baseStart_4027556 : Nat := 118140960795 + 4027556 * 2 ^ 59
def prefixEnd_4027556 : Nat := 4983230072969 + 3 ^ 40 * 4027556 * 2
def baseEnd_4027556 : Nat := 229785787877749933591957

theorem tailTrace_4027556 : CollatzResearch.WordTrace tailWord_4027556 prefixEnd_4027556 229785787877749933591957 := by
  unfold tailWord_4027556
  simp only [CollatzResearch.WordTrace]
  refine ⟨73448517698429969323615261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97931356931239959098153681 73448517698429969323615261)
  ·
    refine ⟨27543194136911238496355723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 73448517698429969323615261 27543194136911238496355723)
    ·
      refine ⟨41314791205366857744533585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27543194136911238496355723 41314791205366857744533585)
      ·
        refine ⟨30986093404025143308400189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41314791205366857744533585 30986093404025143308400189)
        ·
          refine ⟨11619785026509428740650071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30986093404025143308400189 11619785026509428740650071)
          ·
            refine ⟨17429677539764143110975107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11619785026509428740650071 17429677539764143110975107)
            ·
              refine ⟨26144516309646214666462661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17429677539764143110975107 26144516309646214666462661)
              ·
                refine ⟨4902096808058665249961749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 26144516309646214666462661 4902096808058665249961749)
                ·
                  refine ⟨229785787877749933591957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4902096808058665249961749 229785787877749933591957)
                  ·
                    rfl

theorem cell23_4027556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 1, 1, 4, 6].length) (baseStart_4027556 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4027556 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4027556 prefixEnd_4027556 := by exact prefixLift 4027556
  have htrace : WordTrace (prefixWord ++ tailWord_4027556) baseStart_4027556 baseEnd_4027556 := by
    simpa [prefixWord, tailWord_4027556, baseEnd_4027556] using wordTrace_append hprefix tailTrace_4027556
  have hstable : (prefixWord ++ tailWord_4027556).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4027556).length < 2 ^ (prefixWord ++ tailWord_4027556).sum := by decide
  have hdescent : baseEnd_4027556 < baseStart_4027556 := by decide
  rcases family_descends (prefixWord ++ tailWord_4027556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4027599 : List Nat := [1, 1, 2, 1, 1, 3, 2, 3, 3, 6]
def baseStart_4027599 : Nat := 118140960795 + 4027599 * 2 ^ 59
def prefixEnd_4027599 : Nat := 4983230072969 + 3 ^ 40 * 4027599 * 2
def baseEnd_4027599 : Nat := 689364723522630911363305

theorem tailTrace_4027599 : CollatzResearch.WordTrace tailWord_4027599 prefixEnd_4027599 689364723522630911363305 := by
  unfold tailWord_4027599
  simp only [CollatzResearch.WordTrace]
  refine ⟨146898603735704156991045851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97932402490469437994030567 146898603735704156991045851)
  ·
    refine ⟨220347905603556235486568777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146898603735704156991045851 220347905603556235486568777)
    ·
      refine ⟨165260929202667176614926583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 220347905603556235486568777 165260929202667176614926583)
      ·
        refine ⟨247891393804000764922389875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 165260929202667176614926583 247891393804000764922389875)
        ·
          refine ⟨371837090706001147383584813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 247891393804000764922389875 371837090706001147383584813)
          ·
            refine ⟨139438909014750430268844305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 371837090706001147383584813 139438909014750430268844305)
            ·
              refine ⟨104579181761062822701633229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 139438909014750430268844305 104579181761062822701633229)
              ·
                refine ⟨39217193160398558513112461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 104579181761062822701633229 39217193160398558513112461)
                ·
                  refine ⟨14706447435149459442417173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 39217193160398558513112461 14706447435149459442417173)
                  ·
                    refine ⟨689364723522630911363305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 14706447435149459442417173 689364723522630911363305)
                    ·
                      rfl

theorem cell23_4027599_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 2, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 2, 3, 3, 6].length) (baseStart_4027599 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4027599 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4027599 prefixEnd_4027599 := by exact prefixLift 4027599
  have htrace : WordTrace (prefixWord ++ tailWord_4027599) baseStart_4027599 baseEnd_4027599 := by
    simpa [prefixWord, tailWord_4027599, baseEnd_4027599] using wordTrace_append hprefix tailTrace_4027599
  have hstable : (prefixWord ++ tailWord_4027599).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4027599).length < 2 ^ (prefixWord ++ tailWord_4027599).sum := by decide
  have hdescent : baseEnd_4027599 < baseStart_4027599 := by decide
  rcases family_descends (prefixWord ++ tailWord_4027599) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4027626 : List Nat := [3, 1, 3, 1, 1, 3, 1, 1, 3, 1, 5]
def baseStart_4027626 : Nat := 118140960795 + 4027626 * 2 ^ 59
def prefixEnd_4027626 : Nat := 4983230072969 + 3 ^ 40 * 4027626 * 2
def baseEnd_4027626 : Nat := 2068108034545564128452291

theorem tailTrace_4027626 : CollatzResearch.WordTrace tailWord_4027626 prefixEnd_4027626 2068108034545564128452291 := by
  unfold tailWord_4027626
  simp only [CollatzResearch.WordTrace]
  refine ⟨36724897126651585150569683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 97933059004404227068185821 36724897126651585150569683)
  ·
    refine ⟨55087345689977377725854525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36724897126651585150569683 55087345689977377725854525)
    ·
      refine ⟨20657754633741516647195447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 55087345689977377725854525 20657754633741516647195447)
      ·
        refine ⟨30986631950612274970793171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20657754633741516647195447 30986631950612274970793171)
        ·
          refine ⟨46479947925918412456189757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30986631950612274970793171 46479947925918412456189757)
          ·
            refine ⟨17429980472219404671071159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 46479947925918412456189757 17429980472219404671071159)
            ·
              refine ⟨26144970708329107006606739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17429980472219404671071159 26144970708329107006606739)
              ·
                refine ⟨39217456062493660509910109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26144970708329107006606739 39217456062493660509910109)
                ·
                  refine ⟨14706546023435122691216291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 39217456062493660509910109 14706546023435122691216291)
                  ·
                    refine ⟨22059819035152684036824437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14706546023435122691216291 22059819035152684036824437)
                    ·
                      refine ⟨2068108034545564128452291, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 22059819035152684036824437 2068108034545564128452291)
                      ·
                        rfl

theorem cell23_4027626_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 3, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 3, 1, 1, 3, 1, 5].length) (baseStart_4027626 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4027626 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4027626 prefixEnd_4027626 := by exact prefixLift 4027626
  have htrace : WordTrace (prefixWord ++ tailWord_4027626) baseStart_4027626 baseEnd_4027626 := by
    simpa [prefixWord, tailWord_4027626, baseEnd_4027626] using wordTrace_append hprefix tailTrace_4027626
  have hstable : (prefixWord ++ tailWord_4027626).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4027626).length < 2 ^ (prefixWord ++ tailWord_4027626).sum := by decide
  have hdescent : baseEnd_4027626 < baseStart_4027626 := by decide
  rcases family_descends (prefixWord ++ tailWord_4027626) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4027639 : List Nat := [1, 1, 3, 1, 1, 1, 2, 2, 2, 2, 7]
def baseStart_4027639 : Nat := 118140960795 + 4027639 * 2 ^ 59
def prefixEnd_4027639 : Nat := 4983230072969 + 3 ^ 40 * 4027639 * 2
def baseEnd_4027639 : Nat := 2068114709794072577589731

theorem tailTrace_4027639 : CollatzResearch.WordTrace tailWord_4027639 prefixEnd_4027639 2068114709794072577589731 := by
  unfold tailWord_4027639
  simp only [CollatzResearch.WordTrace]
  refine ⟨146900062655559243822501971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97933375103706162548334647 146900062655559243822501971)
  ·
    refine ⟨220350093983338865733752957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146900062655559243822501971 220350093983338865733752957)
    ·
      refine ⟨82631285243752074650157359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 220350093983338865733752957 82631285243752074650157359)
      ·
        refine ⟨123946927865628111975236039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82631285243752074650157359 123946927865628111975236039)
        ·
          refine ⟨185920391798442167962854059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 123946927865628111975236039 185920391798442167962854059)
          ·
            refine ⟨278880587697663251944281089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 185920391798442167962854059 278880587697663251944281089)
            ·
              refine ⟨209160440773247438958210817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 278880587697663251944281089 209160440773247438958210817)
              ·
                refine ⟨156870330579935579218658113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 209160440773247438958210817 156870330579935579218658113)
                ·
                  refine ⟨117652747934951684413993585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 156870330579935579218658113 117652747934951684413993585)
                  ·
                    refine ⟨88239560951213763310495189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 117652747934951684413993585 88239560951213763310495189)
                    ·
                      refine ⟨2068114709794072577589731, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 88239560951213763310495189 2068114709794072577589731)
                      ·
                        rfl

theorem cell23_4027639_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 2, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 2, 2, 2, 2, 7].length) (baseStart_4027639 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4027639 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4027639 prefixEnd_4027639 := by exact prefixLift 4027639
  have htrace : WordTrace (prefixWord ++ tailWord_4027639) baseStart_4027639 baseEnd_4027639 := by
    simpa [prefixWord, tailWord_4027639, baseEnd_4027639] using wordTrace_append hprefix tailTrace_4027639
  have hstable : (prefixWord ++ tailWord_4027639).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4027639).length < 2 ^ (prefixWord ++ tailWord_4027639).sum := by decide
  have hdescent : baseEnd_4027639 < baseStart_4027639 := by decide
  rcases family_descends (prefixWord ++ tailWord_4027639) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4027725 : List Nat := [1, 6, 1, 3, 1, 2, 2, 2, 1, 2, 2]
def baseStart_4027725 : Nat := 118140960795 + 4027725 * 2 ^ 59
def prefixEnd_4027725 : Nat := 4983230072969 + 3 ^ 40 * 4027725 * 2
def baseEnd_4027725 : Nat := 2068158869130359241114337

theorem tailTrace_4027725 : CollatzResearch.WordTrace tailWord_4027725 prefixEnd_4027725 2068158869130359241114337 := by
  unfold tailWord_4027725
  simp only [CollatzResearch.WordTrace]
  refine ⟨146903199333247680510132629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97935466222165120340088419 146903199333247680510132629)
  ·
    refine ⟨6886087468745985023912467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 146903199333247680510132629 6886087468745985023912467)
    ·
      refine ⟨10329131203118977535868701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6886087468745985023912467 10329131203118977535868701)
      ·
        refine ⟨3873424201169616575950763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10329131203118977535868701 3873424201169616575950763)
        ·
          refine ⟨5810136301754424863926145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3873424201169616575950763 5810136301754424863926145)
          ·
            refine ⟨4357602226315818647944609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5810136301754424863926145 4357602226315818647944609)
            ·
              refine ⟨3268201669736863985958457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4357602226315818647944609 3268201669736863985958457)
              ·
                refine ⟨2451151252302647989468843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3268201669736863985958457 2451151252302647989468843)
                ·
                  refine ⟨3676726878453971984203265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2451151252302647989468843 3676726878453971984203265)
                  ·
                    refine ⟨2757545158840478988152449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3676726878453971984203265 2757545158840478988152449)
                    ·
                      refine ⟨2068158869130359241114337, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2757545158840478988152449 2068158869130359241114337)
                      ·
                        rfl

theorem cell23_4027725_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 3, 1, 2, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 3, 1, 2, 2, 2, 1, 2, 2].length) (baseStart_4027725 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4027725 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4027725 prefixEnd_4027725 := by exact prefixLift 4027725
  have htrace : WordTrace (prefixWord ++ tailWord_4027725) baseStart_4027725 baseEnd_4027725 := by
    simpa [prefixWord, tailWord_4027725, baseEnd_4027725] using wordTrace_append hprefix tailTrace_4027725
  have hstable : (prefixWord ++ tailWord_4027725).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4027725).length < 2 ^ (prefixWord ++ tailWord_4027725).sum := by decide
  have hdescent : baseEnd_4027725 < baseStart_4027725 := by decide
  rcases family_descends (prefixWord ++ tailWord_4027725) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4027733 : List Nat := [1, 3, 2, 2, 3, 1, 1, 1, 2, 4, 3]
def baseStart_4027733 : Nat := 118140960795 + 4027733 * 2 ^ 59
def prefixEnd_4027733 : Nat := 4983230072969 + 3 ^ 40 * 4027733 * 2
def baseEnd_4027733 : Nat := 2068162976975595209814299

theorem tailTrace_4027733 : CollatzResearch.WordTrace tailWord_4027733 prefixEnd_4027733 2068162976975595209814299 := by
  unfold tailWord_4027733
  simp only [CollatzResearch.WordTrace]
  refine ⟨146903491117218697876423853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97935660744812465250949235 146903491117218697876423853)
  ·
    refine ⟨55088809168957011703658945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 146903491117218697876423853 55088809168957011703658945)
    ·
      refine ⟨41316606876717758777744209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55088809168957011703658945 41316606876717758777744209)
      ·
        refine ⟨30987455157538319083308157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41316606876717758777744209 30987455157538319083308157)
        ·
          refine ⟨11620295684076869656240559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30987455157538319083308157 11620295684076869656240559)
          ·
            refine ⟨17430443526115304484360839, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11620295684076869656240559 17430443526115304484360839)
            ·
              refine ⟨26145665289172956726541259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17430443526115304484360839 26145665289172956726541259)
              ·
                refine ⟨39218497933759435089811889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26145665289172956726541259 39218497933759435089811889)
                ·
                  refine ⟨29413873450319576317358917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 39218497933759435089811889 29413873450319576317358917)
                  ·
                    refine ⟨5515101271934920559504797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 29413873450319576317358917 5515101271934920559504797)
                    ·
                      refine ⟨2068162976975595209814299, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5515101271934920559504797 2068162976975595209814299)
                      ·
                        rfl

theorem cell23_4027733_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 1, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 1, 1, 1, 2, 4, 3].length) (baseStart_4027733 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4027733 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4027733 prefixEnd_4027733 := by exact prefixLift 4027733
  have htrace : WordTrace (prefixWord ++ tailWord_4027733) baseStart_4027733 baseEnd_4027733 := by
    simpa [prefixWord, tailWord_4027733, baseEnd_4027733] using wordTrace_append hprefix tailTrace_4027733
  have hstable : (prefixWord ++ tailWord_4027733).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4027733).length < 2 ^ (prefixWord ++ tailWord_4027733).sum := by decide
  have hdescent : baseEnd_4027733 < baseStart_4027733 := by decide
  rcases family_descends (prefixWord ++ tailWord_4027733) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4027736 : List Nat := [2, 1, 2, 2, 1, 1, 4, 3, 7]
def baseStart_4027736 : Nat := 118140960795 + 4027736 * 2 ^ 59
def prefixEnd_4027736 : Nat := 4983230072969 + 3 ^ 40 * 4027736 * 2
def baseEnd_4027736 : Nat := 229796057490839855341865

theorem tailTrace_4027736 : CollatzResearch.WordTrace tailWord_4027736 prefixEnd_4027736 229796057490839855341865 := by
  unfold tailWord_4027736
  simp only [CollatzResearch.WordTrace]
  refine ⟨73451800268103914694391531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97935733690805219592522041 73451800268103914694391531)
  ·
    refine ⟨110177700402155872041587297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73451800268103914694391531 110177700402155872041587297)
    ·
      refine ⟨82633275301616904031190473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 110177700402155872041587297 82633275301616904031190473)
      ·
        refine ⟨61974956476212678023392855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 82633275301616904031190473 61974956476212678023392855)
        ·
          refine ⟨92962434714319017035089283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61974956476212678023392855 92962434714319017035089283)
          ·
            refine ⟨139443652071478525552633925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 92962434714319017035089283 139443652071478525552633925)
            ·
              refine ⟨26145684763402223541118861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 139443652071478525552633925 26145684763402223541118861)
              ·
                refine ⟨9804631786275833827919573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26145684763402223541118861 9804631786275833827919573)
                ·
                  refine ⟨229796057490839855341865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 9804631786275833827919573 229796057490839855341865)
                  ·
                    rfl

theorem cell23_4027736_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 4, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 4, 3, 7].length) (baseStart_4027736 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4027736 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4027736 prefixEnd_4027736 := by exact prefixLift 4027736
  have htrace : WordTrace (prefixWord ++ tailWord_4027736) baseStart_4027736 baseEnd_4027736 := by
    simpa [prefixWord, tailWord_4027736, baseEnd_4027736] using wordTrace_append hprefix tailTrace_4027736
  have hstable : (prefixWord ++ tailWord_4027736).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4027736).length < 2 ^ (prefixWord ++ tailWord_4027736).sum := by decide
  have hdescent : baseEnd_4027736 < baseStart_4027736 := by decide
  rcases family_descends (prefixWord ++ tailWord_4027736) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4027747 : List Nat := [1, 1, 1, 5, 2, 2, 2, 3, 2, 2, 2]
def baseStart_4027747 : Nat := 118140960795 + 4027747 * 2 ^ 59
def prefixEnd_4027747 : Nat := 4983230072969 + 3 ^ 40 * 4027747 * 2
def baseEnd_4027747 : Nat := 2068170165704758155039235

theorem tailTrace_4027747 : CollatzResearch.WordTrace tailWord_4027747 prefixEnd_4027747 2068170165704758155039235 := by
  unfold tailWord_4027747
  simp only [CollatzResearch.WordTrace]
  refine ⟨146904001739167978267433495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97936001159445318844955663 146904001739167978267433495)
  ·
    refine ⟨220356002608751967401150243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146904001739167978267433495 220356002608751967401150243)
    ·
      refine ⟨330534003913127951101725365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 220356002608751967401150243 330534003913127951101725365)
      ·
        refine ⟨30987562866855745415786753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 330534003913127951101725365 30987562866855745415786753)
        ·
          refine ⟨23240672150141809061840065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30987562866855745415786753 23240672150141809061840065)
          ·
            refine ⟨17430504112606356796380049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23240672150141809061840065 17430504112606356796380049)
            ·
              refine ⟨13072878084454767597285037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17430504112606356796380049 13072878084454767597285037)
              ·
                refine ⟨4902329281670537848981889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13072878084454767597285037 4902329281670537848981889)
                ·
                  refine ⟨3676746961252903386736417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4902329281670537848981889 3676746961252903386736417)
                  ·
                    refine ⟨2757560220939677540052313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3676746961252903386736417 2757560220939677540052313)
                    ·
                      refine ⟨2068170165704758155039235, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2757560220939677540052313 2068170165704758155039235)
                      ·
                        rfl

theorem cell23_4027747_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 2, 2, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 2, 2, 3, 2, 2, 2].length) (baseStart_4027747 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4027747 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4027747 prefixEnd_4027747 := by exact prefixLift 4027747
  have htrace : WordTrace (prefixWord ++ tailWord_4027747) baseStart_4027747 baseEnd_4027747 := by
    simpa [prefixWord, tailWord_4027747, baseEnd_4027747] using wordTrace_append hprefix tailTrace_4027747
  have hstable : (prefixWord ++ tailWord_4027747).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4027747).length < 2 ^ (prefixWord ++ tailWord_4027747).sum := by decide
  have hdescent : baseEnd_4027747 < baseStart_4027747 := by decide
  rcases family_descends (prefixWord ++ tailWord_4027747) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4027776 : List Nat := [2, 1, 1, 2, 1, 2, 1, 3, 3, 2, 5]
def baseStart_4027776 : Nat := 118140960795 + 4027776 * 2 ^ 59
def prefixEnd_4027776 : Nat := 4983230072969 + 3 ^ 40 * 4027776 * 2
def baseEnd_4027776 : Nat := 2068185056643738541576601

theorem tailTrace_4027776 : CollatzResearch.WordTrace tailWord_4027776 prefixEnd_4027776 2068185056643738541576601 := by
  unfold tailWord_4027776
  simp only [CollatzResearch.WordTrace]
  refine ⟨73452529728031458110119591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97936706304041944146826121 73452529728031458110119591)
  ·
    refine ⟨110178794592047187165179387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73452529728031458110119591 110178794592047187165179387)
    ·
      refine ⟨165268191888070780747769081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110178794592047187165179387 165268191888070780747769081)
      ·
        refine ⟨123951143916053085560826811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 165268191888070780747769081 123951143916053085560826811)
        ·
          refine ⟨185926715874079628341240217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 123951143916053085560826811 185926715874079628341240217)
          ·
            refine ⟨139445036905559721255930163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 185926715874079628341240217 139445036905559721255930163)
            ·
              refine ⟨209167555358339581883895245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 139445036905559721255930163 209167555358339581883895245)
              ·
                refine ⟨78437833259377343206460717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 209167555358339581883895245 78437833259377343206460717)
                ·
                  refine ⟨29414187472266503702422769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 78437833259377343206460717 29414187472266503702422769)
                  ·
                    refine ⟨22060640604199877776817077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 29414187472266503702422769 22060640604199877776817077)
                    ·
                      refine ⟨2068185056643738541576601, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 22060640604199877776817077 2068185056643738541576601)
                      ·
                        rfl

theorem cell23_4027776_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 1, 3, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 1, 3, 3, 2, 5].length) (baseStart_4027776 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4027776 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4027776 prefixEnd_4027776 := by exact prefixLift 4027776
  have htrace : WordTrace (prefixWord ++ tailWord_4027776) baseStart_4027776 baseEnd_4027776 := by
    simpa [prefixWord, tailWord_4027776, baseEnd_4027776] using wordTrace_append hprefix tailTrace_4027776
  have hstable : (prefixWord ++ tailWord_4027776).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4027776).length < 2 ^ (prefixWord ++ tailWord_4027776).sum := by decide
  have hdescent : baseEnd_4027776 < baseStart_4027776 := by decide
  rcases family_descends (prefixWord ++ tailWord_4027776) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4027813 : List Nat := [1, 3, 1, 2, 1, 1, 2, 3, 5, 4]
def baseStart_4027813 : Nat := 118140960795 + 4027813 * 2 ^ 59
def prefixEnd_4027813 : Nat := 4983230072969 + 3 ^ 40 * 4027813 * 2
def baseEnd_4027813 : Nat := 689401351809318298937977

theorem tailTrace_4027813 : CollatzResearch.WordTrace tailWord_4027813 prefixEnd_4027813 689401351809318298937977 := by
  unfold tailWord_4027813
  simp only [CollatzResearch.WordTrace]
  refine ⟨146906408956928871539336093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97937605971285914359557395 146906408956928871539336093)
  ·
    refine ⟨55089903358848326827251035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 146906408956928871539336093 55089903358848326827251035)
    ·
      refine ⟨82634855038272490240876553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55089903358848326827251035 82634855038272490240876553)
      ·
        refine ⟨61976141278704367680657415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 82634855038272490240876553 61976141278704367680657415)
        ·
          refine ⟨92964211918056551520986123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61976141278704367680657415 92964211918056551520986123)
          ·
            refine ⟨139446317877084827281479185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 92964211918056551520986123 139446317877084827281479185)
            ·
              refine ⟨104584738407813620461109389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 139446317877084827281479185 104584738407813620461109389)
              ·
                refine ⟨39219276902930107672916021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 104584738407813620461109389 39219276902930107672916021)
                ·
                  refine ⟨3676807209649697594335877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 39219276902930107672916021 3676807209649697594335877)
                  ·
                    refine ⟨689401351809318298937977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3676807209649697594335877 689401351809318298937977)
                    ·
                      rfl

theorem cell23_4027813_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 2, 3, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 2, 3, 5, 4].length) (baseStart_4027813 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4027813 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4027813 prefixEnd_4027813 := by exact prefixLift 4027813
  have htrace : WordTrace (prefixWord ++ tailWord_4027813) baseStart_4027813 baseEnd_4027813 := by
    simpa [prefixWord, tailWord_4027813, baseEnd_4027813] using wordTrace_append hprefix tailTrace_4027813
  have hstable : (prefixWord ++ tailWord_4027813).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4027813).length < 2 ^ (prefixWord ++ tailWord_4027813).sum := by decide
  have hdescent : baseEnd_4027813 < baseStart_4027813 := by decide
  rcases family_descends (prefixWord ++ tailWord_4027813) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4027823 : List Nat := [1, 1, 2, 1, 2, 2, 1, 2, 6, 2, 3]
def baseStart_4027823 : Nat := 118140960795 + 4027823 * 2 ^ 59
def prefixEnd_4027823 : Nat := 4983230072969 + 3 ^ 40 * 4027823 * 2
def baseEnd_4027823 : Nat := 2068209190234499857688885

theorem tailTrace_4027823 : CollatzResearch.WordTrace tailWord_4027823 prefixEnd_4027823 2068209190234499857688885 := by
  unfold tailWord_4027823
  simp only [CollatzResearch.WordTrace]
  refine ⟨146906773686892643247200123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97937849124595095498133415 146906773686892643247200123)
  ·
    refine ⟨220360160530338964870800185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146906773686892643247200123 220360160530338964870800185)
    ·
      refine ⟨165270120397754223653100139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 220360160530338964870800185 165270120397754223653100139)
      ·
        refine ⟨247905180596631335479650209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 165270120397754223653100139 247905180596631335479650209)
        ·
          refine ⟨185928885447473501609737657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 247905180596631335479650209 185928885447473501609737657)
          ·
            refine ⟨139446664085605126207303243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 185928885447473501609737657 139446664085605126207303243)
            ·
              refine ⟨209169996128407689310954865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 139446664085605126207303243 209169996128407689310954865)
              ·
                refine ⟨156877497096305766983216149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 209169996128407689310954865 156877497096305766983216149)
                ·
                  refine ⟨7353632676389332827338257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 156877497096305766983216149 7353632676389332827338257)
                  ·
                    refine ⟨5515224507291999620503693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7353632676389332827338257 5515224507291999620503693)
                    ·
                      refine ⟨2068209190234499857688885, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5515224507291999620503693 2068209190234499857688885)
                      ·
                        rfl

theorem cell23_4027823_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 1, 2, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 1, 2, 6, 2, 3].length) (baseStart_4027823 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4027823 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4027823 prefixEnd_4027823 := by exact prefixLift 4027823
  have htrace : WordTrace (prefixWord ++ tailWord_4027823) baseStart_4027823 baseEnd_4027823 := by
    simpa [prefixWord, tailWord_4027823, baseEnd_4027823] using wordTrace_append hprefix tailTrace_4027823
  have hstable : (prefixWord ++ tailWord_4027823).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4027823).length < 2 ^ (prefixWord ++ tailWord_4027823).sum := by decide
  have hdescent : baseEnd_4027823 < baseStart_4027823 := by decide
  rcases family_descends (prefixWord ++ tailWord_4027823) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4027913 : List Nat := [1, 2, 1, 1, 3, 1, 4, 1, 3, 1, 5]
def baseStart_4027913 : Nat := 118140960795 + 4027913 * 2 ^ 59
def prefixEnd_4027913 : Nat := 4983230072969 + 3 ^ 40 * 4027913 * 2
def baseEnd_4027913 : Nat := 2068255403493404505563471

theorem tailTrace_4027913 : CollatzResearch.WordTrace tailWord_4027913 prefixEnd_4027913 2068255403493404505563471 := by
  unfold tailWord_4027913
  simp only [CollatzResearch.WordTrace]
  refine ⟨146910056256566588617976393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97940037504377725745317595 146910056256566588617976393)
  ·
    refine ⟨110182542192424941463482295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 146910056256566588617976393 110182542192424941463482295)
    ·
      refine ⟨165273813288637412195223443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110182542192424941463482295 165273813288637412195223443)
      ·
        refine ⟨247910719932956118292835165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 165273813288637412195223443 247910719932956118292835165)
        ·
          refine ⟨92966519974858544359813187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 247910719932956118292835165 92966519974858544359813187)
          ·
            refine ⟨139449779962287816539719781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 92966519974858544359813187 139449779962287816539719781)
            ·
              refine ⟨26146833742928965601197459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 139449779962287816539719781 26146833742928965601197459)
              ·
                refine ⟨39220250614393448401796189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26146833742928965601197459 39220250614393448401796189)
                ·
                  refine ⟨14707593980397543150673571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 39220250614393448401796189 14707593980397543150673571)
                  ·
                    refine ⟨22061390970596314726010357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14707593980397543150673571 22061390970596314726010357)
                    ·
                      refine ⟨2068255403493404505563471, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 22061390970596314726010357 2068255403493404505563471)
                      ·
                        rfl

theorem cell23_4027913_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 4, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 4, 1, 3, 1, 5].length) (baseStart_4027913 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4027913 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4027913 prefixEnd_4027913 := by exact prefixLift 4027913
  have htrace : WordTrace (prefixWord ++ tailWord_4027913) baseStart_4027913 baseEnd_4027913 := by
    simpa [prefixWord, tailWord_4027913, baseEnd_4027913] using wordTrace_append hprefix tailTrace_4027913
  have hstable : (prefixWord ++ tailWord_4027913).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4027913).length < 2 ^ (prefixWord ++ tailWord_4027913).sum := by decide
  have hdescent : baseEnd_4027913 < baseStart_4027913 := by decide
  rcases family_descends (prefixWord ++ tailWord_4027913) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4027944 : List Nat := [2, 1, 5, 2, 2, 1, 1, 3, 1, 1, 4]
def baseStart_4027944 : Nat := 118140960795 + 4027944 * 2 ^ 59
def prefixEnd_4027944 : Nat := 4983230072969 + 3 ^ 40 * 4027944 * 2
def baseEnd_4027944 : Nat := 2068271321393693884275829

theorem tailTrace_4027944 : CollatzResearch.WordTrace tailWord_4027944 prefixEnd_4027944 2068271321393693884275829 := by
  unfold tailWord_4027944
  simp only [CollatzResearch.WordTrace]
  refine ⟨73455593459727140456177443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97940791279636187274903257 73455593459727140456177443)
  ·
    refine ⟨110183390189590710684266165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73455593459727140456177443 110183390189590710684266165)
    ·
      refine ⟨10329692830274129126649953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 110183390189590710684266165 10329692830274129126649953)
      ·
        refine ⟨7747269622705596844987465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10329692830274129126649953 7747269622705596844987465)
        ·
          refine ⟨5810452217029197633740599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7747269622705596844987465 5810452217029197633740599)
          ·
            refine ⟨8715678325543796450610899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5810452217029197633740599 8715678325543796450610899)
            ·
              refine ⟨13073517488315694675916349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8715678325543796450610899 13073517488315694675916349)
              ·
                refine ⟨4902569058118385503468631, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13073517488315694675916349 4902569058118385503468631)
                ·
                  refine ⟨7353853587177578255202947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4902569058118385503468631 7353853587177578255202947)
                  ·
                    refine ⟨11030780380766367382804421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7353853587177578255202947 11030780380766367382804421)
                    ·
                      refine ⟨2068271321393693884275829, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11030780380766367382804421 2068271321393693884275829)
                      ·
                        rfl

theorem cell23_4027944_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 2, 1, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 2, 1, 1, 3, 1, 1, 4].length) (baseStart_4027944 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4027944 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4027944 prefixEnd_4027944 := by exact prefixLift 4027944
  have htrace : WordTrace (prefixWord ++ tailWord_4027944) baseStart_4027944 baseEnd_4027944 := by
    simpa [prefixWord, tailWord_4027944, baseEnd_4027944] using wordTrace_append hprefix tailTrace_4027944
  have hstable : (prefixWord ++ tailWord_4027944).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4027944).length < 2 ^ (prefixWord ++ tailWord_4027944).sum := by decide
  have hdescent : baseEnd_4027944 < baseStart_4027944 := by decide
  rcases family_descends (prefixWord ++ tailWord_4027944) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4027950 : List Nat := [4, 1, 3, 1, 2, 2, 10]
def baseStart_4027950 : Nat := 118140960795 + 4027950 * 2 ^ 59
def prefixEnd_4027950 : Nat := 4983230072969 + 3 ^ 40 * 4027950 * 2
def baseEnd_4027950 : Nat := 25534251879970627911121

theorem tailTrace_4027950 : CollatzResearch.WordTrace tailWord_4027950 prefixEnd_4027950 25534251879970627911121 := by
  unfold tailWord_4027950
  simp only [CollatzResearch.WordTrace]
  refine ⟨18363925719679067992134163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 97940937171621695958048869 18363925719679067992134163)
  ·
    refine ⟨27545888579518601988201245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18363925719679067992134163 27545888579518601988201245)
    ·
      refine ⟨10329708217319475745575467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27545888579518601988201245 10329708217319475745575467)
      ·
        refine ⟨15494562325979213618363201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10329708217319475745575467 15494562325979213618363201)
        ·
          refine ⟨11620921744484410213772401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15494562325979213618363201 11620921744484410213772401)
          ·
            refine ⟨8715691308363307660329301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11620921744484410213772401 8715691308363307660329301)
            ·
              refine ⟨25534251879970627911121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 8715691308363307660329301 25534251879970627911121)
              ·
                rfl

theorem cell23_4027950_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 2, 10].length) (baseStart_4027950 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4027950 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4027950 prefixEnd_4027950 := by exact prefixLift 4027950
  have htrace : WordTrace (prefixWord ++ tailWord_4027950) baseStart_4027950 baseEnd_4027950 := by
    simpa [prefixWord, tailWord_4027950, baseEnd_4027950] using wordTrace_append hprefix tailTrace_4027950
  have hstable : (prefixWord ++ tailWord_4027950).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4027950).length < 2 ^ (prefixWord ++ tailWord_4027950).sum := by decide
  have hdescent : baseEnd_4027950 < baseStart_4027950 := by decide
  rcases family_descends (prefixWord ++ tailWord_4027950) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4027953 : List Nat := [1, 2, 2, 3, 1, 1, 1, 2, 2, 2, 6]
def baseStart_4027953 : Nat := 118140960795 + 4027953 * 2 ^ 59
def prefixEnd_4027953 : Nat := 4983230072969 + 3 ^ 40 * 4027953 * 2
def baseEnd_4027953 : Nat := 2068275942719584349063287

theorem tailTrace_4027953 : CollatzResearch.WordTrace tailWord_4027953 prefixEnd_4027953 2068275942719584349063287 := by
  unfold tailWord_4027953
  simp only [CollatzResearch.WordTrace]
  refine ⟨146911515176421675449432513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97941010117614450299621675 146911515176421675449432513)
  ·
    refine ⟨110183636382316256587074385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 146911515176421675449432513 110183636382316256587074385)
    ·
      refine ⟨82637727286737192440305789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 110183636382316256587074385 82637727286737192440305789)
      ·
        refine ⟨30989147732526447165114671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 82637727286737192440305789 30989147732526447165114671)
        ·
          refine ⟨46483721598789670747672007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30989147732526447165114671 46483721598789670747672007)
          ·
            refine ⟨69725582398184506121508011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46483721598789670747672007 69725582398184506121508011)
            ·
              refine ⟨104588373597276759182262017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 69725582398184506121508011 104588373597276759182262017)
              ·
                refine ⟨78441280197957569386696513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 104588373597276759182262017 78441280197957569386696513)
                ·
                  refine ⟨58830960148468177040022385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 78441280197957569386696513 58830960148468177040022385)
                  ·
                    refine ⟨44123220111351132780016789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 58830960148468177040022385 44123220111351132780016789)
                    ·
                      refine ⟨2068275942719584349063287, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 44123220111351132780016789 2068275942719584349063287)
                      ·
                        rfl

theorem cell23_4027953_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 1, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 1, 2, 2, 2, 6].length) (baseStart_4027953 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4027953 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4027953 prefixEnd_4027953 := by exact prefixLift 4027953
  have htrace : WordTrace (prefixWord ++ tailWord_4027953) baseStart_4027953 baseEnd_4027953 := by
    simpa [prefixWord, tailWord_4027953, baseEnd_4027953] using wordTrace_append hprefix tailTrace_4027953
  have hstable : (prefixWord ++ tailWord_4027953).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4027953).length < 2 ^ (prefixWord ++ tailWord_4027953).sum := by decide
  have hdescent : baseEnd_4027953 < baseStart_4027953 := by decide
  rcases family_descends (prefixWord ++ tailWord_4027953) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4027961 : List Nat := [1, 2, 1, 5, 1, 2, 2, 4, 1, 2, 2]
def baseStart_4027961 : Nat := 118140960795 + 4027961 * 2 ^ 59
def prefixEnd_4027961 : Nat := 4983230072969 + 3 ^ 40 * 4027961 * 2
def baseEnd_4027961 : Nat := 2068280050564820317763251

theorem tailTrace_4027961 : CollatzResearch.WordTrace tailWord_4027961 prefixEnd_4027961 2068280050564820317763251 := by
  unfold tailWord_4027961
  simp only [CollatzResearch.WordTrace]
  refine ⟨146911806960392692815723737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97941204640261795210482491 146911806960392692815723737)
  ·
    refine ⟨110183855220294519611792803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 146911806960392692815723737 110183855220294519611792803)
    ·
      refine ⟨165275782830441779417689205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110183855220294519611792803 165275782830441779417689205)
      ·
        refine ⟨15494604640353916820408363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 165275782830441779417689205 15494604640353916820408363)
        ·
          refine ⟨23241906960530875230612545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15494604640353916820408363 23241906960530875230612545)
          ·
            refine ⟨17431430220398156422959409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23241906960530875230612545 17431430220398156422959409)
            ·
              refine ⟨13073572665298617317219557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17431430220398156422959409 13073572665298617317219557)
              ·
                refine ⟨2451294874743490746978667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13073572665298617317219557 2451294874743490746978667)
                ·
                  refine ⟨3676942312115236120468001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2451294874743490746978667 3676942312115236120468001)
                  ·
                    refine ⟨2757706734086427090351001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3676942312115236120468001 2757706734086427090351001)
                    ·
                      refine ⟨2068280050564820317763251, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2757706734086427090351001 2068280050564820317763251)
                      ·
                        rfl

theorem cell23_4027961_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 2, 2, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 2, 2, 4, 1, 2, 2].length) (baseStart_4027961 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4027961 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4027961 prefixEnd_4027961 := by exact prefixLift 4027961
  have htrace : WordTrace (prefixWord ++ tailWord_4027961) baseStart_4027961 baseEnd_4027961 := by
    simpa [prefixWord, tailWord_4027961, baseEnd_4027961] using wordTrace_append hprefix tailTrace_4027961
  have hstable : (prefixWord ++ tailWord_4027961).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4027961).length < 2 ^ (prefixWord ++ tailWord_4027961).sum := by decide
  have hdescent : baseEnd_4027961 < baseStart_4027961 := by decide
  rcases family_descends (prefixWord ++ tailWord_4027961) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4027974 : List Nat := [6, 1, 1, 1, 3, 1, 1, 1, 1, 1, 6]
def baseStart_4027974 : Nat := 118140960795 + 4027974 * 2 ^ 59
def prefixEnd_4027974 : Nat := 4983230072969 + 3 ^ 40 * 4027974 * 2
def baseEnd_4027974 : Nat := 2068286725813328766900691

theorem tailTrace_4027974 : CollatzResearch.WordTrace tailWord_4027974 prefixEnd_4027974 2068286725813328766900691 := by
  unfold tailWord_4027974
  simp only [CollatzResearch.WordTrace]
  refine ⟨4591008784667049876123343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 97941520739563730690631317 4591008784667049876123343)
  ·
    refine ⟨6886513177000574814185015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4591008784667049876123343 6886513177000574814185015)
    ·
      refine ⟨10329769765500862221277523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6886513177000574814185015 10329769765500862221277523)
      ·
        refine ⟨15494654648251293331916285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10329769765500862221277523 15494654648251293331916285)
        ·
          refine ⟨5810495493094234999468607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15494654648251293331916285 5810495493094234999468607)
          ·
            refine ⟨8715743239641352499202911, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5810495493094234999468607 8715743239641352499202911)
            ·
              refine ⟨13073614859462028748804367, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8715743239641352499202911 13073614859462028748804367)
              ·
                refine ⟨19610422289193043123206551, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13073614859462028748804367 19610422289193043123206551)
                ·
                  refine ⟨29415633433789564684809827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19610422289193043123206551 29415633433789564684809827)
                  ·
                    refine ⟨44123450150684347027214741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 29415633433789564684809827 44123450150684347027214741)
                    ·
                      refine ⟨2068286725813328766900691, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 44123450150684347027214741 2068286725813328766900691)
                      ·
                        rfl

theorem cell23_4027974_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 3, 1, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 3, 1, 1, 1, 1, 1, 6].length) (baseStart_4027974 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4027974 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4027974 prefixEnd_4027974 := by exact prefixLift 4027974
  have htrace : WordTrace (prefixWord ++ tailWord_4027974) baseStart_4027974 baseEnd_4027974 := by
    simpa [prefixWord, tailWord_4027974, baseEnd_4027974] using wordTrace_append hprefix tailTrace_4027974
  have hstable : (prefixWord ++ tailWord_4027974).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4027974).length < 2 ^ (prefixWord ++ tailWord_4027974).sum := by decide
  have hdescent : baseEnd_4027974 < baseStart_4027974 := by decide
  rcases family_descends (prefixWord ++ tailWord_4027974) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4027977 : List Nat := [1, 2, 1, 1, 2, 2, 1, 7, 2, 1, 3]
def baseStart_4027977 : Nat := 118140960795 + 4027977 * 2 ^ 59
def prefixEnd_4027977 : Nat := 4983230072969 + 3 ^ 40 * 4027977 * 2
def baseEnd_4027977 : Nat := 2068288266255292255163177

theorem tailTrace_4027977 : CollatzResearch.WordTrace tailWord_4027977 prefixEnd_4027977 2068288266255292255163177 := by
  unfold tailWord_4027977
  simp only [CollatzResearch.WordTrace]
  refine ⟨146912390528334727548306185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97941593685556485032204123 146912390528334727548306185)
  ·
    refine ⟨110184292896251045661229639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 146912390528334727548306185 110184292896251045661229639)
    ·
      refine ⟨165276439344376568491844459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110184292896251045661229639 165276439344376568491844459)
      ·
        refine ⟨247914659016564852737766689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 165276439344376568491844459 247914659016564852737766689)
        ·
          refine ⟨185935994262423639553325017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 247914659016564852737766689 185935994262423639553325017)
          ·
            refine ⟨139451995696817729664993763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 185935994262423639553325017 139451995696817729664993763)
            ·
              refine ⟨209177993545226594497490645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 139451995696817729664993763 209177993545226594497490645)
              ·
                refine ⟨4902609223716248308534937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 209177993545226594497490645 4902609223716248308534937)
                ·
                  refine ⟨3676956917787186231401203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4902609223716248308534937 3676956917787186231401203)
                  ·
                    refine ⟨5515435376680779347101805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3676956917787186231401203 5515435376680779347101805)
                    ·
                      refine ⟨2068288266255292255163177, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5515435376680779347101805 2068288266255292255163177)
                      ·
                        rfl

theorem cell23_4027977_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 1, 7, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 1, 7, 2, 1, 3].length) (baseStart_4027977 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4027977 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4027977 prefixEnd_4027977 := by exact prefixLift 4027977
  have htrace : WordTrace (prefixWord ++ tailWord_4027977) baseStart_4027977 baseEnd_4027977 := by
    simpa [prefixWord, tailWord_4027977, baseEnd_4027977] using wordTrace_append hprefix tailTrace_4027977
  have hstable : (prefixWord ++ tailWord_4027977).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4027977).length < 2 ^ (prefixWord ++ tailWord_4027977).sum := by decide
  have hdescent : baseEnd_4027977 < baseStart_4027977 := by decide
  rcases family_descends (prefixWord ++ tailWord_4027977) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4027981 : List Nat := [1, 6, 1, 1, 3, 1, 2, 2, 1, 2, 3]
def baseStart_4027981 : Nat := 118140960795 + 4027981 * 2 ^ 59
def prefixEnd_4027981 : Nat := 4983230072969 + 3 ^ 40 * 4027981 * 2
def baseEnd_4027981 : Nat := 2068290320177910239513159

theorem tailTrace_4027981 : CollatzResearch.WordTrace tailWord_4027981 prefixEnd_4027981 2068290320177910239513159 := by
  unfold tailWord_4027981
  simp only [CollatzResearch.WordTrace]
  refine ⟨146912536420320236231451797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97941690946880157487634531 146912536420320236231451797)
  ·
    refine ⟨6886525144702511073349303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 146912536420320236231451797 6886525144702511073349303)
    ·
      refine ⟨10329787717053766610023955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6886525144702511073349303 10329787717053766610023955)
      ·
        refine ⟨15494681575580649915035933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10329787717053766610023955 15494681575580649915035933)
        ·
          refine ⟨5810505590842743718138475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15494681575580649915035933 5810505590842743718138475)
          ·
            refine ⟨8715758386264115577207713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5810505590842743718138475 8715758386264115577207713)
            ·
              refine ⟨6536818789698086682905785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8715758386264115577207713 6536818789698086682905785)
              ·
                refine ⟨4902614092273565012179339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6536818789698086682905785 4902614092273565012179339)
                ·
                  refine ⟨7353921138410347518269009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4902614092273565012179339 7353921138410347518269009)
                  ·
                    refine ⟨5515440853807760638701757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7353921138410347518269009 5515440853807760638701757)
                    ·
                      refine ⟨2068290320177910239513159, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5515440853807760638701757 2068290320177910239513159)
                      ·
                        rfl

theorem cell23_4027981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 3, 1, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 3, 1, 2, 2, 1, 2, 3].length) (baseStart_4027981 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4027981 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4027981 prefixEnd_4027981 := by exact prefixLift 4027981
  have htrace : WordTrace (prefixWord ++ tailWord_4027981) baseStart_4027981 baseEnd_4027981 := by
    simpa [prefixWord, tailWord_4027981, baseEnd_4027981] using wordTrace_append hprefix tailTrace_4027981
  have hstable : (prefixWord ++ tailWord_4027981).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4027981).length < 2 ^ (prefixWord ++ tailWord_4027981).sum := by decide
  have hdescent : baseEnd_4027981 < baseStart_4027981 := by decide
  rcases family_descends (prefixWord ++ tailWord_4027981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4027993 : List Nat := [1, 2, 1, 2, 2, 1, 1, 4, 1, 8]
def baseStart_4027993 : Nat := 118140960795 + 4027993 * 2 ^ 59
def prefixEnd_4027993 : Nat := 4983230072969 + 3 ^ 40 * 4027993 * 2
def baseEnd_4027993 : Nat := 689432160648588064187701

theorem tailTrace_4027993 : CollatzResearch.WordTrace tailWord_4027993 prefixEnd_4027993 689432160648588064187701 := by
  unfold tailWord_4027993
  simp only [CollatzResearch.WordTrace]
  refine ⟨146912974096276762280888633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97941982730851174853925755 146912974096276762280888633)
  ·
    refine ⟨110184730572207571710666475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 146912974096276762280888633 110184730572207571710666475)
    ·
      refine ⟨165277095858311357565999713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110184730572207571710666475 165277095858311357565999713)
      ·
        refine ⟨123957821893733518174499785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 165277095858311357565999713 123957821893733518174499785)
        ·
          refine ⟨92968366420300138630874839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 123957821893733518174499785 92968366420300138630874839)
          ·
            refine ⟨139452549630450207946312259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 92968366420300138630874839 139452549630450207946312259)
            ·
              refine ⟨209178824445675311919468389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 139452549630450207946312259 209178824445675311919468389)
              ·
                refine ⟨39221029583564120984900323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 209178824445675311919468389 39221029583564120984900323)
                ·
                  refine ⟨58831544375346181477350485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39221029583564120984900323 58831544375346181477350485)
                  ·
                    refine ⟨689432160648588064187701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 58831544375346181477350485 689432160648588064187701)
                    ·
                      rfl

theorem cell23_4027993_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 1, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 1, 4, 1, 8].length) (baseStart_4027993 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4027993 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4027993 prefixEnd_4027993 := by exact prefixLift 4027993
  have htrace : WordTrace (prefixWord ++ tailWord_4027993) baseStart_4027993 baseEnd_4027993 := by
    simpa [prefixWord, tailWord_4027993, baseEnd_4027993] using wordTrace_append hprefix tailTrace_4027993
  have hstable : (prefixWord ++ tailWord_4027993).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4027993).length < 2 ^ (prefixWord ++ tailWord_4027993).sum := by decide
  have hdescent : baseEnd_4027993 < baseStart_4027993 := by decide
  rcases family_descends (prefixWord ++ tailWord_4027993) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4028004 : List Nat := [2, 3, 1, 1, 2, 3, 2, 3, 1, 3, 2]
def baseStart_4028004 : Nat := 118140960795 + 4028004 * 2 ^ 59
def prefixEnd_4028004 : Nat := 4983230072969 + 3 ^ 40 * 4028004 * 2
def baseEnd_4028004 : Nat := 2068302130232963649525553

theorem tailTrace_4028004 : CollatzResearch.WordTrace tailWord_4028004 prefixEnd_4028004 2068302130232963649525553 := by
  unfold tailWord_4028004
  simp only [CollatzResearch.WordTrace]
  refine ⟨73456687649618455579769533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97942250199491274106359377 73456687649618455579769533)
  ·
    refine ⟨27546257868606920842413575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 73456687649618455579769533 27546257868606920842413575)
    ·
      refine ⟨41319386802910381263620363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27546257868606920842413575 41319386802910381263620363)
      ·
        refine ⟨61979080204365571895430545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41319386802910381263620363 61979080204365571895430545)
        ·
          refine ⟨46484310153274178921572909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61979080204365571895430545 46484310153274178921572909)
          ·
            refine ⟨17431616307477817095589841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 46484310153274178921572909 17431616307477817095589841)
            ·
              refine ⟨13073712230608362821692381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17431616307477817095589841 13073712230608362821692381)
              ·
                refine ⟨4902642086478136058134643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13073712230608362821692381 4902642086478136058134643)
                ·
                  refine ⟨7353963129717204087201965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4902642086478136058134643 7353963129717204087201965)
                  ·
                    refine ⟨2757736173643951532700737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7353963129717204087201965 2757736173643951532700737)
                    ·
                      refine ⟨2068302130232963649525553, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2757736173643951532700737 2068302130232963649525553)
                      ·
                        rfl

theorem cell23_4028004_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 3, 2, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 3, 2, 3, 1, 3, 2].length) (baseStart_4028004 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4028004 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4028004 prefixEnd_4028004 := by exact prefixLift 4028004
  have htrace : WordTrace (prefixWord ++ tailWord_4028004) baseStart_4028004 baseEnd_4028004 := by
    simpa [prefixWord, tailWord_4028004, baseEnd_4028004] using wordTrace_append hprefix tailTrace_4028004
  have hstable : (prefixWord ++ tailWord_4028004).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4028004).length < 2 ^ (prefixWord ++ tailWord_4028004).sum := by decide
  have hdescent : baseEnd_4028004 < baseStart_4028004 := by decide
  rcases family_descends (prefixWord ++ tailWord_4028004) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4028080 : List Nat := [2, 1, 1, 1, 2, 1, 6, 1, 1, 2, 5]
def baseStart_4028080 : Nat := 118140960795 + 4028080 * 2 ^ 59
def prefixEnd_4028080 : Nat := 4983230072969 + 3 ^ 40 * 4028080 * 2
def baseEnd_4028080 : Nat := 2068341154762705352175203

theorem tailTrace_4028080 : CollatzResearch.WordTrace tailWord_4028080 prefixEnd_4028080 2068341154762705352175203 := by
  unfold tailWord_4028080
  simp only [CollatzResearch.WordTrace]
  refine ⟨73458073623480788069652847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97944098164641050759537129 73458073623480788069652847)
  ·
    refine ⟨110187110435221182104479271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73458073623480788069652847 110187110435221182104479271)
    ·
      refine ⟨165280665652831773156718907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110187110435221182104479271 165280665652831773156718907)
      ·
        refine ⟨247920998479247659735078361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 165280665652831773156718907 247920998479247659735078361)
        ·
          refine ⟨185940748859435744801308771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 247920998479247659735078361 185940748859435744801308771)
          ·
            refine ⟨278911123289153617201963157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 185940748859435744801308771 278911123289153617201963157)
            ·
              refine ⟨13073958904179075806342023, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 278911123289153617201963157 13073958904179075806342023)
              ·
                refine ⟨19610938356268613709513035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13073958904179075806342023 19610938356268613709513035)
                ·
                  refine ⟨29416407534402920564269553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19610938356268613709513035 29416407534402920564269553)
                  ·
                    refine ⟨22062305650802190423202165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 29416407534402920564269553 22062305650802190423202165)
                    ·
                      refine ⟨2068341154762705352175203, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 22062305650802190423202165 2068341154762705352175203)
                      ·
                        rfl

theorem cell23_4028080_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 6, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 6, 1, 1, 2, 5].length) (baseStart_4028080 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4028080 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4028080 prefixEnd_4028080 := by exact prefixLift 4028080
  have htrace : WordTrace (prefixWord ++ tailWord_4028080) baseStart_4028080 baseEnd_4028080 := by
    simpa [prefixWord, tailWord_4028080, baseEnd_4028080] using wordTrace_append hprefix tailTrace_4028080
  have hstable : (prefixWord ++ tailWord_4028080).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4028080).length < 2 ^ (prefixWord ++ tailWord_4028080).sum := by decide
  have hdescent : baseEnd_4028080 < baseStart_4028080 := by decide
  rcases family_descends (prefixWord ++ tailWord_4028080) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4028120 : List Nat := [2, 1, 2, 2, 3, 1, 1, 1, 1, 3, 6]
def baseStart_4028120 : Nat := 118140960795 + 4028120 * 2 ^ 59
def prefixEnd_4028120 : Nat := 4983230072969 + 3 ^ 40 * 4028120 * 2
def baseEnd_4028120 : Nat := 2068361693988885195675019

theorem tailTrace_4028120 : CollatzResearch.WordTrace tailWord_4028120 prefixEnd_4028120 2068361693988885195675019 := by
  unfold tailWord_4028120
  simp only [CollatzResearch.WordTrace]
  refine ⟨73458803083408331485380907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97945070777877775313841209 73458803083408331485380907)
  ·
    refine ⟨110188204625112497228071361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73458803083408331485380907 110188204625112497228071361)
    ·
      refine ⟨82641153468834372921053521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 110188204625112497228071361 82641153468834372921053521)
      ·
        refine ⟨61980865101625779690790141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 82641153468834372921053521 61980865101625779690790141)
        ·
          refine ⟨23242824413109667384046303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 61980865101625779690790141 23242824413109667384046303)
          ·
            refine ⟨34864236619664501076069455, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23242824413109667384046303 34864236619664501076069455)
            ·
              refine ⟨52296354929496751614104183, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34864236619664501076069455 52296354929496751614104183)
              ·
                refine ⟨78444532394245127421156275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52296354929496751614104183 78444532394245127421156275)
                ·
                  refine ⟨117666798591367691131734413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 78444532394245127421156275 117666798591367691131734413)
                  ·
                    refine ⟨44125049471762884174400405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 117666798591367691131734413 44125049471762884174400405)
                    ·
                      refine ⟨2068361693988885195675019, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 44125049471762884174400405 2068361693988885195675019)
                      ·
                        rfl

theorem cell23_4028120_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 1, 1, 1, 3, 6].length) (baseStart_4028120 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4028120 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4028120 prefixEnd_4028120 := by exact prefixLift 4028120
  have htrace : WordTrace (prefixWord ++ tailWord_4028120) baseStart_4028120 baseEnd_4028120 := by
    simpa [prefixWord, tailWord_4028120, baseEnd_4028120] using wordTrace_append hprefix tailTrace_4028120
  have hstable : (prefixWord ++ tailWord_4028120).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4028120).length < 2 ^ (prefixWord ++ tailWord_4028120).sum := by decide
  have hdescent : baseEnd_4028120 < baseStart_4028120 := by decide
  rcases family_descends (prefixWord ++ tailWord_4028120) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4028127 : List Nat := [1, 1, 2, 3, 2, 2, 2, 1, 4, 2, 3]
def baseStart_4028127 : Nat := 118140960795 + 4028127 * 2 ^ 59
def prefixEnd_4028127 : Nat := 4983230072969 + 3 ^ 40 * 4028127 * 2
def baseEnd_4028127 : Nat := 2068365288353466668287487

theorem tailTrace_4028127 : CollatzResearch.WordTrace tailWord_4028127 prefixEnd_4028127 2068365288353466668287487 := by
  unfold tailWord_4028127
  simp only [CollatzResearch.WordTrace]
  refine ⟨146917861477791303166266635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97945240985194202110844423 146917861477791303166266635)
  ·
    refine ⟨220376792216686954749399953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146917861477791303166266635 220376792216686954749399953)
    ·
      refine ⟨165282594162515216062049965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 220376792216686954749399953 165282594162515216062049965)
      ·
        refine ⟨61980972810943206023268737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 165282594162515216062049965 61980972810943206023268737)
        ·
          refine ⟨46485729608207404517451553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61980972810943206023268737 46485729608207404517451553)
          ·
            refine ⟨34864297206155553388088665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46485729608207404517451553 34864297206155553388088665)
            ·
              refine ⟨26148222904616665041066499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34864297206155553388088665 26148222904616665041066499)
              ·
                refine ⟨39222334356924997561599749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26148222904616665041066499 39222334356924997561599749)
                ·
                  refine ⟨7354187691923437042799953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 39222334356924997561599749 7354187691923437042799953)
                  ·
                    refine ⟨5515640768942577782099965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7354187691923437042799953 5515640768942577782099965)
                    ·
                      refine ⟨2068365288353466668287487, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5515640768942577782099965 2068365288353466668287487)
                      ·
                        rfl

theorem cell23_4028127_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 2, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 2, 1, 4, 2, 3].length) (baseStart_4028127 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4028127 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4028127 prefixEnd_4028127 := by exact prefixLift 4028127
  have htrace : WordTrace (prefixWord ++ tailWord_4028127) baseStart_4028127 baseEnd_4028127 := by
    simpa [prefixWord, tailWord_4028127, baseEnd_4028127] using wordTrace_append hprefix tailTrace_4028127
  have hstable : (prefixWord ++ tailWord_4028127).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4028127).length < 2 ^ (prefixWord ++ tailWord_4028127).sum := by decide
  have hdescent : baseEnd_4028127 < baseStart_4028127 := by decide
  rcases family_descends (prefixWord ++ tailWord_4028127) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4028174 : List Nat := [4, 1, 1, 2, 1, 1, 2, 2, 5, 1, 3]
def baseStart_4028174 : Nat := 118140960795 + 4028174 * 2 ^ 59
def prefixEnd_4028174 : Nat := 4983230072969 + 3 ^ 40 * 4028174 * 2
def baseEnd_4028174 : Nat := 2068389421944227984399771

theorem tailTrace_4028174 : CollatzResearch.WordTrace tailWord_4028174 prefixEnd_4028174 2068389421944227984399771 := by
  unfold tailWord_4028174
  simp only [CollatzResearch.WordTrace]
  refine ⟨18364946963577628774153447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 97946383805747353462151717 18364946963577628774153447)
  ·
    refine ⟨27547420445366443161230171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18364946963577628774153447 27547420445366443161230171)
    ·
      refine ⟨41321130668049664741845257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27547420445366443161230171 41321130668049664741845257)
      ·
        refine ⟨30990848001037248556383943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41321130668049664741845257 30990848001037248556383943)
        ·
          refine ⟨46486272001555872834575915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30990848001037248556383943 46486272001555872834575915)
          ·
            refine ⟨69729408002333809251863873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46486272001555872834575915 69729408002333809251863873)
            ·
              refine ⟨52297056001750356938897905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 69729408002333809251863873 52297056001750356938897905)
              ·
                refine ⟨39222792001312767704173429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 52297056001750356938897905 39222792001312767704173429)
                ·
                  refine ⟨3677136750123071972266259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 39222792001312767704173429 3677136750123071972266259)
                  ·
                    refine ⟨5515705125184607958399389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3677136750123071972266259 5515705125184607958399389)
                    ·
                      refine ⟨2068389421944227984399771, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5515705125184607958399389 2068389421944227984399771)
                      ·
                        rfl

theorem cell23_4028174_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 2, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 2, 2, 5, 1, 3].length) (baseStart_4028174 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4028174 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4028174 prefixEnd_4028174 := by exact prefixLift 4028174
  have htrace : WordTrace (prefixWord ++ tailWord_4028174) baseStart_4028174 baseEnd_4028174 := by
    simpa [prefixWord, tailWord_4028174, baseEnd_4028174] using wordTrace_append hprefix tailTrace_4028174
  have hstable : (prefixWord ++ tailWord_4028174).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4028174).length < 2 ^ (prefixWord ++ tailWord_4028174).sum := by decide
  have hdescent : baseEnd_4028174 < baseStart_4028174 := by decide
  rcases family_descends (prefixWord ++ tailWord_4028174) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4028184 : List Nat := [2, 1, 2, 3, 1, 1, 3, 1, 4, 3, 2]
def baseStart_4028184 : Nat := 118140960795 + 4028184 * 2 ^ 59
def prefixEnd_4028184 : Nat := 4983230072969 + 3 ^ 40 * 4028184 * 2
def baseEnd_4028184 : Nat := 2068394556750772945274725

theorem tailTrace_4028184 : CollatzResearch.WordTrace tailWord_4028184 prefixEnd_4028184 2068394556750772945274725 := by
  unfold tailWord_4028184
  simp only [CollatzResearch.WordTrace]
  refine ⟨73459970219292400950545803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97946626959056534600727737 73459970219292400950545803)
  ·
    refine ⟨110189955328938601425818705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73459970219292400950545803 110189955328938601425818705)
    ·
      refine ⟨82642466496703951069364029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 110189955328938601425818705 82642466496703951069364029)
      ·
        refine ⟨30990924936263981651011511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 82642466496703951069364029 30990924936263981651011511)
        ·
          refine ⟨46486387404395972476517267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30990924936263981651011511 46486387404395972476517267)
          ·
            refine ⟨69729581106593958714775901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46486387404395972476517267 69729581106593958714775901)
            ·
              refine ⟨26148592914972734518040963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 69729581106593958714775901 26148592914972734518040963)
              ·
                refine ⟨39222889372459101777061445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26148592914972734518040963 39222889372459101777061445)
                ·
                  refine ⟨7354291757336081583199021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 39222889372459101777061445 7354291757336081583199021)
                  ·
                    refine ⟨2757859409001030593699633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7354291757336081583199021 2757859409001030593699633)
                    ·
                      refine ⟨2068394556750772945274725, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2757859409001030593699633 2068394556750772945274725)
                      ·
                        rfl

theorem cell23_4028184_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 3, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 3, 1, 4, 3, 2].length) (baseStart_4028184 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4028184 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4028184 prefixEnd_4028184 := by exact prefixLift 4028184
  have htrace : WordTrace (prefixWord ++ tailWord_4028184) baseStart_4028184 baseEnd_4028184 := by
    simpa [prefixWord, tailWord_4028184, baseEnd_4028184] using wordTrace_append hprefix tailTrace_4028184
  have hstable : (prefixWord ++ tailWord_4028184).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4028184).length < 2 ^ (prefixWord ++ tailWord_4028184).sum := by decide
  have hdescent : baseEnd_4028184 < baseStart_4028184 := by decide
  rcases family_descends (prefixWord ++ tailWord_4028184) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4028211 : List Nat := [1, 1, 1, 2, 7, 2, 1, 2, 1, 5]
def baseStart_4028211 : Nat := 118140960795 + 4028211 * 2 ^ 59
def prefixEnd_4028211 : Nat := 4983230072969 + 3 ^ 40 * 4028211 * 2
def baseEnd_4028211 : Nat := 689469473576148113212367

theorem tailTrace_4028211 : CollatzResearch.WordTrace tailWord_4028211 prefixEnd_4028211 689469473576148113212367 := by
  unfold tailWord_4028211
  simp only [CollatzResearch.WordTrace]
  refine ⟨146920925209486985512324487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97947283472991323674882991 146920925209486985512324487)
  ·
    refine ⟨220381387814230478268486731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146920925209486985512324487 220381387814230478268486731)
    ·
      refine ⟨330572081721345717402730097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 220381387814230478268486731 330572081721345717402730097)
      ·
        refine ⟨247929061291009288052047573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 330572081721345717402730097 247929061291009288052047573)
        ·
          refine ⟨5810837374008030188719865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 247929061291009288052047573 5810837374008030188719865)
          ·
            refine ⟨4358128030506022641539899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5810837374008030188719865 4358128030506022641539899)
            ·
              refine ⟨6537192045759033962309849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4358128030506022641539899 6537192045759033962309849)
              ·
                refine ⟨4902894034319275471732387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6537192045759033962309849 4902894034319275471732387)
                ·
                  refine ⟨7354341051478913207598581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4902894034319275471732387 7354341051478913207598581)
                  ·
                    refine ⟨689469473576148113212367, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7354341051478913207598581 689469473576148113212367)
                    ·
                      rfl

theorem cell23_4028211_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 7, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 7, 2, 1, 2, 1, 5].length) (baseStart_4028211 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4028211 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4028211 prefixEnd_4028211 := by exact prefixLift 4028211
  have htrace : WordTrace (prefixWord ++ tailWord_4028211) baseStart_4028211 baseEnd_4028211 := by
    simpa [prefixWord, tailWord_4028211, baseEnd_4028211] using wordTrace_append hprefix tailTrace_4028211
  have hstable : (prefixWord ++ tailWord_4028211).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4028211).length < 2 ^ (prefixWord ++ tailWord_4028211).sum := by decide
  have hdescent : baseEnd_4028211 < baseStart_4028211 := by decide
  rcases family_descends (prefixWord ++ tailWord_4028211) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4028227 : List Nat := [1, 1, 1, 3, 1, 5, 1, 1, 3, 2, 4]
def baseStart_4028227 : Nat := 118140960795 + 4028227 * 2 ^ 59
def prefixEnd_4028227 : Nat := 4983230072969 + 3 ^ 40 * 4028227 * 2
def baseEnd_4028227 : Nat := 2068416636418916277037027

theorem tailTrace_4028227 : CollatzResearch.WordTrace tailWord_4028227 prefixEnd_4028227 2068416636418916277037027 := by
  unfold tailWord_4028227
  simp only [CollatzResearch.WordTrace]
  refine ⟨146921508777429020244906935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97947672518286013496604623 146921508777429020244906935)
  ·
    refine ⟨220382263166143530367360403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146921508777429020244906935 220382263166143530367360403)
    ·
      refine ⟨330573394749215295551040605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 220382263166143530367360403 330573394749215295551040605)
      ·
        refine ⟨123965023030955735831640227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 330573394749215295551040605 123965023030955735831640227)
        ·
          refine ⟨185947534546433603747460341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 123965023030955735831640227 185947534546433603747460341)
          ·
            refine ⟨17432581363728150351324407, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 185947534546433603747460341 17432581363728150351324407)
            ·
              refine ⟨26148872045592225526986611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17432581363728150351324407 26148872045592225526986611)
              ·
                refine ⟨39223308068388338290479917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26148872045592225526986611 39223308068388338290479917)
                ·
                  refine ⟨14708740525645626858929969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 39223308068388338290479917 14708740525645626858929969)
                  ·
                    refine ⟨11031555394234220144197477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14708740525645626858929969 11031555394234220144197477)
                    ·
                      refine ⟨2068416636418916277037027, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11031555394234220144197477 2068416636418916277037027)
                      ·
                        rfl

theorem cell23_4028227_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 5, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 5, 1, 1, 3, 2, 4].length) (baseStart_4028227 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4028227 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4028227 prefixEnd_4028227 := by exact prefixLift 4028227
  have htrace : WordTrace (prefixWord ++ tailWord_4028227) baseStart_4028227 baseEnd_4028227 := by
    simpa [prefixWord, tailWord_4028227, baseEnd_4028227] using wordTrace_append hprefix tailTrace_4028227
  have hstable : (prefixWord ++ tailWord_4028227).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4028227).length < 2 ^ (prefixWord ++ tailWord_4028227).sum := by decide
  have hdescent : baseEnd_4028227 < baseStart_4028227 := by decide
  rcases family_descends (prefixWord ++ tailWord_4028227) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4028241 : List Nat := [1, 2, 2, 1, 5, 2, 2, 2, 2, 4]
def baseStart_4028241 : Nat := 118140960795 + 4028241 * 2 ^ 59
def prefixEnd_4028241 : Nat := 4983230072969 + 3 ^ 40 * 4028241 * 2
def baseEnd_4028241 : Nat := 689474608382693074087321

theorem tailTrace_4028241 : CollatzResearch.WordTrace tailWord_4028241 prefixEnd_4028241 689474608382693074087321 := by
  unfold tailWord_4028241
  simp only [CollatzResearch.WordTrace]
  refine ⟨146922019399378300635916577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97948012932918867090611051 146922019399378300635916577)
  ·
    refine ⟨110191514549533725476937433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 146922019399378300635916577 110191514549533725476937433)
    ·
      refine ⟨82643635912150294107703075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 110191514549533725476937433 82643635912150294107703075)
      ·
        refine ⟨123965453868225441161554613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82643635912150294107703075 123965453868225441161554613)
        ·
          refine ⟨11621761300146135108895745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 123965453868225441161554613 11621761300146135108895745)
          ·
            refine ⟨8716320975109601331671809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11621761300146135108895745 8716320975109601331671809)
            ·
              refine ⟨6537240731332200998753857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8716320975109601331671809 6537240731332200998753857)
              ·
                refine ⟨4902930548499150749065393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6537240731332200998753857 4902930548499150749065393)
                ·
                  refine ⟨3677197911374363061799045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4902930548499150749065393 3677197911374363061799045)
                  ·
                    refine ⟨689474608382693074087321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3677197911374363061799045 689474608382693074087321)
                    ·
                      rfl

theorem cell23_4028241_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 2, 2, 2, 2, 4].length) (baseStart_4028241 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4028241 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4028241 prefixEnd_4028241 := by exact prefixLift 4028241
  have htrace : WordTrace (prefixWord ++ tailWord_4028241) baseStart_4028241 baseEnd_4028241 := by
    simpa [prefixWord, tailWord_4028241, baseEnd_4028241] using wordTrace_append hprefix tailTrace_4028241
  have hstable : (prefixWord ++ tailWord_4028241).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4028241).length < 2 ^ (prefixWord ++ tailWord_4028241).sum := by decide
  have hdescent : baseEnd_4028241 < baseStart_4028241 := by decide
  rcases family_descends (prefixWord ++ tailWord_4028241) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4028297 : List Nat := [1, 2, 1, 1, 5, 1, 1, 1, 4, 6]
def baseStart_4028297 : Nat := 118140960795 + 4028297 * 2 ^ 59
def prefixEnd_4028297 : Nat := 4983230072969 + 3 ^ 40 * 4028297 * 2
def baseEnd_4028297 : Nat := 689484193354910334387235

theorem tailTrace_4028297 : CollatzResearch.WordTrace tailWord_4028297 prefixEnd_4028297 689484193354910334387235 := by
  unfold tailWord_4028297
  simp only [CollatzResearch.WordTrace]
  refine ⟨146924061887175422199955145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97949374591450281466636763 146924061887175422199955145)
  ·
    refine ⟨110193046415381566649966359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 146924061887175422199955145 110193046415381566649966359)
    ·
      refine ⟨165289569623072349974949539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110193046415381566649966359 165289569623072349974949539)
      ·
        refine ⟨247934354434608524962424309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 165289569623072349974949539 247934354434608524962424309)
        ·
          refine ⟨23243845728244549215227279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 247934354434608524962424309 23243845728244549215227279)
          ·
            refine ⟨34865768592366823822840919, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23243845728244549215227279 34865768592366823822840919)
            ·
              refine ⟨52298652888550235734261379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34865768592366823822840919 52298652888550235734261379)
              ·
                refine ⟨78447979332825353601392069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52298652888550235734261379 78447979332825353601392069)
                ·
                  refine ⟨14708996124904753800261013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 78447979332825353601392069 14708996124904753800261013)
                  ·
                    refine ⟨689484193354910334387235, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 14708996124904753800261013 689484193354910334387235)
                    ·
                      rfl

theorem cell23_4028297_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 1, 1, 4, 6].length) (baseStart_4028297 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4028297 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4028297 prefixEnd_4028297 := by exact prefixLift 4028297
  have htrace : WordTrace (prefixWord ++ tailWord_4028297) baseStart_4028297 baseEnd_4028297 := by
    simpa [prefixWord, tailWord_4028297, baseEnd_4028297] using wordTrace_append hprefix tailTrace_4028297
  have hstable : (prefixWord ++ tailWord_4028297).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4028297).length < 2 ^ (prefixWord ++ tailWord_4028297).sum := by decide
  have hdescent : baseEnd_4028297 < baseStart_4028297 := by decide
  rcases family_descends (prefixWord ++ tailWord_4028297) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4028298 : List Nat := [3, 1, 2, 4, 2, 1, 1, 1, 4, 1, 3]
def baseStart_4028298 : Nat := 118140960795 + 4028298 * 2 ^ 59
def prefixEnd_4028298 : Nat := 4983230072969 + 3 ^ 40 * 4028298 * 2
def baseEnd_4028298 : Nat := 2068453093545385499249201

theorem tailTrace_4028298 : CollatzResearch.WordTrace tailWord_4028298 prefixEnd_4028298 2068453093545385499249201 := by
  unfold tailWord_4028298
  simp only [CollatzResearch.WordTrace]
  refine ⟨36731024590042949842685387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 97949398906781199580494365 36731024590042949842685387)
  ·
    refine ⟨55096536885064424764028081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36731024590042949842685387 55096536885064424764028081)
    ·
      refine ⟨41322402663798318573021061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55096536885064424764028081 41322402663798318573021061)
      ·
        refine ⟨7747950499462184732441449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 41322402663798318573021061 7747950499462184732441449)
        ·
          refine ⟨5810962874596638549331087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7747950499462184732441449 5810962874596638549331087)
          ·
            refine ⟨8716444311894957823996631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5810962874596638549331087 8716444311894957823996631)
            ·
              refine ⟨13074666467842436735994947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8716444311894957823996631 13074666467842436735994947)
              ·
                refine ⟨19611999701763655103992421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13074666467842436735994947 19611999701763655103992421)
                ·
                  refine ⟨3677249944080685331998579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 19611999701763655103992421 3677249944080685331998579)
                  ·
                    refine ⟨5515874916121027997997869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3677249944080685331998579 5515874916121027997997869)
                    ·
                      refine ⟨2068453093545385499249201, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5515874916121027997997869 2068453093545385499249201)
                      ·
                        rfl

theorem cell23_4028298_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 2, 1, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 2, 1, 1, 1, 4, 1, 3].length) (baseStart_4028298 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4028298 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4028298 prefixEnd_4028298 := by exact prefixLift 4028298
  have htrace : WordTrace (prefixWord ++ tailWord_4028298) baseStart_4028298 baseEnd_4028298 := by
    simpa [prefixWord, tailWord_4028298, baseEnd_4028298] using wordTrace_append hprefix tailTrace_4028298
  have hstable : (prefixWord ++ tailWord_4028298).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4028298).length < 2 ^ (prefixWord ++ tailWord_4028298).sum := by decide
  have hdescent : baseEnd_4028298 < baseStart_4028298 := by decide
  rcases family_descends (prefixWord ++ tailWord_4028298) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4028304 : List Nat := [2, 1, 1, 1, 1, 1, 2, 3, 5, 4, 2]
def baseStart_4028304 : Nat := 118140960795 + 4028304 * 2 ^ 59
def prefixEnd_4028304 : Nat := 4983230072969 + 3 ^ 40 * 4028304 * 2
def baseEnd_4028304 : Nat := 2068456174429312475774173

theorem tailTrace_4028304 : CollatzResearch.WordTrace tailWord_4028304 prefixEnd_4028304 2068456174429312475774173 := by
  unfold tailWord_4028304
  simp only [CollatzResearch.WordTrace]
  refine ⟨73462158599075031197729983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97949544798766708263639977 73462158599075031197729983)
  ·
    refine ⟨110193237898612546796594975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73462158599075031197729983 110193237898612546796594975)
    ·
      refine ⟨165289856847918820194892463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110193237898612546796594975 165289856847918820194892463)
      ·
        refine ⟨247934785271878230292338695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 165289856847918820194892463 247934785271878230292338695)
        ·
          refine ⟨371902177907817345438508043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 247934785271878230292338695 371902177907817345438508043)
          ·
            refine ⟨557853266861726018157762065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 371902177907817345438508043 557853266861726018157762065)
            ·
              refine ⟨418389950146294513618321549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 557853266861726018157762065 418389950146294513618321549)
              ·
                refine ⟨156896231304860442606870581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 418389950146294513618321549 156896231304860442606870581)
                ·
                  refine ⟨14709021684830666494394117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 156896231304860442606870581 14709021684830666494394117)
                  ·
                    refine ⟨2757941565905749967698897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 14709021684830666494394117 2757941565905749967698897)
                    ·
                      refine ⟨2068456174429312475774173, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2757941565905749967698897 2068456174429312475774173)
                      ·
                        rfl

theorem cell23_4028304_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 3, 5, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 3, 5, 4, 2].length) (baseStart_4028304 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4028304 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4028304 prefixEnd_4028304 := by exact prefixLift 4028304
  have htrace : WordTrace (prefixWord ++ tailWord_4028304) baseStart_4028304 baseEnd_4028304 := by
    simpa [prefixWord, tailWord_4028304, baseEnd_4028304] using wordTrace_append hprefix tailTrace_4028304
  have hstable : (prefixWord ++ tailWord_4028304).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4028304).length < 2 ^ (prefixWord ++ tailWord_4028304).sum := by decide
  have hdescent : baseEnd_4028304 < baseStart_4028304 := by decide
  rcases family_descends (prefixWord ++ tailWord_4028304) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4028314 : List Nat := [3, 1, 1, 4, 2, 1, 2, 1, 2, 6]
def baseStart_4028314 : Nat := 118140960795 + 4028314 * 2 ^ 59
def prefixEnd_4028314 : Nat := 4983230072969 + 3 ^ 40 * 4028314 * 2
def baseEnd_4028314 : Nat := 689487103078619145549709

theorem tailTrace_4028314 : CollatzResearch.WordTrace tailWord_4028314 prefixEnd_4028314 689487103078619145549709 := by
  unfold tailWord_4028314
  simp only [CollatzResearch.WordTrace]
  refine ⟨36731170482028458525830999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 97949787952075889402215997 36731170482028458525830999)
  ·
    refine ⟨55096755723042687788746499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36731170482028458525830999 55096755723042687788746499)
    ·
      refine ⟨82645133584564031683119749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55096755723042687788746499 82645133584564031683119749)
      ·
        refine ⟨15495962547105755940584953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 82645133584564031683119749 15495962547105755940584953)
        ·
          refine ⟨11621971910329316955438715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15495962547105755940584953 11621971910329316955438715)
          ·
            refine ⟨17432957865493975433158073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11621971910329316955438715 17432957865493975433158073)
            ·
              refine ⟨13074718399120481574868555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17432957865493975433158073 13074718399120481574868555)
              ·
                refine ⟨19612077598680722362302833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13074718399120481574868555 19612077598680722362302833)
                ·
                  refine ⟨14709058199010541771727125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19612077598680722362302833 14709058199010541771727125)
                  ·
                    refine ⟨689487103078619145549709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 14709058199010541771727125 689487103078619145549709)
                    ·
                      rfl

theorem cell23_4028314_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 1, 2, 1, 2, 6].length) (baseStart_4028314 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4028314 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4028314 prefixEnd_4028314 := by exact prefixLift 4028314
  have htrace : WordTrace (prefixWord ++ tailWord_4028314) baseStart_4028314 baseEnd_4028314 := by
    simpa [prefixWord, tailWord_4028314, baseEnd_4028314] using wordTrace_append hprefix tailTrace_4028314
  have hstable : (prefixWord ++ tailWord_4028314).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4028314).length < 2 ^ (prefixWord ++ tailWord_4028314).sum := by decide
  have hdescent : baseEnd_4028314 < baseStart_4028314 := by decide
  rcases family_descends (prefixWord ++ tailWord_4028314) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4028357 : List Nat := [1, 3, 1, 1, 1, 1, 1, 4, 3, 7]
def baseStart_4028357 : Nat := 118140960795 + 4028357 * 2 ^ 59
def prefixEnd_4028357 : Nat := 4983230072969 + 3 ^ 40 * 4028357 * 2
def baseEnd_4028357 : Nat := 689494462968000256137143

theorem tailTrace_4028357 : CollatzResearch.WordTrace tailWord_4028357 prefixEnd_4028357 689494462968000256137143 := by
  unfold tailWord_4028357
  simp only [CollatzResearch.WordTrace]
  refine ⟨146926250266958052447139325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97950833511305368298092883 146926250266958052447139325)
  ·
    refine ⟨55097343850109269667677247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 146926250266958052447139325 55097343850109269667677247)
    ·
      refine ⟨82646015775163904501515871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55097343850109269667677247 82646015775163904501515871)
      ·
        refine ⟨123969023662745856752273807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82646015775163904501515871 123969023662745856752273807)
        ·
          refine ⟨185953535494118785128410711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 123969023662745856752273807 185953535494118785128410711)
          ·
            refine ⟨278930303241178177692616067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 185953535494118785128410711 278930303241178177692616067)
            ·
              refine ⟨418395454861767266538924101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 278930303241178177692616067 418395454861767266538924101)
              ·
                refine ⟨78449147786581362476048269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 418395454861767266538924101 78449147786581362476048269)
                ·
                  refine ⟨29418430419968010928518101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 78449147786581362476048269 29418430419968010928518101)
                  ·
                    refine ⟨689494462968000256137143, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 29418430419968010928518101 689494462968000256137143)
                    ·
                      rfl

theorem cell23_4028357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 4, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 4, 3, 7].length) (baseStart_4028357 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4028357 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4028357 prefixEnd_4028357 := by exact prefixLift 4028357
  have htrace : WordTrace (prefixWord ++ tailWord_4028357) baseStart_4028357 baseEnd_4028357 := by
    simpa [prefixWord, tailWord_4028357, baseEnd_4028357] using wordTrace_append hprefix tailTrace_4028357
  have hstable : (prefixWord ++ tailWord_4028357).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4028357).length < 2 ^ (prefixWord ++ tailWord_4028357).sum := by decide
  have hdescent : baseEnd_4028357 < baseStart_4028357 := by decide
  rcases family_descends (prefixWord ++ tailWord_4028357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4028468 : List Nat := [2, 5, 1, 2, 2, 1, 1, 1, 8]
def baseStart_4028468 : Nat := 118140960795 + 4028468 * 2 ^ 59
def prefixEnd_4028468 : Nat := 4983230072969 + 3 ^ 40 * 4028468 * 2
def baseEnd_4028468 : Nat := 229837820584072203791491

theorem tailTrace_4028468 : CollatzResearch.WordTrace tailWord_4028468 prefixEnd_4028468 229837820584072203791491 := by
  unfold tailWord_4028468
  simp only [CollatzResearch.WordTrace]
  refine ⟨73465149384777959202215029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97953532513037278936286705 73465149384777959202215029)
  ·
    refine ⟨6887357754822933675207659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 73465149384777959202215029 6887357754822933675207659)
    ·
      refine ⟨10331036632234400512811489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6887357754822933675207659 10331036632234400512811489)
      ·
        refine ⟨7748277474175800384608617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10331036632234400512811489 7748277474175800384608617)
        ·
          refine ⟨5811208105631850288456463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7748277474175800384608617 5811208105631850288456463)
          ·
            refine ⟨8716812158447775432684695, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5811208105631850288456463 8716812158447775432684695)
            ·
              refine ⟨13075218237671663149027043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8716812158447775432684695 13075218237671663149027043)
              ·
                refine ⟨19612827356507494723540565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13075218237671663149027043 19612827356507494723540565)
                ·
                  refine ⟨229837820584072203791491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 19612827356507494723540565 229837820584072203791491)
                  ·
                    rfl

theorem cell23_4028468_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 2, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 2, 1, 1, 1, 8].length) (baseStart_4028468 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4028468 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4028468 prefixEnd_4028468 := by exact prefixLift 4028468
  have htrace : WordTrace (prefixWord ++ tailWord_4028468) baseStart_4028468 baseEnd_4028468 := by
    simpa [prefixWord, tailWord_4028468, baseEnd_4028468] using wordTrace_append hprefix tailTrace_4028468
  have hstable : (prefixWord ++ tailWord_4028468).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4028468).length < 2 ^ (prefixWord ++ tailWord_4028468).sum := by decide
  have hdescent : baseEnd_4028468 < baseStart_4028468 := by decide
  rcases family_descends (prefixWord ++ tailWord_4028468) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4028512 : List Nat := [2, 1, 1, 3, 2, 5, 1, 3, 1, 1, 3]
def baseStart_4028512 : Nat := 118140960795 + 4028512 * 2 ^ 59
def prefixEnd_4028512 : Nat := 4983230072969 + 3 ^ 40 * 4028512 * 2
def baseEnd_4028512 : Nat := 2068562978405447661973217

theorem tailTrace_4028512 : CollatzResearch.WordTrace tailWord_4028512 prefixEnd_4028512 2068562978405447661973217 := by
  unfold tailWord_4028512
  simp only [CollatzResearch.WordTrace]
  refine ⟨73465951790698256959515895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97954602387597675946021193 73465951790698256959515895)
  ·
    refine ⟨110198927686047385439273843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73465951790698256959515895 110198927686047385439273843)
    ·
      refine ⟨165298391529071078158910765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110198927686047385439273843 165298391529071078158910765)
      ·
        refine ⟨61986896823401654309591537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 165298391529071078158910765 61986896823401654309591537)
        ·
          refine ⟨46490172617551240732193653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61986896823401654309591537 46490172617551240732193653)
          ·
            refine ⟨4358453682895428818643155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 46490172617551240732193653 4358453682895428818643155)
            ·
              refine ⟨6537680524343143227964733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4358453682895428818643155 6537680524343143227964733)
              ·
                refine ⟨2451630196628678710486775, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6537680524343143227964733 2451630196628678710486775)
                ·
                  refine ⟨3677445294943018065730163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2451630196628678710486775 3677445294943018065730163)
                  ·
                    refine ⟨5516167942414527098595245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3677445294943018065730163 5516167942414527098595245)
                    ·
                      refine ⟨2068562978405447661973217, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5516167942414527098595245 2068562978405447661973217)
                      ·
                        rfl

theorem cell23_4028512_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 5, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 5, 1, 3, 1, 1, 3].length) (baseStart_4028512 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4028512 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4028512 prefixEnd_4028512 := by exact prefixLift 4028512
  have htrace : WordTrace (prefixWord ++ tailWord_4028512) baseStart_4028512 baseEnd_4028512 := by
    simpa [prefixWord, tailWord_4028512, baseEnd_4028512] using wordTrace_append hprefix tailTrace_4028512
  have hstable : (prefixWord ++ tailWord_4028512).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4028512).length < 2 ^ (prefixWord ++ tailWord_4028512).sum := by decide
  have hdescent : baseEnd_4028512 < baseStart_4028512 := by decide
  rcases family_descends (prefixWord ++ tailWord_4028512) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4028521 : List Nat := [1, 2, 1, 1, 1, 5, 4, 1, 1, 1, 5]
def baseStart_4028521 : Nat := 118140960795 + 4028521 * 2 ^ 59
def prefixEnd_4028521 : Nat := 4983230072969 + 3 ^ 40 * 4028521 * 2
def baseEnd_4028521 : Nat := 2068567599731338126760675

theorem tailTrace_4028521 : CollatzResearch.WordTrace tailWord_4028521 prefixEnd_4028521 2068567599731338126760675 := by
  unfold tailWord_4028521
  simp only [CollatzResearch.WordTrace]
  refine ⟨146932231838363908456109417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97954821225575938970739611 146932231838363908456109417)
  ·
    refine ⟨110199173878772931342082063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 146932231838363908456109417 110199173878772931342082063)
    ·
      refine ⟨165298760818159397013123095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110199173878772931342082063 165298760818159397013123095)
      ·
        refine ⟨247948141227239095519684643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 165298760818159397013123095 247948141227239095519684643)
        ·
          refine ⟨371922211840858643279526965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 247948141227239095519684643 371922211840858643279526965)
          ·
            refine ⟨34867707360080497807455653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 371922211840858643279526965 34867707360080497807455653)
            ·
              refine ⟨6537695130015093338897935, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 34867707360080497807455653 6537695130015093338897935)
              ·
                refine ⟨9806542695022640008346903, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6537695130015093338897935 9806542695022640008346903)
                ·
                  refine ⟨14709814042533960012520355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9806542695022640008346903 14709814042533960012520355)
                  ·
                    refine ⟨22064721063800940018780533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14709814042533960012520355 22064721063800940018780533)
                    ·
                      refine ⟨2068567599731338126760675, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 22064721063800940018780533 2068567599731338126760675)
                      ·
                        rfl

theorem cell23_4028521_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 4, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 4, 1, 1, 1, 5].length) (baseStart_4028521 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4028521 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4028521 prefixEnd_4028521 := by exact prefixLift 4028521
  have htrace : WordTrace (prefixWord ++ tailWord_4028521) baseStart_4028521 baseEnd_4028521 := by
    simpa [prefixWord, tailWord_4028521, baseEnd_4028521] using wordTrace_append hprefix tailTrace_4028521
  have hstable : (prefixWord ++ tailWord_4028521).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4028521).length < 2 ^ (prefixWord ++ tailWord_4028521).sum := by decide
  have hdescent : baseEnd_4028521 < baseStart_4028521 := by decide
  rcases family_descends (prefixWord ++ tailWord_4028521) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4028524 : List Nat := [2, 2, 1, 1, 3, 3, 11]
def baseStart_4028524 : Nat := 118140960795 + 4028524 * 2 ^ 59
def prefixEnd_4028524 : Nat := 4983230072969 + 3 ^ 40 * 4028524 * 2
def baseEnd_4028524 : Nat := 25537890619423476728681

theorem tailTrace_4028524 : CollatzResearch.WordTrace tailWord_4028524 prefixEnd_4028524 25537890619423476728681 := by
  unfold tailWord_4028524
  simp only [CollatzResearch.WordTrace]
  refine ⟨73466170628676519984234313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97954894171568693312312417 73466170628676519984234313)
  ·
    refine ⟨55099627971507389988175735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73466170628676519984234313 55099627971507389988175735)
    ·
      refine ⟨82649441957261084982263603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55099627971507389988175735 82649441957261084982263603)
      ·
        refine ⟨123974162935891627473395405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82649441957261084982263603 123974162935891627473395405)
        ·
          refine ⟨46490311100959360302523277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 123974162935891627473395405 46490311100959360302523277)
          ·
            refine ⟨17433866662859760113446229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 46490311100959360302523277 17433866662859760113446229)
            ·
              refine ⟨25537890619423476728681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 17433866662859760113446229 25537890619423476728681)
              ·
                rfl

theorem cell23_4028524_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 3, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 3, 11].length) (baseStart_4028524 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4028524 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4028524 prefixEnd_4028524 := by exact prefixLift 4028524
  have htrace : WordTrace (prefixWord ++ tailWord_4028524) baseStart_4028524 baseEnd_4028524 := by
    simpa [prefixWord, tailWord_4028524, baseEnd_4028524] using wordTrace_append hprefix tailTrace_4028524
  have hstable : (prefixWord ++ tailWord_4028524).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4028524).length < 2 ^ (prefixWord ++ tailWord_4028524).sum := by decide
  have hdescent : baseEnd_4028524 < baseStart_4028524 := by decide
  rcases family_descends (prefixWord ++ tailWord_4028524) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4028535 : List Nat := [1, 1, 3, 1, 1, 5, 3, 1, 3, 2, 2]
def baseStart_4028535 : Nat := 118140960795 + 4028535 * 2 ^ 59
def prefixEnd_4028535 : Nat := 4983230072969 + 3 ^ 40 * 4028535 * 2
def baseEnd_4028535 : Nat := 2068574788460501071985611

theorem tailTrace_4028535 : CollatzResearch.WordTrace tailWord_4028535 prefixEnd_4028535 2068574788460501071985611 := by
  unfold tailWord_4028535
  simp only [CollatzResearch.WordTrace]
  refine ⟨146932742460313188847119059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97955161640208792564746039 146932742460313188847119059)
  ·
    refine ⟨220399113690469783270678589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146932742460313188847119059 220399113690469783270678589)
    ·
      refine ⟨82649667633926168726504471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 220399113690469783270678589 82649667633926168726504471)
      ·
        refine ⟨123974501450889253089756707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82649667633926168726504471 123974501450889253089756707)
        ·
          refine ⟨185961752176333879634635061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 123974501450889253089756707 185961752176333879634635061)
          ·
            refine ⟨17433914266531301215747037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 185961752176333879634635061 17433914266531301215747037)
            ·
              refine ⟨6537717849949237955905139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17433914266531301215747037 6537717849949237955905139)
              ·
                refine ⟨9806576774923856933857709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6537717849949237955905139 9806576774923856933857709)
                ·
                  refine ⟨3677466290596446350196641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9806576774923856933857709 3677466290596446350196641)
                  ·
                    refine ⟨2758099717947334762647481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3677466290596446350196641 2758099717947334762647481)
                    ·
                      refine ⟨2068574788460501071985611, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2758099717947334762647481 2068574788460501071985611)
                      ·
                        rfl

theorem cell23_4028535_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 5, 3, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 5, 3, 1, 3, 2, 2].length) (baseStart_4028535 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4028535 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4028535 prefixEnd_4028535 := by exact prefixLift 4028535
  have htrace : WordTrace (prefixWord ++ tailWord_4028535) baseStart_4028535 baseEnd_4028535 := by
    simpa [prefixWord, tailWord_4028535, baseEnd_4028535] using wordTrace_append hprefix tailTrace_4028535
  have hstable : (prefixWord ++ tailWord_4028535).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4028535).length < 2 ^ (prefixWord ++ tailWord_4028535).sum := by decide
  have hdescent : baseEnd_4028535 < baseStart_4028535 := by decide
  rcases family_descends (prefixWord ++ tailWord_4028535) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4028541 : List Nat := [1, 4, 1, 1, 3, 3, 2, 8]
def baseStart_4028541 : Nat := 118140960795 + 4028541 * 2 ^ 59
def prefixEnd_4028541 : Nat := 4983230072969 + 3 ^ 40 * 4028541 * 2
def baseEnd_4028541 : Nat := 76613995160904742537429

theorem tailTrace_4028541 : CollatzResearch.WordTrace tailWord_4028541 prefixEnd_4028541 76613995160904742537429 := by
  unfold tailWord_4028541
  simp only [CollatzResearch.WordTrace]
  refine ⟨146932961298291451871837477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97955307532194301247891651 146932961298291451871837477)
  ·
    refine ⟨27549930243429647225969527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 146932961298291451871837477 27549930243429647225969527)
    ·
      refine ⟨41324895365144470838954291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27549930243429647225969527 41324895365144470838954291)
      ·
        refine ⟨61987343047716706258431437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41324895365144470838954291 61987343047716706258431437)
        ·
          refine ⟨23245253642893764846911789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 61987343047716706258431437 23245253642893764846911789)
          ·
            refine ⟨8716970116085161817591921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23245253642893764846911789 8716970116085161817591921)
            ·
              refine ⟨6537727587063871363193941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8716970116085161817591921 6537727587063871363193941)
              ·
                refine ⟨76613995160904742537429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 6537727587063871363193941 76613995160904742537429)
                ·
                  rfl

theorem cell23_4028541_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 3, 2, 8].length) (baseStart_4028541 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4028541 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4028541 prefixEnd_4028541 := by exact prefixLift 4028541
  have htrace : WordTrace (prefixWord ++ tailWord_4028541) baseStart_4028541 baseEnd_4028541 := by
    simpa [prefixWord, tailWord_4028541, baseEnd_4028541] using wordTrace_append hprefix tailTrace_4028541
  have hstable : (prefixWord ++ tailWord_4028541).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4028541).length < 2 ^ (prefixWord ++ tailWord_4028541).sum := by decide
  have hdescent : baseEnd_4028541 < baseStart_4028541 := by decide
  rcases family_descends (prefixWord ++ tailWord_4028541) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4028544 : List Nat := [2, 1, 1, 2, 1, 3, 1, 1, 1, 4, 6]
def baseStart_4028544 : Nat := 118140960795 + 4028544 * 2 ^ 59
def prefixEnd_4028544 : Nat := 4983230072969 + 3 ^ 40 * 4028544 * 2
def baseEnd_4028544 : Nat := 2068579409786391536773069

theorem tailTrace_4028544 : CollatzResearch.WordTrace tailWord_4028544 prefixEnd_4028544 2068579409786391536773069 := by
  unfold tailWord_4028544
  simp only [CollatzResearch.WordTrace]
  refine ⟨73466535358640291692098343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97955380478187055589464457 73466535358640291692098343)
  ·
    refine ⟨110199803037960437538147515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73466535358640291692098343 110199803037960437538147515)
    ·
      refine ⟨165299704556940656307221273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110199803037960437538147515 165299704556940656307221273)
      ·
        refine ⟨123974778417705492230415955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 165299704556940656307221273 123974778417705492230415955)
        ·
          refine ⟨185962167626558238345623933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 123974778417705492230415955 185962167626558238345623933)
          ·
            refine ⟨69735812859959339379608975, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 185962167626558238345623933 69735812859959339379608975)
            ·
              refine ⟨104603719289939009069413463, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 69735812859959339379608975 104603719289939009069413463)
              ·
                refine ⟨156905578934908513604120195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 104603719289939009069413463 156905578934908513604120195)
                ·
                  refine ⟨235358368402362770406180293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 156905578934908513604120195 235358368402362770406180293)
                  ·
                    refine ⟨44129694075443019451158805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 235358368402362770406180293 44129694075443019451158805)
                    ·
                      refine ⟨2068579409786391536773069, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 44129694075443019451158805 2068579409786391536773069)
                      ·
                        rfl

theorem cell23_4028544_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 1, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 1, 1, 1, 4, 6].length) (baseStart_4028544 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4028544 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4028544 prefixEnd_4028544 := by exact prefixLift 4028544
  have htrace : WordTrace (prefixWord ++ tailWord_4028544) baseStart_4028544 baseEnd_4028544 := by
    simpa [prefixWord, tailWord_4028544, baseEnd_4028544] using wordTrace_append hprefix tailTrace_4028544
  have hstable : (prefixWord ++ tailWord_4028544).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4028544).length < 2 ^ (prefixWord ++ tailWord_4028544).sum := by decide
  have hdescent : baseEnd_4028544 < baseStart_4028544 := by decide
  rcases family_descends (prefixWord ++ tailWord_4028544) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4028545 : List Nat := [1, 2, 4, 2, 3, 1, 1, 3, 2, 4]
def baseStart_4028545 : Nat := 118140960795 + 4028545 * 2 ^ 59
def prefixEnd_4028545 : Nat := 4983230072969 + 3 ^ 40 * 4028545 * 2
def baseEnd_4028545 : Nat := 689526641089015344286855

theorem tailTrace_4028545 : CollatzResearch.WordTrace tailWord_4028545 prefixEnd_4028545 689526641089015344286855 := by
  unfold tailWord_4028545
  simp only [CollatzResearch.WordTrace]
  refine ⟨146933107190276960554983089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97955404793517973703322059 146933107190276960554983089)
  ·
    refine ⟨110199830392707720416237317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 146933107190276960554983089 110199830392707720416237317)
    ·
      refine ⟨20662468198632697578044497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 110199830392707720416237317 20662468198632697578044497)
      ·
        refine ⟨15496851148974523183533373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20662468198632697578044497 15496851148974523183533373)
        ·
          refine ⟨5811319180865446193825015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15496851148974523183533373 5811319180865446193825015)
          ·
            refine ⟨8716978771298169290737523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5811319180865446193825015 8716978771298169290737523)
            ·
              refine ⟨13075468156947253936106285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8716978771298169290737523 13075468156947253936106285)
              ·
                refine ⟨4903300558855220226039857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13075468156947253936106285 4903300558855220226039857)
                ·
                  refine ⟨3677475419141415169529893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4903300558855220226039857 3677475419141415169529893)
                  ·
                    refine ⟨689526641089015344286855, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3677475419141415169529893 689526641089015344286855)
                    ·
                      rfl

theorem cell23_4028545_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 3, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 3, 1, 1, 3, 2, 4].length) (baseStart_4028545 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4028545 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4028545 prefixEnd_4028545 := by exact prefixLift 4028545
  have htrace : WordTrace (prefixWord ++ tailWord_4028545) baseStart_4028545 baseEnd_4028545 := by
    simpa [prefixWord, tailWord_4028545, baseEnd_4028545] using wordTrace_append hprefix tailTrace_4028545
  have hstable : (prefixWord ++ tailWord_4028545).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4028545).length < 2 ^ (prefixWord ++ tailWord_4028545).sum := by decide
  have hdescent : baseEnd_4028545 < baseStart_4028545 := by decide
  rcases family_descends (prefixWord ++ tailWord_4028545) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4028586 : List Nat := [3, 1, 5, 1, 2, 1, 1, 4, 1, 2, 2]
def baseStart_4028586 : Nat := 118140960795 + 4028586 * 2 ^ 59
def prefixEnd_4028586 : Nat := 4983230072969 + 3 ^ 40 * 4028586 * 2
def baseEnd_4028586 : Nat := 2068600975973880372447877

theorem tailTrace_4028586 : CollatzResearch.WordTrace tailWord_4028586 prefixEnd_4028586 2068600975973880372447877 := by
  unfold tailWord_4028586
  simp only [CollatzResearch.WordTrace]
  refine ⟨36733650645782106139306403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 97956401722085616371483741 36733650645782106139306403)
  ·
    refine ⟨55100475968673159208959605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36733650645782106139306403 55100475968673159208959605)
    ·
      refine ⟨5165669622063108675839963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 55100475968673159208959605 5165669622063108675839963)
      ·
        refine ⟨7748504433094663013759945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5165669622063108675839963 7748504433094663013759945)
        ·
          refine ⟨5811378324820997260319959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7748504433094663013759945 5811378324820997260319959)
          ·
            refine ⟨8717067487231495890479939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5811378324820997260319959 8717067487231495890479939)
            ·
              refine ⟨13075601230847243835719909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8717067487231495890479939 13075601230847243835719909)
              ·
                refine ⟨2451675230783858219197483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13075601230847243835719909 2451675230783858219197483)
                ·
                  refine ⟨3677512846175787328796225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2451675230783858219197483 3677512846175787328796225)
                  ·
                    refine ⟨2758134634631840496597169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3677512846175787328796225 2758134634631840496597169)
                    ·
                      refine ⟨2068600975973880372447877, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2758134634631840496597169 2068600975973880372447877)
                      ·
                        rfl

theorem cell23_4028586_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 2, 1, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 2, 1, 1, 4, 1, 2, 2].length) (baseStart_4028586 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4028586 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4028586 prefixEnd_4028586 := by exact prefixLift 4028586
  have htrace : WordTrace (prefixWord ++ tailWord_4028586) baseStart_4028586 baseEnd_4028586 := by
    simpa [prefixWord, tailWord_4028586, baseEnd_4028586] using wordTrace_append hprefix tailTrace_4028586
  have hstable : (prefixWord ++ tailWord_4028586).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4028586).length < 2 ^ (prefixWord ++ tailWord_4028586).sum := by decide
  have hdescent : baseEnd_4028586 < baseStart_4028586 := by decide
  rcases family_descends (prefixWord ++ tailWord_4028586) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4028601 : List Nat := [1, 2, 1, 4, 1, 2, 3, 1, 2, 6]
def baseStart_4028601 : Nat := 118140960795 + 4028601 * 2 ^ 59
def prefixEnd_4028601 : Nat := 4983230072969 + 3 ^ 40 * 4028601 * 2
def baseEnd_4028601 : Nat := 689536226061232604586769

theorem tailTrace_4028601 : CollatzResearch.WordTrace tailWord_4028601 prefixEnd_4028601 689536226061232604586769 := by
  unfold tailWord_4028601
  simp only [CollatzResearch.WordTrace]
  refine ⟨146935149678074082119021657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97956766452049388079347771 146935149678074082119021657)
  ·
    refine ⟨110201362258555561589266243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 146935149678074082119021657 110201362258555561589266243)
    ·
      refine ⟨165302043387833342383899365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110201362258555561589266243 165302043387833342383899365)
      ·
        refine ⟨30994133135218751696981131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 165302043387833342383899365 30994133135218751696981131)
        ·
          refine ⟨46491199702828127545471697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30994133135218751696981131 46491199702828127545471697)
          ·
            refine ⟨34868399777121095659103773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46491199702828127545471697 34868399777121095659103773)
            ·
              refine ⟨13075649916420410872163915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34868399777121095659103773 13075649916420410872163915)
              ·
                refine ⟨19613474874630616308245873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13075649916420410872163915 19613474874630616308245873)
                ·
                  refine ⟨14710106155972962231184405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19613474874630616308245873 14710106155972962231184405)
                  ·
                    refine ⟨689536226061232604586769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 14710106155972962231184405 689536226061232604586769)
                    ·
                      rfl

theorem cell23_4028601_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 3, 1, 2, 6].length) (baseStart_4028601 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4028601 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4028601 prefixEnd_4028601 := by exact prefixLift 4028601
  have htrace : WordTrace (prefixWord ++ tailWord_4028601) baseStart_4028601 baseEnd_4028601 := by
    simpa [prefixWord, tailWord_4028601, baseEnd_4028601] using wordTrace_append hprefix tailTrace_4028601
  have hstable : (prefixWord ++ tailWord_4028601).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4028601).length < 2 ^ (prefixWord ++ tailWord_4028601).sum := by decide
  have hdescent : baseEnd_4028601 < baseStart_4028601 := by decide
  rcases family_descends (prefixWord ++ tailWord_4028601) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4028636 : List Nat := [2, 2, 5, 2, 1, 2, 1, 2, 2, 1, 3]
def baseStart_4028636 : Nat := 118140960795 + 4028636 * 2 ^ 59
def prefixEnd_4028636 : Nat := 4983230072969 + 3 ^ 40 * 4028636 * 2
def baseEnd_4028636 : Nat := 2068626650006605176822647

theorem tailTrace_4028636 : CollatzResearch.WordTrace tailWord_4028636 prefixEnd_4028636 2068626650006605176822647 := by
  unfold tailWord_4028636
  simp only [CollatzResearch.WordTrace]
  refine ⟨73468213116473641548272881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97957617488631522064363841 73468213116473641548272881)
  ·
    refine ⟨55101159837355231161204661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73468213116473641548272881 55101159837355231161204661)
    ·
      refine ⟨5165733734752052921362937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 55101159837355231161204661 5165733734752052921362937)
      ·
        refine ⟨3874300301064039691022203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5165733734752052921362937 3874300301064039691022203)
        ·
          refine ⟨5811450451596059536533305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3874300301064039691022203 5811450451596059536533305)
          ·
            refine ⟨4358587838697044652399979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5811450451596059536533305 4358587838697044652399979)
            ·
              refine ⟨6537881758045566978599969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4358587838697044652399979 6537881758045566978599969)
              ·
                refine ⟨4903411318534175233949977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6537881758045566978599969 4903411318534175233949977)
                ·
                  refine ⟨3677558488900631425462483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4903411318534175233949977 3677558488900631425462483)
                  ·
                    refine ⟨5516337733350947138193725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3677558488900631425462483 5516337733350947138193725)
                    ·
                      refine ⟨2068626650006605176822647, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5516337733350947138193725 2068626650006605176822647)
                      ·
                        rfl

theorem cell23_4028636_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 2, 1, 2, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 2, 1, 2, 1, 2, 2, 1, 3].length) (baseStart_4028636 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4028636 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4028636 prefixEnd_4028636 := by exact prefixLift 4028636
  have htrace : WordTrace (prefixWord ++ tailWord_4028636) baseStart_4028636 baseEnd_4028636 := by
    simpa [prefixWord, tailWord_4028636, baseEnd_4028636] using wordTrace_append hprefix tailTrace_4028636
  have hstable : (prefixWord ++ tailWord_4028636).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4028636).length < 2 ^ (prefixWord ++ tailWord_4028636).sum := by decide
  have hdescent : baseEnd_4028636 < baseStart_4028636 := by decide
  rcases family_descends (prefixWord ++ tailWord_4028636) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4028648 : List Nat := [2, 1, 4, 1, 2, 3, 2, 1, 7]
def baseStart_4028648 : Nat := 118140960795 + 4028648 * 2 ^ 59
def prefixEnd_4028648 : Nat := 4983230072969 + 3 ^ 40 * 4028648 * 2
def baseEnd_4028648 : Nat := 229848090197162125541399

theorem tailTrace_4028648 : CollatzResearch.WordTrace tailWord_4028648 prefixEnd_4028648 229848090197162125541399 := by
  unfold tailWord_4028648
  simp only [CollatzResearch.WordTrace]
  refine ⟨73468431954451904572991299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97957909272602539430655065 73468431954451904572991299)
  ·
    refine ⟨110202647931677856859486949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73468431954451904572991299 110202647931677856859486949)
    ·
      refine ⟨20662996487189598161153803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 110202647931677856859486949 20662996487189598161153803)
      ·
        refine ⟨30994494730784397241730705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20662996487189598161153803 30994494730784397241730705)
        ·
          refine ⟨23245871048088297931298029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30994494730784397241730705 23245871048088297931298029)
          ·
            refine ⟨8717201643033111724236761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23245871048088297931298029 8717201643033111724236761)
            ·
              refine ⟨6537901232274833793177571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8717201643033111724236761 6537901232274833793177571)
              ·
                refine ⟨9806851848412250689766357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6537901232274833793177571 9806851848412250689766357)
                ·
                  refine ⟨229848090197162125541399, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 9806851848412250689766357 229848090197162125541399)
                  ·
                    rfl

theorem cell23_4028648_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 3, 2, 1, 7].length) (baseStart_4028648 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4028648 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4028648 prefixEnd_4028648 := by exact prefixLift 4028648
  have htrace : WordTrace (prefixWord ++ tailWord_4028648) baseStart_4028648 baseEnd_4028648 := by
    simpa [prefixWord, tailWord_4028648, baseEnd_4028648] using wordTrace_append hprefix tailTrace_4028648
  have hstable : (prefixWord ++ tailWord_4028648).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4028648).length < 2 ^ (prefixWord ++ tailWord_4028648).sum := by decide
  have hdescent : baseEnd_4028648 < baseStart_4028648 := by decide
  rcases family_descends (prefixWord ++ tailWord_4028648) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4028735 : List Nat := [1, 1, 2, 2, 4, 1, 4, 1, 2, 2, 3]
def baseStart_4028735 : Nat := 118140960795 + 4028735 * 2 ^ 59
def prefixEnd_4028735 : Nat := 4983230072969 + 3 ^ 40 * 4028735 * 2
def baseEnd_4028735 : Nat := 2068677484591400289484691

theorem tailTrace_4028735 : CollatzResearch.WordTrace tailWord_4028735 prefixEnd_4028735 2068677484591400289484691 := by
  unfold tailWord_4028735
  simp only [CollatzResearch.WordTrace]
  refine ⟨146940037059588623004399659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97960024706392415336266439 146940037059588623004399659)
  ·
    refine ⟨220410055589382934506599489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146940037059588623004399659 220410055589382934506599489)
    ·
      refine ⟨165307541692037200879949617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 220410055589382934506599489 165307541692037200879949617)
      ·
        refine ⟨123980656269027900659962213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 165307541692037200879949617 123980656269027900659962213)
        ·
          refine ⟨23246373050442731373742915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 123980656269027900659962213 23246373050442731373742915)
          ·
            refine ⟨34869559575664097060614373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23246373050442731373742915 34869559575664097060614373)
            ·
              refine ⟨6538042420437018198865195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 34869559575664097060614373 6538042420437018198865195)
              ·
                refine ⟨9807063630655527298297793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6538042420437018198865195 9807063630655527298297793)
                ·
                  refine ⟨7355297722991645473723345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9807063630655527298297793 7355297722991645473723345)
                  ·
                    refine ⟨5516473292243734105292509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7355297722991645473723345 5516473292243734105292509)
                    ·
                      refine ⟨2068677484591400289484691, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5516473292243734105292509 2068677484591400289484691)
                      ·
                        rfl

theorem cell23_4028735_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 4, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 4, 1, 2, 2, 3].length) (baseStart_4028735 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4028735 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4028735 prefixEnd_4028735 := by exact prefixLift 4028735
  have htrace : WordTrace (prefixWord ++ tailWord_4028735) baseStart_4028735 baseEnd_4028735 := by
    simpa [prefixWord, tailWord_4028735, baseEnd_4028735] using wordTrace_append hprefix tailTrace_4028735
  have hstable : (prefixWord ++ tailWord_4028735).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4028735).length < 2 ^ (prefixWord ++ tailWord_4028735).sum := by decide
  have hdescent : baseEnd_4028735 < baseStart_4028735 := by decide
  rcases family_descends (prefixWord ++ tailWord_4028735) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4028741 : List Nat := [1, 3, 1, 1, 1, 2, 1, 1, 3, 1, 8]
def baseStart_4028741 : Nat := 118140960795 + 4028741 * 2 ^ 59
def prefixEnd_4028741 : Nat := 4983230072969 + 3 ^ 40 * 4028741 * 2
def baseEnd_4028741 : Nat := 2068680565475327266009663

theorem tailTrace_4028741 : CollatzResearch.WordTrace tailWord_4028741 prefixEnd_4028741 2068680565475327266009663 := by
  unfold tailWord_4028741
  simp only [CollatzResearch.WordTrace]
  refine ⟨146940255897566886029118077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97960170598377924019412051 146940255897566886029118077)
  ·
    refine ⟨55102595961587582260919279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 146940255897566886029118077 55102595961587582260919279)
    ·
      refine ⟨82653893942381373391378919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55102595961587582260919279 82653893942381373391378919)
      ·
        refine ⟨123980840913572060087068379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82653893942381373391378919 123980840913572060087068379)
        ·
          refine ⟨185971261370358090130602569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 123980840913572060087068379 185971261370358090130602569)
          ·
            refine ⟨139478446027768567597951927, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 185971261370358090130602569 139478446027768567597951927)
            ·
              refine ⟨209217669041652851396927891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 139478446027768567597951927 209217669041652851396927891)
              ·
                refine ⟨313826503562479277095391837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 209217669041652851396927891 313826503562479277095391837)
                ·
                  refine ⟨117684938835929728910771939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 313826503562479277095391837 117684938835929728910771939)
                  ·
                    refine ⟨176527408253894593366157909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 117684938835929728910771939 176527408253894593366157909)
                    ·
                      refine ⟨2068680565475327266009663, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 176527408253894593366157909 2068680565475327266009663)
                      ·
                        rfl

theorem cell23_4028741_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 1, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 1, 1, 3, 1, 8].length) (baseStart_4028741 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4028741 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4028741 prefixEnd_4028741 := by exact prefixLift 4028741
  have htrace : WordTrace (prefixWord ++ tailWord_4028741) baseStart_4028741 baseEnd_4028741 := by
    simpa [prefixWord, tailWord_4028741, baseEnd_4028741] using wordTrace_append hprefix tailTrace_4028741
  have hstable : (prefixWord ++ tailWord_4028741).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4028741).length < 2 ^ (prefixWord ++ tailWord_4028741).sum := by decide
  have hdescent : baseEnd_4028741 < baseStart_4028741 := by decide
  rcases family_descends (prefixWord ++ tailWord_4028741) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4028835 : List Nat := [1, 1, 1, 4, 1, 4, 3, 1, 1, 2, 4]
def baseStart_4028835 : Nat := 118140960795 + 4028835 * 2 ^ 59
def prefixEnd_4028835 : Nat := 4983230072969 + 3 ^ 40 * 4028835 * 2
def baseEnd_4028835 : Nat := 2068728832656849898234231

theorem tailTrace_4028835 : CollatzResearch.WordTrace tailWord_4028835 prefixEnd_4028835 2068728832656849898234231 := by
  unfold tailWord_4028835
  simp only [CollatzResearch.WordTrace]
  refine ⟨146943684359226340083039959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97962456239484226722026639 146943684359226340083039959)
  ·
    refine ⟨220415526538839510124559939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146943684359226340083039959 220415526538839510124559939)
    ·
      refine ⟨330623289808259265186839909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 220415526538839510124559939 330623289808259265186839909)
      ·
        refine ⟨61991866839048612222532483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 330623289808259265186839909 61991866839048612222532483)
        ·
          refine ⟨92987800258572918333798725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61991866839048612222532483 92987800258572918333798725)
          ·
            refine ⟨17435212548482422187587261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 92987800258572918333798725 17435212548482422187587261)
            ·
              refine ⟨6538204705680908320345223, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17435212548482422187587261 6538204705680908320345223)
              ·
                refine ⟨9807307058521362480517835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6538204705680908320345223 9807307058521362480517835)
                ·
                  refine ⟨14710960587782043720776753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9807307058521362480517835 14710960587782043720776753)
                  ·
                    refine ⟨11033220440836532790582565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14710960587782043720776753 11033220440836532790582565)
                    ·
                      refine ⟨2068728832656849898234231, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11033220440836532790582565 2068728832656849898234231)
                      ·
                        rfl

theorem cell23_4028835_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 4, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 4, 3, 1, 1, 2, 4].length) (baseStart_4028835 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4028835 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4028835 prefixEnd_4028835 := by exact prefixLift 4028835
  have htrace : WordTrace (prefixWord ++ tailWord_4028835) baseStart_4028835 baseEnd_4028835 := by
    simpa [prefixWord, tailWord_4028835, baseEnd_4028835] using wordTrace_append hprefix tailTrace_4028835
  have hstable : (prefixWord ++ tailWord_4028835).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4028835).length < 2 ^ (prefixWord ++ tailWord_4028835).sum := by decide
  have hdescent : baseEnd_4028835 < baseStart_4028835 := by decide
  rcases family_descends (prefixWord ++ tailWord_4028835) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4028839 : List Nat := [1, 1, 6, 1, 1, 2, 2, 2, 3, 2, 2]
def baseStart_4028839 : Nat := 118140960795 + 4028839 * 2 ^ 59
def prefixEnd_4028839 : Nat := 4983230072969 + 3 ^ 40 * 4028839 * 2
def baseEnd_4028839 : Nat := 2068730886579467882584213

theorem tailTrace_4028839 : CollatzResearch.WordTrace tailWord_4028839 prefixEnd_4028839 2068730886579467882584213 := by
  unfold tailWord_4028839
  simp only [CollatzResearch.WordTrace]
  refine ⟨146943830251211848766185571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97962553500807899177457047 146943830251211848766185571)
  ·
    refine ⟨220415745376817773149278357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146943830251211848766185571 220415745376817773149278357)
    ·
      refine ⟨10331988064538333116372423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 220415745376817773149278357 10331988064538333116372423)
      ·
        refine ⟨15497982096807499674558635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10331988064538333116372423 15497982096807499674558635)
        ·
          refine ⟨23246973145211249511837953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15497982096807499674558635 23246973145211249511837953)
          ·
            refine ⟨17435229858908437133878465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23246973145211249511837953 17435229858908437133878465)
            ·
              refine ⟨13076422394181327850408849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17435229858908437133878465 13076422394181327850408849)
              ·
                refine ⟨9807316795635995887806637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13076422394181327850408849 9807316795635995887806637)
                ·
                  refine ⟨3677743798363498457927489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9807316795635995887806637 3677743798363498457927489)
                  ·
                    refine ⟨2758307848772623843445617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3677743798363498457927489 2758307848772623843445617)
                    ·
                      refine ⟨2068730886579467882584213, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2758307848772623843445617 2068730886579467882584213)
                      ·
                        rfl

theorem cell23_4028839_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 2, 2, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 2, 2, 2, 3, 2, 2].length) (baseStart_4028839 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4028839 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4028839 prefixEnd_4028839 := by exact prefixLift 4028839
  have htrace : WordTrace (prefixWord ++ tailWord_4028839) baseStart_4028839 baseEnd_4028839 := by
    simpa [prefixWord, tailWord_4028839, baseEnd_4028839] using wordTrace_append hprefix tailTrace_4028839
  have hstable : (prefixWord ++ tailWord_4028839).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4028839).length < 2 ^ (prefixWord ++ tailWord_4028839).sum := by decide
  have hdescent : baseEnd_4028839 < baseStart_4028839 := by decide
  rcases family_descends (prefixWord ++ tailWord_4028839) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4028872 : List Nat := [2, 1, 3, 1, 3, 2, 2, 1, 4, 1, 3]
def baseStart_4028872 : Nat := 118140960795 + 4028872 * 2 ^ 59
def prefixEnd_4028872 : Nat := 4983230072969 + 3 ^ 40 * 4028872 * 2
def baseEnd_4028872 : Nat := 2068747831441066253471561

theorem tailTrace_4028872 : CollatzResearch.WordTrace tailWord_4028872 prefixEnd_4028872 2068747831441066253471561 := by
  unfold tailWord_4028872
  simp only [CollatzResearch.WordTrace]
  refine ⟨73472516930046147701068435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97963355906728196934757913 73472516930046147701068435)
  ·
    refine ⟨110208775395069221551602653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73472516930046147701068435 110208775395069221551602653)
    ·
      refine ⟨41328290773150958081850995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 110208775395069221551602653 41328290773150958081850995)
      ·
        refine ⟨61992436159726437122776493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41328290773150958081850995 61992436159726437122776493)
        ·
          refine ⟨23247163559897413921041185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 61992436159726437122776493 23247163559897413921041185)
          ·
            refine ⟨17435372669923060440780889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23247163559897413921041185 17435372669923060440780889)
            ·
              refine ⟨13076529502442295330585667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17435372669923060440780889 13076529502442295330585667)
              ·
                refine ⟨19614794253663442995878501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13076529502442295330585667 19614794253663442995878501)
                ·
                  refine ⟨3677773922561895561727219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 19614794253663442995878501 3677773922561895561727219)
                  ·
                    refine ⟨5516660883842843342590829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3677773922561895561727219 5516660883842843342590829)
                    ·
                      refine ⟨2068747831441066253471561, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5516660883842843342590829 2068747831441066253471561)
                      ·
                        rfl

theorem cell23_4028872_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 2, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 2, 2, 1, 4, 1, 3].length) (baseStart_4028872 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4028872 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4028872 prefixEnd_4028872 := by exact prefixLift 4028872
  have htrace : WordTrace (prefixWord ++ tailWord_4028872) baseStart_4028872 baseEnd_4028872 := by
    simpa [prefixWord, tailWord_4028872, baseEnd_4028872] using wordTrace_append hprefix tailTrace_4028872
  have hstable : (prefixWord ++ tailWord_4028872).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4028872).length < 2 ^ (prefixWord ++ tailWord_4028872).sum := by decide
  have hdescent : baseEnd_4028872 < baseStart_4028872 := by decide
  rcases family_descends (prefixWord ++ tailWord_4028872) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4028888 : List Nat := [2, 1, 2, 2, 2, 1, 1, 3, 1, 8]
def baseStart_4028888 : Nat := 118140960795 + 4028888 * 2 ^ 59
def prefixEnd_4028888 : Nat := 4983230072969 + 3 ^ 40 * 4028888 * 2
def baseEnd_4028888 : Nat := 689585349043846063623829

theorem tailTrace_4028888 : CollatzResearch.WordTrace tailWord_4028888 prefixEnd_4028888 689585349043846063623829 := by
  unfold tailWord_4028888
  simp only [CollatzResearch.WordTrace]
  refine ⟨73472808714017165067359659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97963744952022886756479545 73472808714017165067359659)
  ·
    refine ⟨110209213071025747601039489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73472808714017165067359659 110209213071025747601039489)
    ·
      refine ⟨82656909803269310700779617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 110209213071025747601039489 82656909803269310700779617)
      ·
        refine ⟨61992682352451983025584713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 82656909803269310700779617 61992682352451983025584713)
        ·
          refine ⟨46494511764338987269188535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61992682352451983025584713 46494511764338987269188535)
          ·
            refine ⟨69741767646508480903782803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46494511764338987269188535 69741767646508480903782803)
            ·
              refine ⟨104612651469762721355674205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 69741767646508480903782803 104612651469762721355674205)
              ·
                refine ⟨39229744301161020508377827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 104612651469762721355674205 39229744301161020508377827)
                ·
                  refine ⟨58844616451741530762566741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39229744301161020508377827 58844616451741530762566741)
                  ·
                    refine ⟨689585349043846063623829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 58844616451741530762566741 689585349043846063623829)
                    ·
                      rfl

theorem cell23_4028888_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 1, 3, 1, 8].length) (baseStart_4028888 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4028888 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4028888 prefixEnd_4028888 := by exact prefixLift 4028888
  have htrace : WordTrace (prefixWord ++ tailWord_4028888) baseStart_4028888 baseEnd_4028888 := by
    simpa [prefixWord, tailWord_4028888, baseEnd_4028888] using wordTrace_append hprefix tailTrace_4028888
  have hstable : (prefixWord ++ tailWord_4028888).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4028888).length < 2 ^ (prefixWord ++ tailWord_4028888).sum := by decide
  have hdescent : baseEnd_4028888 < baseStart_4028888 := by decide
  rcases family_descends (prefixWord ++ tailWord_4028888) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4028899 : List Nat := [1, 1, 1, 6, 3, 1, 1, 1, 3, 3, 2]
def baseStart_4028899 : Nat := 118140960795 + 4028899 * 2 ^ 59
def prefixEnd_4028899 : Nat := 4983230072969 + 3 ^ 40 * 4028899 * 2
def baseEnd_4028899 : Nat := 2068761695418737647833937

theorem tailTrace_4028899 : CollatzResearch.WordTrace tailWord_4028899 prefixEnd_4028899 2068761695418737647833937 := by
  unfold tailWord_4028899
  simp only [CollatzResearch.WordTrace]
  refine ⟨146946018630994479013369751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97964012420662986008913167 146946018630994479013369751)
  ·
    refine ⟨220419027946491718520054627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146946018630994479013369751 220419027946491718520054627)
    ·
      refine ⟨330628541919737577780081941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 220419027946491718520054627 330628541919737577780081941)
      ·
        refine ⟨15498212902487698958441341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 330628541919737577780081941 15498212902487698958441341)
        ·
          refine ⟨5811829838432887109415503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15498212902487698958441341 5811829838432887109415503)
          ·
            refine ⟨8717744757649330664123255, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5811829838432887109415503 8717744757649330664123255)
            ·
              refine ⟨13076617136473995996184883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8717744757649330664123255 13076617136473995996184883)
              ·
                refine ⟨19614925704710993994277325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13076617136473995996184883 19614925704710993994277325)
                ·
                  refine ⟨7355597139266622747853997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19614925704710993994277325 7355597139266622747853997)
                  ·
                    refine ⟨2758348927224983530445249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7355597139266622747853997 2758348927224983530445249)
                    ·
                      refine ⟨2068761695418737647833937, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2758348927224983530445249 2068761695418737647833937)
                      ·
                        rfl

theorem cell23_4028899_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 3, 1, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 3, 1, 1, 1, 3, 3, 2].length) (baseStart_4028899 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4028899 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4028899 prefixEnd_4028899 := by exact prefixLift 4028899
  have htrace : WordTrace (prefixWord ++ tailWord_4028899) baseStart_4028899 baseEnd_4028899 := by
    simpa [prefixWord, tailWord_4028899, baseEnd_4028899] using wordTrace_append hprefix tailTrace_4028899
  have hstable : (prefixWord ++ tailWord_4028899).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4028899).length < 2 ^ (prefixWord ++ tailWord_4028899).sum := by decide
  have hdescent : baseEnd_4028899 < baseStart_4028899 := by decide
  rcases family_descends (prefixWord ++ tailWord_4028899) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4028912 : List Nat := [2, 1, 1, 1, 3, 3, 3, 2, 1, 4, 2]
def baseStart_4028912 : Nat := 118140960795 + 4028912 * 2 ^ 59
def prefixEnd_4028912 : Nat := 4983230072969 + 3 ^ 40 * 4028912 * 2
def baseEnd_4028912 : Nat := 2068768370667246096971377

theorem tailTrace_4028912 : CollatzResearch.WordTrace tailWord_4028912 prefixEnd_4028912 2068768370667246096971377 := by
  unfold tailWord_4028912
  simp only [CollatzResearch.WordTrace]
  refine ⟨73473246389973691116796495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97964328519964921489061993 73473246389973691116796495)
  ·
    refine ⟨110209869584960536675194743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73473246389973691116796495 110209869584960536675194743)
    ·
      refine ⟨165314804377440805012792115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110209869584960536675194743 165314804377440805012792115)
      ·
        refine ⟨247972206566161207519188173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 165314804377440805012792115 247972206566161207519188173)
        ·
          refine ⟨92989577462310452819695565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 247972206566161207519188173 92989577462310452819695565)
          ·
            refine ⟨34871091548366419807385837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 92989577462310452819695565 34871091548366419807385837)
            ·
              refine ⟨13076659330637407427769689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34871091548366419807385837 13076659330637407427769689)
              ·
                refine ⟨9807494497978055570827267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13076659330637407427769689 9807494497978055570827267)
                ·
                  refine ⟨14711241746967083356240901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9807494497978055570827267 14711241746967083356240901)
                  ·
                    refine ⟨2758357827556328129295169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 14711241746967083356240901 2758357827556328129295169)
                    ·
                      refine ⟨2068768370667246096971377, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2758357827556328129295169 2068768370667246096971377)
                      ·
                        rfl

theorem cell23_4028912_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 3, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 3, 2, 1, 4, 2].length) (baseStart_4028912 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4028912 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4028912 prefixEnd_4028912 := by exact prefixLift 4028912
  have htrace : WordTrace (prefixWord ++ tailWord_4028912) baseStart_4028912 baseEnd_4028912 := by
    simpa [prefixWord, tailWord_4028912, baseEnd_4028912] using wordTrace_append hprefix tailTrace_4028912
  have hstable : (prefixWord ++ tailWord_4028912).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4028912).length < 2 ^ (prefixWord ++ tailWord_4028912).sum := by decide
  have hdescent : baseEnd_4028912 < baseStart_4028912 := by decide
  rcases family_descends (prefixWord ++ tailWord_4028912) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4028925 : List Nat := [1, 4, 1, 1, 1, 3, 2, 2, 2, 2, 4]
def baseStart_4028925 : Nat := 118140960795 + 4028925 * 2 ^ 59
def prefixEnd_4028925 : Nat := 4983230072969 + 3 ^ 40 * 4028925 * 2
def baseEnd_4028925 : Nat := 2068775045915754546108817

theorem tailTrace_4028925 : CollatzResearch.WordTrace tailWord_4028925 prefixEnd_4028925 2068775045915754546108817 := by
  unfold tailWord_4028925
  simp only [CollatzResearch.WordTrace]
  refine ⟨146946966928900285453816229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97964644619266856969210819 146946966928900285453816229)
  ·
    refine ⟨27552556299168803522590543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 146946966928900285453816229 27552556299168803522590543)
    ·
      refine ⟨41328834448753205283885815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27552556299168803522590543 41328834448753205283885815)
      ·
        refine ⟨61993251673129807925828723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41328834448753205283885815 61993251673129807925828723)
        ·
          refine ⟨92989877509694711888743085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61993251673129807925828723 92989877509694711888743085)
          ·
            refine ⟨34871204066135516958278657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 92989877509694711888743085 34871204066135516958278657)
            ·
              refine ⟨26153403049601637718708993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34871204066135516958278657 26153403049601637718708993)
              ·
                refine ⟨19615052287201228289031745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26153403049601637718708993 19615052287201228289031745)
                ·
                  refine ⟨14711289215400921216773809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19615052287201228289031745 14711289215400921216773809)
                  ·
                    refine ⟨11033466911550690912580357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14711289215400921216773809 11033466911550690912580357)
                    ·
                      refine ⟨2068775045915754546108817, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11033466911550690912580357 2068775045915754546108817)
                      ·
                        rfl

theorem cell23_4028925_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 2, 2, 2, 2, 4].length) (baseStart_4028925 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4028925 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4028925 prefixEnd_4028925 := by exact prefixLift 4028925
  have htrace : WordTrace (prefixWord ++ tailWord_4028925) baseStart_4028925 baseEnd_4028925 := by
    simpa [prefixWord, tailWord_4028925, baseEnd_4028925] using wordTrace_append hprefix tailTrace_4028925
  have hstable : (prefixWord ++ tailWord_4028925).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4028925).length < 2 ^ (prefixWord ++ tailWord_4028925).sum := by decide
  have hdescent : baseEnd_4028925 < baseStart_4028925 := by decide
  rcases family_descends (prefixWord ++ tailWord_4028925) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4028932 : List Nat := [2, 3, 2, 3, 1, 1, 1, 1, 2, 4, 3]
def baseStart_4028932 : Nat := 118140960795 + 4028932 * 2 ^ 59
def prefixEnd_4028932 : Nat := 4983230072969 + 3 ^ 40 * 4028932 * 2
def baseEnd_4028932 : Nat := 2068778640280336018721285

theorem tailTrace_4028932 : CollatzResearch.WordTrace tailWord_4028932 prefixEnd_4028932 2068778640280336018721285 := by
  unfold tailWord_4028932
  simp only [CollatzResearch.WordTrace]
  refine ⟨73473611119937462824660525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97964814826583283766214033 73473611119937462824660525)
  ·
    refine ⟨27552604169976548559247697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 73473611119937462824660525 27552604169976548559247697)
    ·
      refine ⟨20664453127482411419435773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27552604169976548559247697 20664453127482411419435773)
      ·
        refine ⟨7749169922805904282288415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20664453127482411419435773 7749169922805904282288415)
        ·
          refine ⟨11623754884208856423432623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7749169922805904282288415 11623754884208856423432623)
          ·
            refine ⟨17435632326313284635148935, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11623754884208856423432623 17435632326313284635148935)
            ·
              refine ⟨26153448489469926952723403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17435632326313284635148935 26153448489469926952723403)
              ·
                refine ⟨39230172734204890429085105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26153448489469926952723403 39230172734204890429085105)
                ·
                  refine ⟨29422629550653667821813829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 39230172734204890429085105 29422629550653667821813829)
                  ·
                    refine ⟨5516743040747562716590093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 29422629550653667821813829 5516743040747562716590093)
                    ·
                      refine ⟨2068778640280336018721285, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5516743040747562716590093 2068778640280336018721285)
                      ·
                        rfl

theorem cell23_4028932_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 1, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 1, 1, 1, 2, 4, 3].length) (baseStart_4028932 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4028932 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4028932 prefixEnd_4028932 := by exact prefixLift 4028932
  have htrace : WordTrace (prefixWord ++ tailWord_4028932) baseStart_4028932 baseEnd_4028932 := by
    simpa [prefixWord, tailWord_4028932, baseEnd_4028932] using wordTrace_append hprefix tailTrace_4028932
  have hstable : (prefixWord ++ tailWord_4028932).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4028932).length < 2 ^ (prefixWord ++ tailWord_4028932).sum := by decide
  have hdescent : baseEnd_4028932 < baseStart_4028932 := by decide
  rcases family_descends (prefixWord ++ tailWord_4028932) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4028942 : List Nat := [4, 1, 1, 2, 3, 2, 1, 1, 2, 2, 4]
def baseStart_4028942 : Nat := 118140960795 + 4028942 * 2 ^ 59
def prefixEnd_4028942 : Nat := 4983230072969 + 3 ^ 40 * 4028942 * 2
def baseEnd_4028942 : Nat := 2068783775086880979596239

theorem tailTrace_4028942 : CollatzResearch.WordTrace tailWord_4028942 prefixEnd_4028942 2068783775086880979596239 := by
  unfold tailWord_4028942
  simp only [CollatzResearch.WordTrace]
  refine ⟨18368448371229837169648135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 97965057979892464904790053 18368448371229837169648135)
  ·
    refine ⟨27552672556844755754472203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18368448371229837169648135 27552672556844755754472203)
    ·
      refine ⟨41329008835267133631708305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27552672556844755754472203 41329008835267133631708305)
      ·
        refine ⟨30996756626450350223781229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41329008835267133631708305 30996756626450350223781229)
        ·
          refine ⟨11623783734918881333917961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30996756626450350223781229 11623783734918881333917961)
          ·
            refine ⟨8717837801189161000438471, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11623783734918881333917961 8717837801189161000438471)
            ·
              refine ⟨13076756701783741500657707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8717837801189161000438471 13076756701783741500657707)
              ·
                refine ⟨19615135052675612250986561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13076756701783741500657707 19615135052675612250986561)
                ·
                  refine ⟨14711351289506709188239921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19615135052675612250986561 14711351289506709188239921)
                  ·
                    refine ⟨11033513467130031891179941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14711351289506709188239921 11033513467130031891179941)
                    ·
                      refine ⟨2068783775086880979596239, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11033513467130031891179941 2068783775086880979596239)
                      ·
                        rfl

theorem cell23_4028942_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 2, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 2, 1, 1, 2, 2, 4].length) (baseStart_4028942 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4028942 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4028942 prefixEnd_4028942 := by exact prefixLift 4028942
  have htrace : WordTrace (prefixWord ++ tailWord_4028942) baseStart_4028942 baseEnd_4028942 := by
    simpa [prefixWord, tailWord_4028942, baseEnd_4028942] using wordTrace_append hprefix tailTrace_4028942
  have hstable : (prefixWord ++ tailWord_4028942).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4028942).length < 2 ^ (prefixWord ++ tailWord_4028942).sum := by decide
  have hdescent : baseEnd_4028942 < baseStart_4028942 := by decide
  rcases family_descends (prefixWord ++ tailWord_4028942) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4028967 : List Nat := [1, 1, 7, 2, 2, 1, 2, 1, 1, 3, 2]
def baseStart_4028967 : Nat := 118140960795 + 4028967 * 2 ^ 59
def prefixEnd_4028967 : Nat := 4983230072969 + 3 ^ 40 * 4028967 * 2
def baseEnd_4028967 : Nat := 2068796612103243381783625

theorem tailTrace_4028967 : CollatzResearch.WordTrace tailWord_4028967 prefixEnd_4028967 2068796612103243381783625 := by
  unfold tailWord_4028967
  simp only [CollatzResearch.WordTrace]
  refine ⟨146948498794748126626845155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97965665863165417751230103 146948498794748126626845155)
  ·
    refine ⟨220422748192122189940267733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146948498794748126626845155 220422748192122189940267733)
    ·
      refine ⟨5166158160752863826725025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 220422748192122189940267733 5166158160752863826725025)
      ·
        refine ⟨3874618620564647870043769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5166158160752863826725025 3874618620564647870043769)
        ·
          refine ⟨2905963965423485902532827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3874618620564647870043769 2905963965423485902532827)
          ·
            refine ⟨4358945948135228853799241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2905963965423485902532827 4358945948135228853799241)
            ·
              refine ⟨3269209461101421640349431, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4358945948135228853799241 3269209461101421640349431)
              ·
                refine ⟨4903814191652132460524147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3269209461101421640349431 4903814191652132460524147)
                ·
                  refine ⟨7355721287478198690786221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4903814191652132460524147 7355721287478198690786221)
                  ·
                    refine ⟨2758395482804324509044833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7355721287478198690786221 2758395482804324509044833)
                    ·
                      refine ⟨2068796612103243381783625, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2758395482804324509044833 2068796612103243381783625)
                      ·
                        rfl

theorem cell23_4028967_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 2, 2, 1, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 2, 2, 1, 2, 1, 1, 3, 2].length) (baseStart_4028967 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4028967 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4028967 prefixEnd_4028967 := by exact prefixLift 4028967
  have htrace : WordTrace (prefixWord ++ tailWord_4028967) baseStart_4028967 baseEnd_4028967 := by
    simpa [prefixWord, tailWord_4028967, baseEnd_4028967] using wordTrace_append hprefix tailTrace_4028967
  have hstable : (prefixWord ++ tailWord_4028967).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4028967).length < 2 ^ (prefixWord ++ tailWord_4028967).sum := by decide
  have hdescent : baseEnd_4028967 < baseStart_4028967 := by decide
  rcases family_descends (prefixWord ++ tailWord_4028967) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4029015 : List Nat := [1, 1, 3, 2, 2, 2, 1, 1, 2, 4, 4]
def baseStart_4029015 : Nat := 118140960795 + 4029015 * 2 ^ 59
def prefixEnd_4029015 : Nat := 4983230072969 + 3 ^ 40 * 4029015 * 2
def baseEnd_4029015 : Nat := 2068821259174659193983403

theorem tailTrace_4029015 : CollatzResearch.WordTrace tailWord_4029015 prefixEnd_4029015 2068821259174659193983403 := by
  unfold tailWord_4029015
  simp only [CollatzResearch.WordTrace]
  refine ⟨146950249498574230824592499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97966832999049487216394999 146950249498574230824592499)
  ·
    refine ⟨220425374247861346236888749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146950249498574230824592499 220425374247861346236888749)
    ·
      refine ⟨82659515342948004838833281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 220425374247861346236888749 82659515342948004838833281)
      ·
        refine ⟨61994636507211003629124961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 82659515342948004838833281 61994636507211003629124961)
        ·
          refine ⟨46495977380408252721843721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61994636507211003629124961 46495977380408252721843721)
          ·
            refine ⟨34871983035306189541382791, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46495977380408252721843721 34871983035306189541382791)
            ·
              refine ⟨52307974552959284312074187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34871983035306189541382791 52307974552959284312074187)
              ·
                refine ⟨78461961829438926468111281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52307974552959284312074187 78461961829438926468111281)
                ·
                  refine ⟨58846471372079194851083461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 78461961829438926468111281 58846471372079194851083461)
                  ·
                    refine ⟨11033713382264849034578149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 58846471372079194851083461 11033713382264849034578149)
                    ·
                      refine ⟨2068821259174659193983403, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11033713382264849034578149 2068821259174659193983403)
                      ·
                        rfl

theorem cell23_4029015_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 1, 1, 2, 4, 4].length) (baseStart_4029015 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4029015 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4029015 prefixEnd_4029015 := by exact prefixLift 4029015
  have htrace : WordTrace (prefixWord ++ tailWord_4029015) baseStart_4029015 baseEnd_4029015 := by
    simpa [prefixWord, tailWord_4029015, baseEnd_4029015] using wordTrace_append hprefix tailTrace_4029015
  have hstable : (prefixWord ++ tailWord_4029015).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4029015).length < 2 ^ (prefixWord ++ tailWord_4029015).sum := by decide
  have hdescent : baseEnd_4029015 < baseStart_4029015 := by decide
  rcases family_descends (prefixWord ++ tailWord_4029015) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4029025 : List Nat := [1, 2, 3, 1, 1, 4, 1, 2, 8]
def baseStart_4029025 : Nat := 118140960795 + 4029025 * 2 ^ 59
def prefixEnd_4029025 : Nat := 4983230072969 + 3 ^ 40 * 4029025 * 2
def baseEnd_4029025 : Nat := 229869599331244906095373

theorem tailTrace_4029025 : CollatzResearch.WordTrace tailWord_4029025 prefixEnd_4029025 229869599331244906095373 := by
  unfold tailWord_4029025
  simp only [CollatzResearch.WordTrace]
  refine ⟨146950614228538002532456529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97967076152358668354971019 146950614228538002532456529)
  ·
    refine ⟨110212960671403501899342397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 146950614228538002532456529 110212960671403501899342397)
    ·
      refine ⟨41329860251776313212253399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 110212960671403501899342397 41329860251776313212253399)
      ·
        refine ⟨61994790377664469818380099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41329860251776313212253399 61994790377664469818380099)
        ·
          refine ⟨92992185566496704727570149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61994790377664469818380099 92992185566496704727570149)
          ·
            refine ⟨17436034793718132136419403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 92992185566496704727570149 17436034793718132136419403)
            ·
              refine ⟨26154052190577198204629105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17436034793718132136419403 26154052190577198204629105)
              ·
                refine ⟨19615539142932898653471829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26154052190577198204629105 19615539142932898653471829)
                ·
                  refine ⟨229869599331244906095373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 19615539142932898653471829 229869599331244906095373)
                  ·
                    rfl

theorem cell23_4029025_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 4, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 4, 1, 2, 8].length) (baseStart_4029025 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4029025 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4029025 prefixEnd_4029025 := by exact prefixLift 4029025
  have htrace : WordTrace (prefixWord ++ tailWord_4029025) baseStart_4029025 baseEnd_4029025 := by
    simpa [prefixWord, tailWord_4029025, baseEnd_4029025] using wordTrace_append hprefix tailTrace_4029025
  have hstable : (prefixWord ++ tailWord_4029025).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4029025).length < 2 ^ (prefixWord ++ tailWord_4029025).sum := by decide
  have hdescent : baseEnd_4029025 < baseStart_4029025 := by decide
  rcases family_descends (prefixWord ++ tailWord_4029025) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4029075 : List Nat := [1, 1, 1, 2, 1, 2, 2, 2, 2, 5, 4]
def baseStart_4029075 : Nat := 118140960795 + 4029075 * 2 ^ 59
def prefixEnd_4029075 : Nat := 4983230072969 + 3 ^ 40 * 4029075 * 2
def baseEnd_4029075 : Nat := 2068852068013928959233127

theorem tailTrace_4029075 : CollatzResearch.WordTrace tailWord_4029075 prefixEnd_4029075 2068852068013928959233127 := by
  unfold tailWord_4029075
  simp only [CollatzResearch.WordTrace]
  refine ⟨146952437878356861071776679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97968291918904574047851119 146952437878356861071776679)
  ·
    refine ⟨220428656817535291607665019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146952437878356861071776679 220428656817535291607665019)
    ·
      refine ⟨330642985226302937411497529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 220428656817535291607665019 330642985226302937411497529)
      ·
        refine ⟨247982238919727203058623147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 330642985226302937411497529 247982238919727203058623147)
        ·
          refine ⟨371973358379590804587934721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 247982238919727203058623147 371973358379590804587934721)
          ·
            refine ⟨278980018784693103440951041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 371973358379590804587934721 278980018784693103440951041)
            ·
              refine ⟨209235014088519827580713281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 278980018784693103440951041 209235014088519827580713281)
              ·
                refine ⟨156926260566389870685534961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 209235014088519827580713281 156926260566389870685534961)
                ·
                  refine ⟨117694695424792403014151221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 156926260566389870685534961 117694695424792403014151221)
                  ·
                    refine ⟨11033877696074287782576677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 117694695424792403014151221 11033877696074287782576677)
                    ·
                      refine ⟨2068852068013928959233127, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11033877696074287782576677 2068852068013928959233127)
                      ·
                        rfl

theorem cell23_4029075_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 2, 2, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 2, 2, 2, 5, 4].length) (baseStart_4029075 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4029075 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4029075 prefixEnd_4029075 := by exact prefixLift 4029075
  have htrace : WordTrace (prefixWord ++ tailWord_4029075) baseStart_4029075 baseEnd_4029075 := by
    simpa [prefixWord, tailWord_4029075, baseEnd_4029075] using wordTrace_append hprefix tailTrace_4029075
  have hstable : (prefixWord ++ tailWord_4029075).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4029075).length < 2 ^ (prefixWord ++ tailWord_4029075).sum := by decide
  have hdescent : baseEnd_4029075 < baseStart_4029075 := by decide
  rcases family_descends (prefixWord ++ tailWord_4029075) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4029103 : List Nat := [1, 1, 2, 1, 2, 5, 4, 2, 1, 1, 3]
def baseStart_4029103 : Nat := 118140960795 + 4029103 * 2 ^ 59
def prefixEnd_4029103 : Nat := 4983230072969 + 3 ^ 40 * 4029103 * 2
def baseEnd_4029103 : Nat := 2068866445472254849682999

theorem tailTrace_4029103 : CollatzResearch.WordTrace tailWord_4029103 prefixEnd_4029103 2068866445472254849682999 := by
  unfold tailWord_4029103
  simp only [CollatzResearch.WordTrace]
  refine ⟨146953459122255421853795963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97968972748170281235863975 146953459122255421853795963)
  ·
    refine ⟨220430188683383132780693945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146953459122255421853795963 220430188683383132780693945)
    ·
      refine ⟨165322641512537349585520459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 220430188683383132780693945 165322641512537349585520459)
      ·
        refine ⟨247983962268806024378280689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 165322641512537349585520459 247983962268806024378280689)
        ·
          refine ⟨185987971701604518283710517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 247983962268806024378280689 185987971701604518283710517)
          ·
            refine ⟨17436372347025423589097861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 185987971701604518283710517 17436372347025423589097861)
            ·
              refine ⟨3269319815067266922955849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17436372347025423589097861 3269319815067266922955849)
              ·
                refine ⟨2451989861300450192216887, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3269319815067266922955849 2451989861300450192216887)
                ·
                  refine ⟨3677984791950675288325331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2451989861300450192216887 3677984791950675288325331)
                  ·
                    refine ⟨5516977187926012932487997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3677984791950675288325331 5516977187926012932487997)
                    ·
                      refine ⟨2068866445472254849682999, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5516977187926012932487997 2068866445472254849682999)
                      ·
                        rfl

theorem cell23_4029103_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 5, 4, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 5, 4, 2, 1, 1, 3].length) (baseStart_4029103 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4029103 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4029103 prefixEnd_4029103 := by exact prefixLift 4029103
  have htrace : WordTrace (prefixWord ++ tailWord_4029103) baseStart_4029103 baseEnd_4029103 := by
    simpa [prefixWord, tailWord_4029103, baseEnd_4029103] using wordTrace_append hprefix tailTrace_4029103
  have hstable : (prefixWord ++ tailWord_4029103).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4029103).length < 2 ^ (prefixWord ++ tailWord_4029103).sum := by decide
  have hdescent : baseEnd_4029103 < baseStart_4029103 := by decide
  rcases family_descends (prefixWord ++ tailWord_4029103) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4029109 : List Nat := [1, 3, 3, 3, 1, 1, 1, 2, 3, 1, 4]
def baseStart_4029109 : Nat := 118140960795 + 4029109 * 2 ^ 59
def prefixEnd_4029109 : Nat := 4983230072969 + 3 ^ 40 * 4029109 * 2
def baseEnd_4029109 : Nat := 2068869526356181826207971

theorem tailTrace_4029109 : CollatzResearch.WordTrace tailWord_4029109 prefixEnd_4029109 2068869526356181826207971 := by
  unfold tailWord_4029109
  simp only [CollatzResearch.WordTrace]
  refine ⟨146953677960233684878514381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97969118640155789919009587 146953677960233684878514381)
  ·
    refine ⟨55107629235087631829442893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 146953677960233684878514381 55107629235087631829442893)
    ·
      refine ⟨20665360963157861936041085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 55107629235087631829442893 20665360963157861936041085)
      ·
        refine ⟨7749510361184198226015407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20665360963157861936041085 7749510361184198226015407)
        ·
          refine ⟨11624265541776297339023111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7749510361184198226015407 11624265541776297339023111)
          ·
            refine ⟨17436398312664446008534667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11624265541776297339023111 17436398312664446008534667)
            ·
              refine ⟨26154597468996669012802001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17436398312664446008534667 26154597468996669012802001)
              ·
                refine ⟨19615948101747501759601501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26154597468996669012802001 19615948101747501759601501)
                ·
                  refine ⟨7355980538155313159850563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19615948101747501759601501 7355980538155313159850563)
                  ·
                    refine ⟨11033970807232969739775845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7355980538155313159850563 11033970807232969739775845)
                    ·
                      refine ⟨2068869526356181826207971, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11033970807232969739775845 2068869526356181826207971)
                      ·
                        rfl

theorem cell23_4029109_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 1, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 1, 1, 2, 3, 1, 4].length) (baseStart_4029109 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4029109 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4029109 prefixEnd_4029109 := by exact prefixLift 4029109
  have htrace : WordTrace (prefixWord ++ tailWord_4029109) baseStart_4029109 baseEnd_4029109 := by
    simpa [prefixWord, tailWord_4029109, baseEnd_4029109] using wordTrace_append hprefix tailTrace_4029109
  have hstable : (prefixWord ++ tailWord_4029109).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4029109).length < 2 ^ (prefixWord ++ tailWord_4029109).sum := by decide
  have hdescent : baseEnd_4029109 < baseStart_4029109 := by decide
  rcases family_descends (prefixWord ++ tailWord_4029109) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4029119 : List Nat := [1, 1, 2, 2, 2, 4, 2, 3, 2, 4]
def baseStart_4029119 : Nat := 118140960795 + 4029119 * 2 ^ 59
def prefixEnd_4029119 : Nat := 4983230072969 + 3 ^ 40 * 4029119 * 2
def baseEnd_4029119 : Nat := 689624887054242262360975

theorem tailTrace_4029119 : CollatzResearch.WordTrace tailWord_4029119 prefixEnd_4029119 689624887054242262360975 := by
  unfold tailWord_4029119
  simp only [CollatzResearch.WordTrace]
  refine ⟨146954042690197456586378411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97969361793464971057585607 146954042690197456586378411)
  ·
    refine ⟨220431064035296184879567617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146954042690197456586378411 220431064035296184879567617)
    ·
      refine ⟨165323298026472138659675713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 220431064035296184879567617 165323298026472138659675713)
      ·
        refine ⟨123992473519854103994756785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 165323298026472138659675713 123992473519854103994756785)
        ·
          refine ⟨92994355139890577996067589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 123992473519854103994756785 92994355139890577996067589)
          ·
            refine ⟨17436441588729483374262673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 92994355139890577996067589 17436441588729483374262673)
            ·
              refine ⟨13077331191547112530697005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17436441588729483374262673 13077331191547112530697005)
              ·
                refine ⟨4903999196830167199011377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13077331191547112530697005 4903999196830167199011377)
                ·
                  refine ⟨3677999397622625399258533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4903999196830167199011377 3677999397622625399258533)
                  ·
                    refine ⟨689624887054242262360975, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3677999397622625399258533 689624887054242262360975)
                    ·
                      rfl

theorem cell23_4029119_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 4, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 4, 2, 3, 2, 4].length) (baseStart_4029119 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4029119 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4029119 prefixEnd_4029119 := by exact prefixLift 4029119
  have htrace : WordTrace (prefixWord ++ tailWord_4029119) baseStart_4029119 baseEnd_4029119 := by
    simpa [prefixWord, tailWord_4029119, baseEnd_4029119] using wordTrace_append hprefix tailTrace_4029119
  have hstable : (prefixWord ++ tailWord_4029119).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4029119).length < 2 ^ (prefixWord ++ tailWord_4029119).sum := by decide
  have hdescent : baseEnd_4029119 < baseStart_4029119 := by decide
  rcases family_descends (prefixWord ++ tailWord_4029119) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4029140 : List Nat := [2, 4, 1, 3, 3, 1, 2, 1, 1, 5]
def baseStart_4029140 : Nat := 118140960795 + 4029140 * 2 ^ 59
def prefixEnd_4029140 : Nat := 4983230072969 + 3 ^ 40 * 4029140 * 2
def baseEnd_4029140 : Nat := 689628481418823734973443

theorem tailTrace_4029140 : CollatzResearch.WordTrace tailWord_4029140 prefixEnd_4029140 689628481418823734973443 := by
  unfold tailWord_4029140
  simp only [CollatzResearch.WordTrace]
  refine ⟨73477404311560688586446437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97969872415414251448595249 73477404311560688586446437)
  ·
    refine ⟨13777013308417629109958707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 73477404311560688586446437 13777013308417629109958707)
    ·
      refine ⟨20665519962626443664938061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13777013308417629109958707 20665519962626443664938061)
      ·
        refine ⟨7749569985984916374351773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20665519962626443664938061 7749569985984916374351773)
        ·
          refine ⟨2906088744744343640381915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7749569985984916374351773 2906088744744343640381915)
          ·
            refine ⟨4359133117116515460572873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2906088744744343640381915 4359133117116515460572873)
            ·
              refine ⟨3269349837837386595429655, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4359133117116515460572873 3269349837837386595429655)
              ·
                refine ⟨4904024756756079893144483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3269349837837386595429655 4904024756756079893144483)
                ·
                  refine ⟨7356037135134119839716725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4904024756756079893144483 7356037135134119839716725)
                  ·
                    refine ⟨689628481418823734973443, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7356037135134119839716725 689628481418823734973443)
                    ·
                      rfl

theorem cell23_4029140_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 3, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 3, 1, 2, 1, 1, 5].length) (baseStart_4029140 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4029140 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4029140 prefixEnd_4029140 := by exact prefixLift 4029140
  have htrace : WordTrace (prefixWord ++ tailWord_4029140) baseStart_4029140 baseEnd_4029140 := by
    simpa [prefixWord, tailWord_4029140, baseEnd_4029140] using wordTrace_append hprefix tailTrace_4029140
  have hstable : (prefixWord ++ tailWord_4029140).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4029140).length < 2 ^ (prefixWord ++ tailWord_4029140).sum := by decide
  have hdescent : baseEnd_4029140 < baseStart_4029140 := by decide
  rcases family_descends (prefixWord ++ tailWord_4029140) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4029143 : List Nat := [1, 1, 3, 2, 1, 4, 1, 5, 1, 2, 2]
def baseStart_4029143 : Nat := 118140960795 + 4029143 * 2 ^ 59
def prefixEnd_4029143 : Nat := 4983230072969 + 3 ^ 40 * 4029143 * 2
def baseEnd_4029143 : Nat := 2068886984698434693182815

theorem tailTrace_4029143 : CollatzResearch.WordTrace tailWord_4029143 prefixEnd_4029143 2068886984698434693182815 := by
  unfold tailWord_4029143
  simp only [CollatzResearch.WordTrace]
  refine ⟨146954918042110508685252083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97969945361407005790168055 146954918042110508685252083)
  ·
    refine ⟨220432377063165763027878125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146954918042110508685252083 220432377063165763027878125)
    ·
      refine ⟨82662141398687161135454297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 220432377063165763027878125 82662141398687161135454297)
      ·
        refine ⟨61996606049015370851590723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 82662141398687161135454297 61996606049015370851590723)
        ·
          refine ⟨92994909073523056277386085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61996606049015370851590723 92994909073523056277386085)
          ·
            refine ⟨17436545451285573052009891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 92994909073523056277386085 17436545451285573052009891)
            ·
              refine ⟨26154818176928359578014837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17436545451285573052009891 26154818176928359578014837)
              ·
                refine ⟨2452014204087033710438891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 26154818176928359578014837 2452014204087033710438891)
                ·
                  refine ⟨3678021306130550565658337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2452014204087033710438891 3678021306130550565658337)
                  ·
                    refine ⟨2758515979597912924243753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3678021306130550565658337 2758515979597912924243753)
                    ·
                      refine ⟨2068886984698434693182815, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2758515979597912924243753 2068886984698434693182815)
                      ·
                        rfl

theorem cell23_4029143_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 4, 1, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 4, 1, 5, 1, 2, 2].length) (baseStart_4029143 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4029143 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4029143 prefixEnd_4029143 := by exact prefixLift 4029143
  have htrace : WordTrace (prefixWord ++ tailWord_4029143) baseStart_4029143 baseEnd_4029143 := by
    simpa [prefixWord, tailWord_4029143, baseEnd_4029143] using wordTrace_append hprefix tailTrace_4029143
  have hstable : (prefixWord ++ tailWord_4029143).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4029143).length < 2 ^ (prefixWord ++ tailWord_4029143).sum := by decide
  have hdescent : baseEnd_4029143 < baseStart_4029143 := by decide
  rcases family_descends (prefixWord ++ tailWord_4029143) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4029173 : List Nat := [1, 3, 6, 1, 1, 1, 1, 1, 1, 1, 6]
def baseStart_4029173 : Nat := 118140960795 + 4029173 * 2 ^ 59
def prefixEnd_4029173 : Nat := 4983230072969 + 3 ^ 40 * 4029173 * 2
def baseEnd_4029173 : Nat := 2068902389118069575807677

theorem tailTrace_4029173 : CollatzResearch.WordTrace tailWord_4029173 prefixEnd_4029173 2068902389118069575807677 := by
  unfold tailWord_4029173
  simp only [CollatzResearch.WordTrace]
  refine ⟨146956012232001823808844173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97970674821334549205896115 146956012232001823808844173)
  ·
    refine ⟨55108504587000683928316565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 146956012232001823808844173 55108504587000683928316565)
    ·
      refine ⟨2583211152515657059139839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 55108504587000683928316565 2583211152515657059139839)
      ·
        refine ⟨3874816728773485588709759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2583211152515657059139839 3874816728773485588709759)
        ·
          refine ⟨5812225093160228383064639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3874816728773485588709759 5812225093160228383064639)
          ·
            refine ⟨8718337639740342574596959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5812225093160228383064639 8718337639740342574596959)
            ·
              refine ⟨13077506459610513861895439, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8718337639740342574596959 13077506459610513861895439)
              ·
                refine ⟨19616259689415770792843159, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13077506459610513861895439 19616259689415770792843159)
                ·
                  refine ⟨29424389534123656189264739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19616259689415770792843159 29424389534123656189264739)
                  ·
                    refine ⟨44136584301185484283897109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 29424389534123656189264739 44136584301185484283897109)
                    ·
                      refine ⟨2068902389118069575807677, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 44136584301185484283897109 2068902389118069575807677)
                      ·
                        rfl

theorem cell23_4029173_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 6, 1, 1, 1, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 6, 1, 1, 1, 1, 1, 1, 1, 6].length) (baseStart_4029173 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4029173 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4029173 prefixEnd_4029173 := by exact prefixLift 4029173
  have htrace : WordTrace (prefixWord ++ tailWord_4029173) baseStart_4029173 baseEnd_4029173 := by
    simpa [prefixWord, tailWord_4029173, baseEnd_4029173] using wordTrace_append hprefix tailTrace_4029173
  have hstable : (prefixWord ++ tailWord_4029173).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4029173).length < 2 ^ (prefixWord ++ tailWord_4029173).sum := by decide
  have hdescent : baseEnd_4029173 < baseStart_4029173 := by decide
  rcases family_descends (prefixWord ++ tailWord_4029173) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4029199 : List Nat := [1, 1, 2, 1, 1, 1, 6, 1, 3, 4, 2]
def baseStart_4029199 : Nat := 118140960795 + 4029199 * 2 ^ 59
def prefixEnd_4029199 : Nat := 4983230072969 + 3 ^ 40 * 4029199 * 2
def baseEnd_4029199 : Nat := 2068915739615086474082557

theorem tailTrace_4029199 : CollatzResearch.WordTrace tailWord_4029199 prefixEnd_4029199 2068915739615086474082557 := by
  unfold tailWord_4029199
  simp only [CollatzResearch.WordTrace]
  refine ⟨146956960529907630249290651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97971307019938420166193767 146956960529907630249290651)
  ·
    refine ⟨220435440794861445373935977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146956960529907630249290651 220435440794861445373935977)
    ·
      refine ⟨165326580596146084030451983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 220435440794861445373935977 165326580596146084030451983)
      ·
        refine ⟨247989870894219126045677975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 165326580596146084030451983 247989870894219126045677975)
        ·
          refine ⟨371984806341328689068516963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 247989870894219126045677975 371984806341328689068516963)
          ·
            refine ⟨557977209511993033602775445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 371984806341328689068516963 557977209511993033602775445)
            ·
              refine ⟨26155181695874673450130099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 557977209511993033602775445 26155181695874673450130099)
              ·
                refine ⟨39232772543812010175195149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26155181695874673450130099 39232772543812010175195149)
                ·
                  refine ⟨14712289703929503815698181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 39232772543812010175195149 14712289703929503815698181)
                  ·
                    refine ⟨2758554319486781965443409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 14712289703929503815698181 2758554319486781965443409)
                    ·
                      refine ⟨2068915739615086474082557, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2758554319486781965443409 2068915739615086474082557)
                      ·
                        rfl

theorem cell23_4029199_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 6, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 6, 1, 3, 4, 2].length) (baseStart_4029199 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4029199 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4029199 prefixEnd_4029199 := by exact prefixLift 4029199
  have htrace : WordTrace (prefixWord ++ tailWord_4029199) baseStart_4029199 baseEnd_4029199 := by
    simpa [prefixWord, tailWord_4029199, baseEnd_4029199] using wordTrace_append hprefix tailTrace_4029199
  have hstable : (prefixWord ++ tailWord_4029199).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4029199).length < 2 ^ (prefixWord ++ tailWord_4029199).sum := by decide
  have hdescent : baseEnd_4029199 < baseStart_4029199 := by decide
  rcases family_descends (prefixWord ++ tailWord_4029199) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4029233 : List Nat := [1, 2, 2, 3, 2, 1, 3, 3, 2, 2, 2]
def baseStart_4029233 : Nat := 118140960795 + 4029233 * 2 ^ 59
def prefixEnd_4029233 : Nat := 4983230072969 + 3 ^ 40 * 4029233 * 2
def baseEnd_4029233 : Nat := 2068933197957339341057401

theorem tailTrace_4029233 : CollatzResearch.WordTrace tailWord_4029233 prefixEnd_4029233 2068933197957339341057401 := by
  unfold tailWord_4029233
  simp only [CollatzResearch.WordTrace]
  refine ⟨146958200611784454056028353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97972133741189636037352235 146958200611784454056028353)
  ·
    refine ⟨110218650458838340542021265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 146958200611784454056028353 110218650458838340542021265)
    ·
      refine ⟨82663987844128755406515949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 110218650458838340542021265 82663987844128755406515949)
      ·
        refine ⟨30998995441548283277443481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 82663987844128755406515949 30998995441548283277443481)
        ·
          refine ⟨23249246581161212458082611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30998995441548283277443481 23249246581161212458082611)
          ·
            refine ⟨34873869871741818687123917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23249246581161212458082611 34873869871741818687123917)
            ·
              refine ⟨13077701201903182007671469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34873869871741818687123917 13077701201903182007671469)
              ·
                refine ⟨4904137950713693252876801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13077701201903182007671469 4904137950713693252876801)
                ·
                  refine ⟨3678103463035269939657601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4904137950713693252876801 3678103463035269939657601)
                  ·
                    refine ⟨2758577597276452454743201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3678103463035269939657601 2758577597276452454743201)
                    ·
                      refine ⟨2068933197957339341057401, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2758577597276452454743201 2068933197957339341057401)
                      ·
                        rfl

theorem cell23_4029233_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 3, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 3, 3, 2, 2, 2].length) (baseStart_4029233 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4029233 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4029233 prefixEnd_4029233 := by exact prefixLift 4029233
  have htrace : WordTrace (prefixWord ++ tailWord_4029233) baseStart_4029233 baseEnd_4029233 := by
    simpa [prefixWord, tailWord_4029233, baseEnd_4029233] using wordTrace_append hprefix tailTrace_4029233
  have hstable : (prefixWord ++ tailWord_4029233).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4029233).length < 2 ^ (prefixWord ++ tailWord_4029233).sum := by decide
  have hdescent : baseEnd_4029233 < baseStart_4029233 := by decide
  rcases family_descends (prefixWord ++ tailWord_4029233) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4029254 : List Nat := [6, 1, 1, 2, 2, 1, 3, 1, 1, 3, 2]
def baseStart_4029254 : Nat := 118140960795 + 4029254 * 2 ^ 59
def prefixEnd_4029254 : Nat := 4983230072969 + 3 ^ 40 * 4029254 * 2
def baseEnd_4029254 : Nat := 2068943981051083758894805

theorem tailTrace_4029254 : CollatzResearch.WordTrace tailWord_4029254 prefixEnd_4029254 2068943981051083758894805 := by
  unfold tailWord_4029254
  simp only [CollatzResearch.WordTrace]
  refine ⟨4592467704522136707579463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 97972644363138916428361877 4592467704522136707579463)
  ·
    refine ⟨6888701556783205061369195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4592467704522136707579463 6888701556783205061369195)
    ·
      refine ⟨10333052335174807592053793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6888701556783205061369195 10333052335174807592053793)
      ·
        refine ⟨7749789251381105694040345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10333052335174807592053793 7749789251381105694040345)
        ·
          refine ⟨5812341938535829270530259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7749789251381105694040345 5812341938535829270530259)
          ·
            refine ⟨8718512907803743905795389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5812341938535829270530259 8718512907803743905795389)
            ·
              refine ⟨3269442340426403964673271, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8718512907803743905795389 3269442340426403964673271)
              ·
                refine ⟨4904163510639605947009907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3269442340426403964673271 4904163510639605947009907)
                ·
                  refine ⟨7356245265959408920514861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4904163510639605947009907 7356245265959408920514861)
                  ·
                    refine ⟨2758591974734778345193073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7356245265959408920514861 2758591974734778345193073)
                    ·
                      refine ⟨2068943981051083758894805, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2758591974734778345193073 2068943981051083758894805)
                      ·
                        rfl

theorem cell23_4029254_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 2, 1, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 2, 1, 3, 1, 1, 3, 2].length) (baseStart_4029254 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4029254 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4029254 prefixEnd_4029254 := by exact prefixLift 4029254
  have htrace : WordTrace (prefixWord ++ tailWord_4029254) baseStart_4029254 baseEnd_4029254 := by
    simpa [prefixWord, tailWord_4029254, baseEnd_4029254] using wordTrace_append hprefix tailTrace_4029254
  have hstable : (prefixWord ++ tailWord_4029254).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4029254).length < 2 ^ (prefixWord ++ tailWord_4029254).sum := by decide
  have hdescent : baseEnd_4029254 < baseStart_4029254 := by decide
  rcases family_descends (prefixWord ++ tailWord_4029254) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4029259 : List Nat := [1, 1, 1, 1, 3, 1, 1, 1, 6, 5, 2]
def baseStart_4029259 : Nat := 118140960795 + 4029259 * 2 ^ 59
def prefixEnd_4029259 : Nat := 4983230072969 + 3 ^ 40 * 4029259 * 2
def baseEnd_4029259 : Nat := 2068946548454356239332281

theorem tailTrace_4029259 : CollatzResearch.WordTrace tailWord_4029259 prefixEnd_4029259 2068946548454356239332281 := by
  unfold tailWord_4029259
  simp only [CollatzResearch.WordTrace]
  refine ⟨146959148909690260496474831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97972765939793506997649887 146959148909690260496474831)
  ·
    refine ⟨220438723364535390744712247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146959148909690260496474831 220438723364535390744712247)
    ·
      refine ⟨330658085046803086117068371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 220438723364535390744712247 330658085046803086117068371)
      ·
        refine ⟨495987127570204629175602557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 330658085046803086117068371 495987127570204629175602557)
        ·
          refine ⟨185995172838826735940850959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 495987127570204629175602557 185995172838826735940850959)
          ·
            refine ⟨278992759258240103911276439, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 185995172838826735940850959 278992759258240103911276439)
            ·
              refine ⟨418489138887360155866914659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 278992759258240103911276439 418489138887360155866914659)
              ·
                refine ⟨627733708331040233800371989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 418489138887360155866914659 627733708331040233800371989)
                ·
                  refine ⟨29425017578017510959392437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 627733708331040233800371989 29425017578017510959392437)
                  ·
                    refine ⟨2758595397939141652443041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 29425017578017510959392437 2758595397939141652443041)
                    ·
                      refine ⟨2068946548454356239332281, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2758595397939141652443041 2068946548454356239332281)
                      ·
                        rfl

theorem cell23_4029259_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 1, 6, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 1, 6, 5, 2].length) (baseStart_4029259 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4029259 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4029259 prefixEnd_4029259 := by exact prefixLift 4029259
  have htrace : WordTrace (prefixWord ++ tailWord_4029259) baseStart_4029259 baseEnd_4029259 := by
    simpa [prefixWord, tailWord_4029259, baseEnd_4029259] using wordTrace_append hprefix tailTrace_4029259
  have hstable : (prefixWord ++ tailWord_4029259).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4029259).length < 2 ^ (prefixWord ++ tailWord_4029259).sum := by decide
  have hdescent : baseEnd_4029259 < baseStart_4029259 := by decide
  rcases family_descends (prefixWord ++ tailWord_4029259) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4029269 : List Nat := [1, 3, 2, 2, 2, 1, 1, 4, 2, 5]
def baseStart_4029269 : Nat := 118140960795 + 4029269 * 2 ^ 59
def prefixEnd_4029269 : Nat := 4983230072969 + 3 ^ 40 * 4029269 * 2
def baseEnd_4029269 : Nat := 689650561086967066735745

theorem tailTrace_4029269 : CollatzResearch.WordTrace tailWord_4029269 prefixEnd_4029269 689650561086967066735745 := by
  unfold tailWord_4029269
  simp only [CollatzResearch.WordTrace]
  refine ⟨146959513639654032204338861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97973009093102688136225907 146959513639654032204338861)
  ·
    refine ⟨55109817614870262076627073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 146959513639654032204338861 55109817614870262076627073)
    ·
      refine ⟨41332363211152696557470305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55109817614870262076627073 41332363211152696557470305)
      ·
        refine ⟨30999272408364522418102729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41332363211152696557470305 30999272408364522418102729)
        ·
          refine ⟨23249454306273391813577047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30999272408364522418102729 23249454306273391813577047)
          ·
            refine ⟨34874181459410087720365571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23249454306273391813577047 34874181459410087720365571)
            ·
              refine ⟨52311272189115131580548357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34874181459410087720365571 52311272189115131580548357)
              ·
                refine ⟨9808363535459087171352817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 52311272189115131580548357 9808363535459087171352817)
                ·
                  refine ⟨7356272651594315378514613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9808363535459087171352817 7356272651594315378514613)
                  ·
                    refine ⟨689650561086967066735745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7356272651594315378514613 689650561086967066735745)
                    ·
                      rfl

theorem cell23_4029269_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 1, 4, 2, 5].length) (baseStart_4029269 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4029269 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4029269 prefixEnd_4029269 := by exact prefixLift 4029269
  have htrace : WordTrace (prefixWord ++ tailWord_4029269) baseStart_4029269 baseEnd_4029269 := by
    simpa [prefixWord, tailWord_4029269, baseEnd_4029269] using wordTrace_append hprefix tailTrace_4029269
  have hstable : (prefixWord ++ tailWord_4029269).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4029269).length < 2 ^ (prefixWord ++ tailWord_4029269).sum := by decide
  have hdescent : baseEnd_4029269 < baseStart_4029269 := by decide
  rcases family_descends (prefixWord ++ tailWord_4029269) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4029273 : List Nat := [1, 2, 1, 2, 2, 6, 2, 2, 5]
def baseStart_4029273 : Nat := 118140960795 + 4029273 * 2 ^ 59
def prefixEnd_4029273 : Nat := 4983230072969 + 3 ^ 40 * 4029273 * 2
def baseEnd_4029273 : Nat := 229883748575946576061913

theorem tailTrace_4029273 : CollatzResearch.WordTrace tailWord_4029273 prefixEnd_4029273 229883748575946576061913 := by
  unfold tailWord_4029273
  simp only [CollatzResearch.WordTrace]
  refine ⟨146959659531639540887484473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97973106354426360591656315 146959659531639540887484473)
  ·
    refine ⟨110219744648729655665613355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 146959659531639540887484473 110219744648729655665613355)
    ·
      refine ⟨165329616973094483498420033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110219744648729655665613355 165329616973094483498420033)
      ·
        refine ⟨123997212729820862623815025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 165329616973094483498420033 123997212729820862623815025)
        ·
          refine ⟨92997909547365646967861269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 123997212729820862623815025 92997909547365646967861269)
          ·
            refine ⟨4359277010032764701618497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 92997909547365646967861269 4359277010032764701618497)
            ·
              refine ⟨3269457757524573526213873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4359277010032764701618497 3269457757524573526213873)
              ·
                refine ⟨2452093318143430144660405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3269457757524573526213873 2452093318143430144660405)
                ·
                  refine ⟨229883748575946576061913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2452093318143430144660405 229883748575946576061913)
                  ·
                    rfl

theorem cell23_4029273_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 6, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 6, 2, 2, 5].length) (baseStart_4029273 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4029273 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4029273 prefixEnd_4029273 := by exact prefixLift 4029273
  have htrace : WordTrace (prefixWord ++ tailWord_4029273) baseStart_4029273 baseEnd_4029273 := by
    simpa [prefixWord, tailWord_4029273, baseEnd_4029273] using wordTrace_append hprefix tailTrace_4029273
  have hstable : (prefixWord ++ tailWord_4029273).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4029273).length < 2 ^ (prefixWord ++ tailWord_4029273).sum := by decide
  have hdescent : baseEnd_4029273 < baseStart_4029273 := by decide
  rcases family_descends (prefixWord ++ tailWord_4029273) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4029299 : List Nat := [1, 1, 1, 2, 2, 1, 5, 1, 5, 4]
def baseStart_4029299 : Nat := 118140960795 + 4029299 * 2 ^ 59
def prefixEnd_4029299 : Nat := 4983230072969 + 3 ^ 40 * 4029299 * 2
def baseEnd_4029299 : Nat := 689655695893512027610699

theorem tailTrace_4029299 : CollatzResearch.WordTrace tailWord_4029299 prefixEnd_4029299 689655695893512027610699 := by
  unfold tailWord_4029299
  simp only [CollatzResearch.WordTrace]
  refine ⟨146960607829545347327930951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97973738553030231551953967 146960607829545347327930951)
  ·
    refine ⟨220440911744318020991896427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146960607829545347327930951 220440911744318020991896427)
    ·
      refine ⟨330661367616477031487844641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 220440911744318020991896427 330661367616477031487844641)
      ·
        refine ⟨247996025712357773615883481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 330661367616477031487844641 247996025712357773615883481)
        ·
          refine ⟨185997019284268330211912611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 247996025712357773615883481 185997019284268330211912611)
          ·
            refine ⟨278995528926402495317868917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 185997019284268330211912611 278995528926402495317868917)
            ·
              refine ⟨26155830836850233936050211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 278995528926402495317868917 26155830836850233936050211)
              ·
                refine ⟨39233746255275350904075317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26155830836850233936050211 39233746255275350904075317)
                ·
                  refine ⟨3678163711432064147257061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 39233746255275350904075317 3678163711432064147257061)
                  ·
                    refine ⟨689655695893512027610699, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3678163711432064147257061 689655695893512027610699)
                    ·
                      rfl

theorem cell23_4029299_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 5, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 5, 1, 5, 4].length) (baseStart_4029299 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4029299 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4029299 prefixEnd_4029299 := by exact prefixLift 4029299
  have htrace : WordTrace (prefixWord ++ tailWord_4029299) baseStart_4029299 baseEnd_4029299 := by
    simpa [prefixWord, tailWord_4029299, baseEnd_4029299] using wordTrace_append hprefix tailTrace_4029299
  have hstable : (prefixWord ++ tailWord_4029299).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4029299).length < 2 ^ (prefixWord ++ tailWord_4029299).sum := by decide
  have hdescent : baseEnd_4029299 < baseStart_4029299 := by decide
  rcases family_descends (prefixWord ++ tailWord_4029299) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4029319 : List Nat := [1, 1, 4, 2, 3, 1, 1, 1, 2, 1, 6]
def baseStart_4029319 : Nat := 118140960795 + 4029319 * 2 ^ 59
def prefixEnd_4029319 : Nat := 4983230072969 + 3 ^ 40 * 4029319 * 2
def baseEnd_4029319 : Nat := 2068977357293626004582005

theorem tailTrace_4029319 : CollatzResearch.WordTrace tailWord_4029319 prefixEnd_4029319 2068977357293626004582005 := by
  unfold tailWord_4029319
  simp only [CollatzResearch.WordTrace]
  refine ⟨146961337289472890743659011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97974224859648593829106007 146961337289472890743659011)
  ·
    refine ⟨220442005934209336115488517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146961337289472890743659011 220442005934209336115488517)
    ·
      refine ⟨41332876112664250521654097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 220442005934209336115488517 41332876112664250521654097)
      ·
        refine ⟨30999657084498187891240573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41332876112664250521654097 30999657084498187891240573)
        ·
          refine ⟨11624871406686820459215215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30999657084498187891240573 11624871406686820459215215)
          ·
            refine ⟨17437307110030230688822823, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11624871406686820459215215 17437307110030230688822823)
            ·
              refine ⟨26155960665045346033234235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17437307110030230688822823 26155960665045346033234235)
              ·
                refine ⟨39233940997568019049851353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26155960665045346033234235 39233940997568019049851353)
                ·
                  refine ⟨29425455748176014287388515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 39233940997568019049851353 29425455748176014287388515)
                  ·
                    refine ⟨44138183622264021431082773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 29425455748176014287388515 44138183622264021431082773)
                    ·
                      refine ⟨2068977357293626004582005, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 44138183622264021431082773 2068977357293626004582005)
                      ·
                        rfl

theorem cell23_4029319_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 1, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 1, 1, 1, 2, 1, 6].length) (baseStart_4029319 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4029319 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4029319 prefixEnd_4029319 := by exact prefixLift 4029319
  have htrace : WordTrace (prefixWord ++ tailWord_4029319) baseStart_4029319 baseEnd_4029319 := by
    simpa [prefixWord, tailWord_4029319, baseEnd_4029319] using wordTrace_append hprefix tailTrace_4029319
  have hstable : (prefixWord ++ tailWord_4029319).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4029319).length < 2 ^ (prefixWord ++ tailWord_4029319).sum := by decide
  have hdescent : baseEnd_4029319 < baseStart_4029319 := by decide
  rcases family_descends (prefixWord ++ tailWord_4029319) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4029333 : List Nat := [1, 3, 2, 1, 1, 4, 2, 4, 1, 4]
def baseStart_4029333 : Nat := 118140960795 + 4029333 * 2 ^ 59
def prefixEnd_4029333 : Nat := 4983230072969 + 3 ^ 40 * 4029333 * 2
def baseEnd_4029333 : Nat := 689661515340929649935647

theorem tailTrace_4029333 : CollatzResearch.WordTrace tailWord_4029333 prefixEnd_4029333 689661515340929649935647 := by
  unfold tailWord_4029333
  simp only [CollatzResearch.WordTrace]
  refine ⟨146961847911422171134668653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97974565274281447423112435 146961847911422171134668653)
  ·
    refine ⟨55110692966783314175500745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 146961847911422171134668653 55110692966783314175500745)
    ·
      refine ⟨41333019725087485631625559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55110692966783314175500745 41333019725087485631625559)
      ·
        refine ⟨61999529587631228447438339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41333019725087485631625559 61999529587631228447438339)
        ·
          refine ⟨92999294381446842671157509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61999529587631228447438339 92999294381446842671157509)
          ·
            refine ⟨17437367696521283000842033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 92999294381446842671157509 17437367696521283000842033)
            ·
              refine ⟨13078025772390962250631525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17437367696521283000842033 13078025772390962250631525)
              ·
                refine ⟨2452129832323305421993411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13078025772390962250631525 2452129832323305421993411)
                ·
                  refine ⟨3678194748484958132990117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2452129832323305421993411 3678194748484958132990117)
                  ·
                    refine ⟨689661515340929649935647, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3678194748484958132990117 689661515340929649935647)
                    ·
                      rfl

theorem cell23_4029333_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 4, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 4, 2, 4, 1, 4].length) (baseStart_4029333 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4029333 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4029333 prefixEnd_4029333 := by exact prefixLift 4029333
  have htrace : WordTrace (prefixWord ++ tailWord_4029333) baseStart_4029333 baseEnd_4029333 := by
    simpa [prefixWord, tailWord_4029333, baseEnd_4029333] using wordTrace_append hprefix tailTrace_4029333
  have hstable : (prefixWord ++ tailWord_4029333).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4029333).length < 2 ^ (prefixWord ++ tailWord_4029333).sum := by decide
  have hdescent : baseEnd_4029333 < baseStart_4029333 := by decide
  rcases family_descends (prefixWord ++ tailWord_4029333) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4029376 : List Nat := [2, 1, 1, 2, 3, 3, 2, 3, 1, 5]
def baseStart_4029376 : Nat := 118140960795 + 4029376 * 2 ^ 59
def prefixEnd_4029376 : Nat := 4983230072969 + 3 ^ 40 * 4029376 * 2
def baseEnd_4029376 : Nat := 689668875230310760523081

theorem tailTrace_4029376 : CollatzResearch.WordTrace tailWord_4029376 prefixEnd_4029376 689668875230310760523081 := by
  unfold tailWord_4029376
  simp only [CollatzResearch.WordTrace]
  refine ⟨73481708125133194739241991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97975610833510926318989321 73481708125133194739241991)
  ·
    refine ⟨110222562187699792108862987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73481708125133194739241991 110222562187699792108862987)
    ·
      refine ⟨165333843281549688163294481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110222562187699792108862987 165333843281549688163294481)
      ·
        refine ⟨124000382461162266122470861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 165333843281549688163294481 124000382461162266122470861)
        ·
          refine ⟨46500143422935849795926573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 124000382461162266122470861 46500143422935849795926573)
          ·
            refine ⟨17437553783600943673472465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 46500143422935849795926573 17437553783600943673472465)
            ·
              refine ⟨13078165337700707755104349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17437553783600943673472465 13078165337700707755104349)
              ·
                refine ⟨4904312001637765408164131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13078165337700707755104349 4904312001637765408164131)
                ·
                  refine ⟨7356468002456648112246197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4904312001637765408164131 7356468002456648112246197)
                  ·
                    refine ⟨689668875230310760523081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7356468002456648112246197 689668875230310760523081)
                    ·
                      rfl

theorem cell23_4029376_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 3, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 3, 2, 3, 1, 5].length) (baseStart_4029376 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4029376 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4029376 prefixEnd_4029376 := by exact prefixLift 4029376
  have htrace : WordTrace (prefixWord ++ tailWord_4029376) baseStart_4029376 baseEnd_4029376 := by
    simpa [prefixWord, tailWord_4029376, baseEnd_4029376] using wordTrace_append hprefix tailTrace_4029376
  have hstable : (prefixWord ++ tailWord_4029376).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4029376).length < 2 ^ (prefixWord ++ tailWord_4029376).sum := by decide
  have hdescent : baseEnd_4029376 < baseStart_4029376 := by decide
  rcases family_descends (prefixWord ++ tailWord_4029376) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4029390 : List Nat := [4, 1, 1, 1, 2, 5, 1, 1, 3, 1, 3]
def baseStart_4029390 : Nat := 118140960795 + 4029390 * 2 ^ 59
def prefixEnd_4029390 : Nat := 4983230072969 + 3 ^ 40 * 4029390 * 2
def baseEnd_4029390 : Nat := 2069013814420095226794179

theorem tailTrace_4029390 : CollatzResearch.WordTrace tailWord_4029390 prefixEnd_4029390 2069013814420095226794179 := by
  unfold tailWord_4029390
  simp only [CollatzResearch.WordTrace]
  refine ⟨18370490859026958733686703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 97975951248143779912995749 18370490859026958733686703)
  ·
    refine ⟨27555736288540438100530055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18370490859026958733686703 27555736288540438100530055)
    ·
      refine ⟨41333604432810657150795083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27555736288540438100530055 41333604432810657150795083)
      ·
        refine ⟨62000406649215985726192625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41333604432810657150795083 62000406649215985726192625)
        ·
          refine ⟨46500304986911989294644469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62000406649215985726192625 46500304986911989294644469)
          ·
            refine ⟨4359403592522998996372919, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 46500304986911989294644469 4359403592522998996372919)
            ·
              refine ⟨6539105388784498494559379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4359403592522998996372919 6539105388784498494559379)
              ·
                refine ⟨9808658083176747741839069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6539105388784498494559379 9808658083176747741839069)
                ·
                  refine ⟨3678246781191280403189651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9808658083176747741839069 3678246781191280403189651)
                  ·
                    refine ⟨5517370171786920604784477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3678246781191280403189651 5517370171786920604784477)
                    ·
                      refine ⟨2069013814420095226794179, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5517370171786920604784477 2069013814420095226794179)
                      ·
                        rfl

theorem cell23_4029390_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 5, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 5, 1, 1, 3, 1, 3].length) (baseStart_4029390 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4029390 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4029390 prefixEnd_4029390 := by exact prefixLift 4029390
  have htrace : WordTrace (prefixWord ++ tailWord_4029390) baseStart_4029390 baseEnd_4029390 := by
    simpa [prefixWord, tailWord_4029390, baseEnd_4029390] using wordTrace_append hprefix tailTrace_4029390
  have hstable : (prefixWord ++ tailWord_4029390).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4029390).length < 2 ^ (prefixWord ++ tailWord_4029390).sum := by decide
  have hdescent : baseEnd_4029390 < baseStart_4029390 := by decide
  rcases family_descends (prefixWord ++ tailWord_4029390) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4029399 : List Nat := [1, 1, 3, 2, 1, 1, 2, 3, 3, 1, 5]
def baseStart_4029399 : Nat := 118140960795 + 4029399 * 2 ^ 59
def prefixEnd_4029399 : Nat := 4983230072969 + 3 ^ 40 * 4029399 * 2
def baseEnd_4029399 : Nat := 2069018435745985691581637

theorem tailTrace_4029399 : CollatzResearch.WordTrace tailWord_4029399 prefixEnd_4029399 2069018435745985691581637 := by
  unfold tailWord_4029399
  simp only [CollatzResearch.WordTrace]
  refine ⟨146964255129183064406571251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97976170086122042937714167 146964255129183064406571251)
  ·
    refine ⟨220446382693774596609856877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146964255129183064406571251 220446382693774596609856877)
    ·
      refine ⟨82667393510165473728696329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 220446382693774596609856877 82667393510165473728696329)
      ·
        refine ⟨62000545132624105296522247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 82667393510165473728696329 62000545132624105296522247)
        ·
          refine ⟨93000817698936157944783371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62000545132624105296522247 93000817698936157944783371)
          ·
            refine ⟨139501226548404236917175057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 93000817698936157944783371 139501226548404236917175057)
            ·
              refine ⟨104625919911303177687881293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 139501226548404236917175057 104625919911303177687881293)
              ·
                refine ⟨39234719966738691632955485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 104625919911303177687881293 39234719966738691632955485)
                ·
                  refine ⟨14713019987527009362358307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 39234719966738691632955485 14713019987527009362358307)
                  ·
                    refine ⟨22069529981290514043537461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14713019987527009362358307 22069529981290514043537461)
                    ·
                      refine ⟨2069018435745985691581637, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 22069529981290514043537461 2069018435745985691581637)
                      ·
                        rfl

theorem cell23_4029399_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 2, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 2, 3, 3, 1, 5].length) (baseStart_4029399 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4029399 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4029399 prefixEnd_4029399 := by exact prefixLift 4029399
  have htrace : WordTrace (prefixWord ++ tailWord_4029399) baseStart_4029399 baseEnd_4029399 := by
    simpa [prefixWord, tailWord_4029399, baseEnd_4029399] using wordTrace_append hprefix tailTrace_4029399
  have hstable : (prefixWord ++ tailWord_4029399).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4029399).length < 2 ^ (prefixWord ++ tailWord_4029399).sum := by decide
  have hdescent : baseEnd_4029399 < baseStart_4029399 := by decide
  rcases family_descends (prefixWord ++ tailWord_4029399) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4029410 : List Nat := [3, 3, 3, 1, 1, 1, 3, 2, 1, 5]
def baseStart_4029410 : Nat := 118140960795 + 4029410 * 2 ^ 59
def prefixEnd_4029410 : Nat := 4983230072969 + 3 ^ 40 * 4029410 * 2
def baseEnd_4029410 : Nat := 689674694677728382848029

theorem tailTrace_4029410 : CollatzResearch.WordTrace tailWord_4029410 prefixEnd_4029410 689674694677728382848029 := by
  unfold tailWord_4029410
  simp only [CollatzResearch.WordTrace]
  refine ⟨36741164083035803321305421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 97976437554762142190147789 36741164083035803321305421)
  ·
    refine ⟨13777936531138426245489533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 36741164083035803321305421 13777936531138426245489533)
    ·
      refine ⟨5166726199176909842058575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13777936531138426245489533 5166726199176909842058575)
      ·
        refine ⟨7750089298765364763087863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5166726199176909842058575 7750089298765364763087863)
        ·
          refine ⟨11625133948148047144631795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7750089298765364763087863 11625133948148047144631795)
          ·
            refine ⟨17437700922222070716947693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11625133948148047144631795 17437700922222070716947693)
            ·
              refine ⟨6539137845833276518855385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17437700922222070716947693 6539137845833276518855385)
              ·
                refine ⟨4904353384374957389141539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6539137845833276518855385 4904353384374957389141539)
                ·
                  refine ⟨7356530076562436083712309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4904353384374957389141539 7356530076562436083712309)
                  ·
                    refine ⟨689674694677728382848029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7356530076562436083712309 689674694677728382848029)
                    ·
                      rfl

theorem cell23_4029410_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 1, 3, 2, 1, 5].length) (baseStart_4029410 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4029410 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4029410 prefixEnd_4029410 := by exact prefixLift 4029410
  have htrace : WordTrace (prefixWord ++ tailWord_4029410) baseStart_4029410 baseEnd_4029410 := by
    simpa [prefixWord, tailWord_4029410, baseEnd_4029410] using wordTrace_append hprefix tailTrace_4029410
  have hstable : (prefixWord ++ tailWord_4029410).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4029410).length < 2 ^ (prefixWord ++ tailWord_4029410).sum := by decide
  have hdescent : baseEnd_4029410 < baseStart_4029410 := by decide
  rcases family_descends (prefixWord ++ tailWord_4029410) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4029447 : List Nat := [1, 1, 4, 3, 1, 1, 3, 4, 1, 2, 2]
def baseStart_4029447 : Nat := 118140960795 + 4029447 * 2 ^ 59
def prefixEnd_4029447 : Nat := 4983230072969 + 3 ^ 40 * 4029447 * 2
def baseEnd_4029447 : Nat := 2069043082817401503781417

theorem tailTrace_4029447 : CollatzResearch.WordTrace tailWord_4029447 prefixEnd_4029447 2069043082817401503781417 := by
  unfold tailWord_4029447
  simp only [CollatzResearch.WordTrace]
  refine ⟨146966005833009168604318595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97977337222006112402879063 146966005833009168604318595)
  ·
    refine ⟨220449008749513752906477893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146966005833009168604318595 220449008749513752906477893)
    ·
      refine ⟨41334189140533828669964605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 220449008749513752906477893 41334189140533828669964605)
      ·
        refine ⟨15500320927700185751236727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 41334189140533828669964605 15500320927700185751236727)
        ·
          refine ⟨23250481391550278626855091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15500320927700185751236727 23250481391550278626855091)
          ·
            refine ⟨34875722087325417940282637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23250481391550278626855091 34875722087325417940282637)
            ·
              refine ⟨13078395782747031727605989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34875722087325417940282637 13078395782747031727605989)
              ·
                refine ⟨2452199209265068448926123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13078395782747031727605989 2452199209265068448926123)
                ·
                  refine ⟨3678298813897602673389185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2452199209265068448926123 3678298813897602673389185)
                  ·
                    refine ⟨2758724110423202005041889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3678298813897602673389185 2758724110423202005041889)
                    ·
                      refine ⟨2069043082817401503781417, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2758724110423202005041889 2069043082817401503781417)
                      ·
                        rfl

theorem cell23_4029447_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 3, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 3, 4, 1, 2, 2].length) (baseStart_4029447 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4029447 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4029447 prefixEnd_4029447 := by exact prefixLift 4029447
  have htrace : WordTrace (prefixWord ++ tailWord_4029447) baseStart_4029447 baseEnd_4029447 := by
    simpa [prefixWord, tailWord_4029447, baseEnd_4029447] using wordTrace_append hprefix tailTrace_4029447
  have hstable : (prefixWord ++ tailWord_4029447).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4029447).length < 2 ^ (prefixWord ++ tailWord_4029447).sum := by decide
  have hdescent : baseEnd_4029447 < baseStart_4029447 := by decide
  rcases family_descends (prefixWord ++ tailWord_4029447) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4029456 : List Nat := [2, 1, 1, 1, 1, 1, 1, 3, 1, 9, 2]
def baseStart_4029456 : Nat := 118140960795 + 4029456 * 2 ^ 59
def prefixEnd_4029456 : Nat := 4983230072969 + 3 ^ 40 * 4029456 * 2
def baseEnd_4029456 : Nat := 2069047704143291968568875

theorem tailTrace_4029456 : CollatzResearch.WordTrace tailWord_4029456 prefixEnd_4029456 2069047704143291968568875 := by
  unfold tailWord_4029456
  simp only [CollatzResearch.WordTrace]
  refine ⟨73483167044988281570698111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97977556059984375427597481 73483167044988281570698111)
  ·
    refine ⟨110224750567482422356047167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73483167044988281570698111 110224750567482422356047167)
    ·
      refine ⟨165337125851223633534070751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110224750567482422356047167 165337125851223633534070751)
      ·
        refine ⟨248005688776835450301106127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 165337125851223633534070751 248005688776835450301106127)
        ·
          refine ⟨372008533165253175451659191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 248005688776835450301106127 372008533165253175451659191)
          ·
            refine ⟨558012799747879763177488787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 372008533165253175451659191 558012799747879763177488787)
            ·
              refine ⟨837019199621819644766233181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 558012799747879763177488787 837019199621819644766233181)
              ·
                refine ⟨313882199858182366787337443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 837019199621819644766233181 313882199858182366787337443)
                ·
                  refine ⟨470823299787273550181006165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 313882199858182366787337443 470823299787273550181006165)
                  ·
                    refine ⟨2758730272191055958091833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 470823299787273550181006165 2758730272191055958091833)
                    ·
                      refine ⟨2069047704143291968568875, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2758730272191055958091833 2069047704143291968568875)
                      ·
                        rfl

theorem cell23_4029456_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 3, 1, 9, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 3, 1, 9, 2].length) (baseStart_4029456 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4029456 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4029456 prefixEnd_4029456 := by exact prefixLift 4029456
  have htrace : WordTrace (prefixWord ++ tailWord_4029456) baseStart_4029456 baseEnd_4029456 := by
    simpa [prefixWord, tailWord_4029456, baseEnd_4029456] using wordTrace_append hprefix tailTrace_4029456
  have hstable : (prefixWord ++ tailWord_4029456).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4029456).length < 2 ^ (prefixWord ++ tailWord_4029456).sum := by decide
  have hdescent : baseEnd_4029456 < baseStart_4029456 := by decide
  rcases family_descends (prefixWord ++ tailWord_4029456) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4029459 : List Nat := [1, 1, 1, 2, 1, 4, 1, 2, 1, 4, 5]
def baseStart_4029459 : Nat := 118140960795 + 4029459 * 2 ^ 59
def prefixEnd_4029459 : Nat := 4983230072969 + 3 ^ 40 * 4029459 * 2
def baseEnd_4029459 : Nat := 2069049244585255456831361

theorem tailTrace_4029459 : CollatzResearch.WordTrace tailWord_4029459 prefixEnd_4029459 2069049244585255456831361 := by
  unfold tailWord_4029459
  simp only [CollatzResearch.WordTrace]
  refine ⟨146966443508965694653755431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97977629005977129769170287 146966443508965694653755431)
  ·
    refine ⟨220449665263448541980633147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146966443508965694653755431 220449665263448541980633147)
    ·
      refine ⟨330674497895172812970949721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 220449665263448541980633147 330674497895172812970949721)
      ·
        refine ⟨248005873421379609728212291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 330674497895172812970949721 248005873421379609728212291)
        ·
          refine ⟨372008810132069414592318437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 248005873421379609728212291 372008810132069414592318437)
          ·
            refine ⟨69751651899763015236059707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 372008810132069414592318437 69751651899763015236059707)
            ·
              refine ⟨104627477849644522854089561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 69751651899763015236059707 104627477849644522854089561)
              ·
                refine ⟨78470608387233392140567171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 104627477849644522854089561 78470608387233392140567171)
                ·
                  refine ⟨117705912580850088210850757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 78470608387233392140567171 117705912580850088210850757)
                  ·
                    refine ⟨22069858608909391539534517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 117705912580850088210850757 22069858608909391539534517)
                    ·
                      refine ⟨2069049244585255456831361, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 22069858608909391539534517 2069049244585255456831361)
                      ·
                        rfl

theorem cell23_4029459_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 1, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 1, 2, 1, 4, 5].length) (baseStart_4029459 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4029459 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4029459 prefixEnd_4029459 := by exact prefixLift 4029459
  have htrace : WordTrace (prefixWord ++ tailWord_4029459) baseStart_4029459 baseEnd_4029459 := by
    simpa [prefixWord, tailWord_4029459, baseEnd_4029459] using wordTrace_append hprefix tailTrace_4029459
  have hstable : (prefixWord ++ tailWord_4029459).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4029459).length < 2 ^ (prefixWord ++ tailWord_4029459).sum := by decide
  have hdescent : baseEnd_4029459 < baseStart_4029459 := by decide
  rcases family_descends (prefixWord ++ tailWord_4029459) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4029463 : List Nat := [1, 1, 3, 5, 1, 1, 1, 3, 1, 3, 3]
def baseStart_4029463 : Nat := 118140960795 + 4029463 * 2 ^ 59
def prefixEnd_4029463 : Nat := 4983230072969 + 3 ^ 40 * 4029463 * 2
def baseEnd_4029463 : Nat := 2069051298507873441181343

theorem tailTrace_4029463 : CollatzResearch.WordTrace tailWord_4029463 prefixEnd_4029463 2069051298507873441181343 := by
  unfold tailWord_4029463
  simp only [CollatzResearch.WordTrace]
  refine ⟨146966589400951203336901043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97977726267300802224600695 146966589400951203336901043)
  ·
    refine ⟨220449884101426805005351565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146966589400951203336901043 220449884101426805005351565)
    ·
      refine ⟨82668706538035051877006837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 220449884101426805005351565 82668706538035051877006837)
      ·
        refine ⟨7750191237940786113469391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 82668706538035051877006837 7750191237940786113469391)
        ·
          refine ⟨11625286856911179170204087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7750191237940786113469391 11625286856911179170204087)
          ·
            refine ⟨17437930285366768755306131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11625286856911179170204087 17437930285366768755306131)
            ·
              refine ⟨26156895428050153132959197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17437930285366768755306131 26156895428050153132959197)
              ·
                refine ⟨9808835785518807424859699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26156895428050153132959197 9808835785518807424859699)
                ·
                  refine ⟨14713253678278211137289549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9808835785518807424859699 14713253678278211137289549)
                  ·
                    refine ⟨5517470129354329176483581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14713253678278211137289549 5517470129354329176483581)
                    ·
                      refine ⟨2069051298507873441181343, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5517470129354329176483581 2069051298507873441181343)
                      ·
                        rfl

theorem cell23_4029463_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 1, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 1, 1, 3, 1, 3, 3].length) (baseStart_4029463 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4029463 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4029463 prefixEnd_4029463 := by exact prefixLift 4029463
  have htrace : WordTrace (prefixWord ++ tailWord_4029463) baseStart_4029463 baseEnd_4029463 := by
    simpa [prefixWord, tailWord_4029463, baseEnd_4029463] using wordTrace_append hprefix tailTrace_4029463
  have hstable : (prefixWord ++ tailWord_4029463).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4029463).length < 2 ^ (prefixWord ++ tailWord_4029463).sum := by decide
  have hdescent : baseEnd_4029463 < baseStart_4029463 := by decide
  rcases family_descends (prefixWord ++ tailWord_4029463) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4029490 : List Nat := [3, 2, 1, 1, 2, 2, 3, 3, 1, 3, 2]
def baseStart_4029490 : Nat := 118140960795 + 4029490 * 2 ^ 59
def prefixEnd_4029490 : Nat := 4983230072969 + 3 ^ 40 * 4029490 * 2
def baseEnd_4029490 : Nat := 2069065162485544835543719

theorem tailTrace_4029490 : CollatzResearch.WordTrace tailWord_4029490 prefixEnd_4029490 2069065162485544835543719 := by
  unfold tailWord_4029490
  simp only [CollatzResearch.WordTrace]
  refine ⟨36741893542963346737033481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 97978382781235591298755949 36741893542963346737033481)
  ·
    refine ⟨27556420157222510052775111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36741893542963346737033481 27556420157222510052775111)
    ·
      refine ⟨41334630235833765079162667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27556420157222510052775111 41334630235833765079162667)
      ·
        refine ⟨62001945353750647618744001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41334630235833765079162667 62001945353750647618744001)
        ·
          refine ⟨46501459015312985714058001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62001945353750647618744001 46501459015312985714058001)
          ·
            refine ⟨34876094261484739285543501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46501459015312985714058001 34876094261484739285543501)
            ·
              refine ⟨13078535348056777232078813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34876094261484739285543501 13078535348056777232078813)
              ·
                refine ⟨4904450755521291462029555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13078535348056777232078813 4904450755521291462029555)
                ·
                  refine ⟨7356676133281937193044333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4904450755521291462029555 7356676133281937193044333)
                  ·
                    refine ⟨2758753549980726447391625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7356676133281937193044333 2758753549980726447391625)
                    ·
                      refine ⟨2069065162485544835543719, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2758753549980726447391625 2069065162485544835543719)
                      ·
                        rfl

theorem cell23_4029490_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 3, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 3, 3, 1, 3, 2].length) (baseStart_4029490 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4029490 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4029490 prefixEnd_4029490 := by exact prefixLift 4029490
  have htrace : WordTrace (prefixWord ++ tailWord_4029490) baseStart_4029490 baseEnd_4029490 := by
    simpa [prefixWord, tailWord_4029490, baseEnd_4029490] using wordTrace_append hprefix tailTrace_4029490
  have hstable : (prefixWord ++ tailWord_4029490).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4029490).length < 2 ^ (prefixWord ++ tailWord_4029490).sum := by decide
  have hdescent : baseEnd_4029490 < baseStart_4029490 := by decide
  rcases family_descends (prefixWord ++ tailWord_4029490) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4029496 : List Nat := [2, 1, 2, 1, 5, 1, 1, 2, 2, 6]
def baseStart_4029496 : Nat := 118140960795 + 4029496 * 2 ^ 59
def prefixEnd_4029496 : Nat := 4983230072969 + 3 ^ 40 * 4029496 * 2
def baseEnd_4029496 : Nat := 689689414456490604022897

theorem tailTrace_4029496 : CollatzResearch.WordTrace tailWord_4029496 prefixEnd_4029496 689689414456490604022897 := by
  unfold tailWord_4029496
  simp only [CollatzResearch.WordTrace]
  refine ⟨73483896504915824986426171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97978528673221099981901561 73483896504915824986426171)
  ·
    refine ⟨110225844757373737479639257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73483896504915824986426171 110225844757373737479639257)
    ·
      refine ⟨82669383568030303109729443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 110225844757373737479639257 82669383568030303109729443)
      ·
        refine ⟨124004075352045454664594165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82669383568030303109729443 124004075352045454664594165)
        ·
          refine ⟨11625382064254261374805703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 124004075352045454664594165 11625382064254261374805703)
          ·
            refine ⟨17438073096381392062208555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11625382064254261374805703 17438073096381392062208555)
            ·
              refine ⟨26157109644572088093312833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17438073096381392062208555 26157109644572088093312833)
              ·
                refine ⟨19617832233429066069984625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26157109644572088093312833 19617832233429066069984625)
                ·
                  refine ⟨14713374175071799552488469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19617832233429066069984625 14713374175071799552488469)
                  ·
                    refine ⟨689689414456490604022897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 14713374175071799552488469 689689414456490604022897)
                    ·
                      rfl

theorem cell23_4029496_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 1, 1, 2, 2, 6].length) (baseStart_4029496 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4029496 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4029496 prefixEnd_4029496 := by exact prefixLift 4029496
  have htrace : WordTrace (prefixWord ++ tailWord_4029496) baseStart_4029496 baseEnd_4029496 := by
    simpa [prefixWord, tailWord_4029496, baseEnd_4029496] using wordTrace_append hprefix tailTrace_4029496
  have hstable : (prefixWord ++ tailWord_4029496).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4029496).length < 2 ^ (prefixWord ++ tailWord_4029496).sum := by decide
  have hdescent : baseEnd_4029496 < baseStart_4029496 := by decide
  rcases family_descends (prefixWord ++ tailWord_4029496) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4029497 : List Nat := [1, 2, 1, 5, 2, 3, 1, 2, 2, 1, 3]
def baseStart_4029497 : Nat := 118140960795 + 4029497 * 2 ^ 59
def prefixEnd_4029497 : Nat := 4983230072969 + 3 ^ 40 * 4029497 * 2
def baseEnd_4029497 : Nat := 2069068756850126308156187

theorem tailTrace_4029497 : CollatzResearch.WordTrace tailWord_4029497 prefixEnd_4029497 2069068756850126308156187 := by
  unfold tailWord_4029497
  simp only [CollatzResearch.WordTrace]
  refine ⟨146967829482828027143638745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97978552988552018095759163 146967829482828027143638745)
  ·
    refine ⟨110225872112121020357729059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 146967829482828027143638745 110225872112121020357729059)
    ·
      refine ⟨165338808168181530536593589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110225872112121020357729059 165338808168181530536593589)
      ·
        refine ⟨15500513265767018487805649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 165338808168181530536593589 15500513265767018487805649)
        ·
          refine ⟨11625384949325263865854237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15500513265767018487805649 11625384949325263865854237)
          ·
            refine ⟨4359519355996973949695339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11625384949325263865854237 4359519355996973949695339)
            ·
              refine ⟨6539279033995460924543009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4359519355996973949695339 6539279033995460924543009)
              ·
                refine ⟨4904459275496595693407257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6539279033995460924543009 4904459275496595693407257)
                ·
                  refine ⟨3678344456622446770055443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4904459275496595693407257 3678344456622446770055443)
                  ·
                    refine ⟨5517516684933670155083165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3678344456622446770055443 5517516684933670155083165)
                    ·
                      refine ⟨2069068756850126308156187, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5517516684933670155083165 2069068756850126308156187)
                      ·
                        rfl

theorem cell23_4029497_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 3, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 3, 1, 2, 2, 1, 3].length) (baseStart_4029497 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4029497 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4029497 prefixEnd_4029497 := by exact prefixLift 4029497
  have htrace : WordTrace (prefixWord ++ tailWord_4029497) baseStart_4029497 baseEnd_4029497 := by
    simpa [prefixWord, tailWord_4029497, baseEnd_4029497] using wordTrace_append hprefix tailTrace_4029497
  have hstable : (prefixWord ++ tailWord_4029497).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4029497).length < 2 ^ (prefixWord ++ tailWord_4029497).sum := by decide
  have hdescent : baseEnd_4029497 < baseStart_4029497 := by decide
  rcases family_descends (prefixWord ++ tailWord_4029497) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4029499 : List Nat := [1, 1, 1, 1, 1, 2, 1, 3, 1, 5, 6]
def baseStart_4029499 : Nat := 118140960795 + 4029499 * 2 ^ 59
def prefixEnd_4029499 : Nat := 4983230072969 + 3 ^ 40 * 4029499 * 2
def baseEnd_4029499 : Nat := 2069069783811435300331177

theorem tailTrace_4029499 : CollatzResearch.WordTrace tailWord_4029499 prefixEnd_4029499 2069069783811435300331177 := by
  unfold tailWord_4029499
  simp only [CollatzResearch.WordTrace]
  refine ⟨146967902428820781485211551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97978601619213854323474367 146967902428820781485211551)
  ·
    refine ⟨220451853643231172227817327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146967902428820781485211551 220451853643231172227817327)
    ·
      refine ⟨330677780464846758341725991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 220451853643231172227817327 330677780464846758341725991)
      ·
        refine ⟨496016670697270137512588987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 330677780464846758341725991 496016670697270137512588987)
        ·
          refine ⟨744025006045905206268883481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 496016670697270137512588987 744025006045905206268883481)
          ·
            refine ⟨558018754534428904701662611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 744025006045905206268883481 558018754534428904701662611)
            ·
              refine ⟨837028131801643357052493917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 558018754534428904701662611 837028131801643357052493917)
              ·
                refine ⟨313885549425616258894685219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 837028131801643357052493917 313885549425616258894685219)
                ·
                  refine ⟨470828324138424388342027829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 313885549425616258894685219 470828324138424388342027829)
                  ·
                    refine ⟨44140155387977286407065109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 470828324138424388342027829 44140155387977286407065109)
                    ·
                      refine ⟨2069069783811435300331177, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 44140155387977286407065109 2069069783811435300331177)
                      ·
                        rfl

theorem cell23_4029499_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 3, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 3, 1, 5, 6].length) (baseStart_4029499 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4029499 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4029499 prefixEnd_4029499 := by exact prefixLift 4029499
  have htrace : WordTrace (prefixWord ++ tailWord_4029499) baseStart_4029499 baseEnd_4029499 := by
    simpa [prefixWord, tailWord_4029499, baseEnd_4029499] using wordTrace_append hprefix tailTrace_4029499
  have hstable : (prefixWord ++ tailWord_4029499).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4029499).length < 2 ^ (prefixWord ++ tailWord_4029499).sum := by decide
  have hdescent : baseEnd_4029499 < baseStart_4029499 := by decide
  rcases family_descends (prefixWord ++ tailWord_4029499) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4029520 : List Nat := [2, 1, 1, 1, 1, 3, 1, 7, 2, 2, 2]
def baseStart_4029520 : Nat := 118140960795 + 4029520 * 2 ^ 59
def prefixEnd_4029520 : Nat := 4983230072969 + 3 ^ 40 * 4029520 * 2
def baseEnd_4029520 : Nat := 2069080566905179718168581

theorem tailTrace_4029520 : CollatzResearch.WordTrace tailWord_4029520 prefixEnd_4029520 2069080566905179718168581 := by
  unfold tailWord_4029520
  simp only [CollatzResearch.WordTrace]
  refine ⟨73484334180872351035863007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97979112241163134714484009 73484334180872351035863007)
  ·
    refine ⟨110226501271308526553794511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73484334180872351035863007 110226501271308526553794511)
    ·
      refine ⟨165339751906962789830691767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110226501271308526553794511 165339751906962789830691767)
      ·
        refine ⟨248009627860444184746037651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 165339751906962789830691767 248009627860444184746037651)
        ·
          refine ⟨372014441790666277119056477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 248009627860444184746037651 372014441790666277119056477)
          ·
            refine ⟨139505415671499853919646179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 372014441790666277119056477 139505415671499853919646179)
            ·
              refine ⟨209258123507249780879469269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 139505415671499853919646179 209258123507249780879469269)
              ·
                refine ⟨4904487269701166739362561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 209258123507249780879469269 4904487269701166739362561)
                ·
                  refine ⟨3678365452275875054521921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4904487269701166739362561 3678365452275875054521921)
                  ·
                    refine ⟨2758774089206906290891441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3678365452275875054521921 2758774089206906290891441)
                    ·
                      refine ⟨2069080566905179718168581, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2758774089206906290891441 2069080566905179718168581)
                      ·
                        rfl

theorem cell23_4029520_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 1, 7, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 1, 7, 2, 2, 2].length) (baseStart_4029520 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4029520 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4029520 prefixEnd_4029520 := by exact prefixLift 4029520
  have htrace : WordTrace (prefixWord ++ tailWord_4029520) baseStart_4029520 baseEnd_4029520 := by
    simpa [prefixWord, tailWord_4029520, baseEnd_4029520] using wordTrace_append hprefix tailTrace_4029520
  have hstable : (prefixWord ++ tailWord_4029520).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4029520).length < 2 ^ (prefixWord ++ tailWord_4029520).sum := by decide
  have hdescent : baseEnd_4029520 < baseStart_4029520 := by decide
  rcases family_descends (prefixWord ++ tailWord_4029520) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4029593 : List Nat := [1, 2, 1, 2, 1, 2, 1, 1, 6, 4, 2]
def baseStart_4029593 : Nat := 118140960795 + 4029593 * 2 ^ 59
def prefixEnd_4029593 : Nat := 4983230072969 + 3 ^ 40 * 4029593 * 2
def baseEnd_4029593 : Nat := 2069118050992957932555745

theorem tailTrace_4029593 : CollatzResearch.WordTrace tailWord_4029593 prefixEnd_4029593 2069118050992957932555745 := by
  unfold tailWord_4029593
  simp only [CollatzResearch.WordTrace]
  refine ⟨146971330890480235539133433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97980887260320157026088955 146971330890480235539133433)
  ·
    refine ⟨110228498167860176654350075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 146971330890480235539133433 110228498167860176654350075)
    ·
      refine ⟨165342747251790264981525113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110228498167860176654350075 165342747251790264981525113)
      ·
        refine ⟨124007060438842698736143835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 165342747251790264981525113 124007060438842698736143835)
        ·
          refine ⟨186010590658264048104215753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 124007060438842698736143835 186010590658264048104215753)
          ·
            refine ⟨139507942993698036078161815, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 186010590658264048104215753 139507942993698036078161815)
            ·
              refine ⟨209261914490547054117242723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 139507942993698036078161815 209261914490547054117242723)
              ·
                refine ⟨313892871735820581175864085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 209261914490547054117242723 313892871735820581175864085)
                ·
                  refine ⟨14713728362616589742618629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 313892871735820581175864085 14713728362616589742618629)
                  ·
                    refine ⟨2758824067990610576740993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 14713728362616589742618629 2758824067990610576740993)
                    ·
                      refine ⟨2069118050992957932555745, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2758824067990610576740993 2069118050992957932555745)
                      ·
                        rfl

theorem cell23_4029593_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 1, 1, 6, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 1, 1, 6, 4, 2].length) (baseStart_4029593 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4029593 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4029593 prefixEnd_4029593 := by exact prefixLift 4029593
  have htrace : WordTrace (prefixWord ++ tailWord_4029593) baseStart_4029593 baseEnd_4029593 := by
    simpa [prefixWord, tailWord_4029593, baseEnd_4029593] using wordTrace_append hprefix tailTrace_4029593
  have hstable : (prefixWord ++ tailWord_4029593).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4029593).length < 2 ^ (prefixWord ++ tailWord_4029593).sum := by decide
  have hdescent : baseEnd_4029593 < baseStart_4029593 := by decide
  rcases family_descends (prefixWord ++ tailWord_4029593) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4029677 : List Nat := [1, 5, 1, 2, 2, 1, 1, 3, 3, 1, 3]
def baseStart_4029677 : Nat := 118140960795 + 4029677 * 2 ^ 59
def prefixEnd_4029677 : Nat := 4983230072969 + 3 ^ 40 * 4029677 * 2
def baseEnd_4029677 : Nat := 2069161183367935603905359

theorem tailTrace_4029677 : CollatzResearch.WordTrace tailWord_4029677 prefixEnd_4029677 2069161183367935603905359 := by
  unfold tailWord_4029677
  simp only [CollatzResearch.WordTrace]
  refine ⟨146974394622175917885191285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97982929748117278590127523 146974394622175917885191285)
  ·
    refine ⟨13778849495828992301736683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 146974394622175917885191285 13778849495828992301736683)
    ·
      refine ⟨20668274243743488452605025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13778849495828992301736683 20668274243743488452605025)
      ·
        refine ⟨15501205682807616339453769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20668274243743488452605025 15501205682807616339453769)
        ·
          refine ⟨11625904262105712254590327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15501205682807616339453769 11625904262105712254590327)
          ·
            refine ⟨17438856393158568381885491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11625904262105712254590327 17438856393158568381885491)
            ·
              refine ⟨26158284589737852572828237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17438856393158568381885491 26158284589737852572828237)
              ·
                refine ⟨9809356721151694714810589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26158284589737852572828237 9809356721151694714810589)
                ·
                  refine ⟨3678508770431885518053971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9809356721151694714810589 3678508770431885518053971)
                  ·
                    refine ⟨5517763155647828277080957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3678508770431885518053971 5517763155647828277080957)
                    ·
                      refine ⟨2069161183367935603905359, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5517763155647828277080957 2069161183367935603905359)
                      ·
                        rfl

theorem cell23_4029677_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 1, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 1, 1, 3, 3, 1, 3].length) (baseStart_4029677 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4029677 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4029677 prefixEnd_4029677 := by exact prefixLift 4029677
  have htrace : WordTrace (prefixWord ++ tailWord_4029677) baseStart_4029677 baseEnd_4029677 := by
    simpa [prefixWord, tailWord_4029677, baseEnd_4029677] using wordTrace_append hprefix tailTrace_4029677
  have hstable : (prefixWord ++ tailWord_4029677).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4029677).length < 2 ^ (prefixWord ++ tailWord_4029677).sum := by decide
  have hdescent : baseEnd_4029677 < baseStart_4029677 := by decide
  rcases family_descends (prefixWord ++ tailWord_4029677) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4029710 : List Nat := [4, 1, 1, 2, 1, 3, 1, 2, 4, 4]
def baseStart_4029710 : Nat := 118140960795 + 4029710 * 2 ^ 59
def prefixEnd_4029710 : Nat := 4983230072969 + 3 ^ 40 * 4029710 * 2
def baseEnd_4029710 : Nat := 689726042743177991597569

theorem tailTrace_4029710 : CollatzResearch.WordTrace tailWord_4029710 prefixEnd_4029710 689726042743177991597569 := by
  unfold tailWord_4029710
  simp only [CollatzResearch.WordTrace]
  refine ⟨18371949778882045565142823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 97983732154037576347428389 18371949778882045565142823)
  ·
    refine ⟨27557924668323068347714235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18371949778882045565142823 27557924668323068347714235)
    ·
      refine ⟨41336887002484602521571353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27557924668323068347714235 41336887002484602521571353)
      ·
        refine ⟨31002665251863451891178515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41336887002484602521571353 31002665251863451891178515)
        ·
          refine ⟨46503997877795177836767773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31002665251863451891178515 46503997877795177836767773)
          ·
            refine ⟨17438999204173191688787915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 46503997877795177836767773 17438999204173191688787915)
            ·
              refine ⟨26158498806259787533181873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17438999204173191688787915 26158498806259787533181873)
              ·
                refine ⟨19618874104694840649886405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26158498806259787533181873 19618874104694840649886405)
                ·
                  refine ⟨3678538894630282621853701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 19618874104694840649886405 3678538894630282621853701)
                  ·
                    refine ⟨689726042743177991597569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3678538894630282621853701 689726042743177991597569)
                    ·
                      rfl

theorem cell23_4029710_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 3, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 3, 1, 2, 4, 4].length) (baseStart_4029710 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4029710 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4029710 prefixEnd_4029710 := by exact prefixLift 4029710
  have htrace : WordTrace (prefixWord ++ tailWord_4029710) baseStart_4029710 baseEnd_4029710 := by
    simpa [prefixWord, tailWord_4029710, baseEnd_4029710] using wordTrace_append hprefix tailTrace_4029710
  have hstable : (prefixWord ++ tailWord_4029710).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4029710).length < 2 ^ (prefixWord ++ tailWord_4029710).sum := by decide
  have hdescent : baseEnd_4029710 < baseStart_4029710 := by decide
  rcases family_descends (prefixWord ++ tailWord_4029710) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4029713 : List Nat := [1, 2, 2, 1, 1, 4, 2, 1, 3, 2, 4]
def baseStart_4029713 : Nat := 118140960795 + 4029713 * 2 ^ 59
def prefixEnd_4029713 : Nat := 4983230072969 + 3 ^ 40 * 4029713 * 2
def baseEnd_4029713 : Nat := 2069179668671497463055193

theorem tailTrace_4029713 : CollatzResearch.WordTrace tailWord_4029713 prefixEnd_4029713 2069179668671497463055193 := by
  unfold tailWord_4029713
  simp only [CollatzResearch.WordTrace]
  refine ⟨146975707650045496033501793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97983805100030330689001195 146975707650045496033501793)
  ·
    refine ⟨110231780737534122025126345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 146975707650045496033501793 110231780737534122025126345)
    ·
      refine ⟨82673835553150591518844759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 110231780737534122025126345 82673835553150591518844759)
      ·
        refine ⟨124010753329725887278267139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82673835553150591518844759 124010753329725887278267139)
        ·
          refine ⟨186016129994588830917400709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 124010753329725887278267139 186016129994588830917400709)
          ·
            refine ⟨34878024373985405797012633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 186016129994588830917400709 34878024373985405797012633)
            ·
              refine ⟨26158518280489054347759475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34878024373985405797012633 26158518280489054347759475)
              ·
                refine ⟨39237777420733581521639213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26158518280489054347759475 39237777420733581521639213)
                ·
                  refine ⟨14714166532775093070614705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 39237777420733581521639213 14714166532775093070614705)
                  ·
                    refine ⟨11035624899581319802961029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14714166532775093070614705 11035624899581319802961029)
                    ·
                      refine ⟨2069179668671497463055193, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11035624899581319802961029 2069179668671497463055193)
                      ·
                        rfl

theorem cell23_4029713_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 2, 4].length) (baseStart_4029713 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4029713 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4029713 prefixEnd_4029713 := by exact prefixLift 4029713
  have htrace : WordTrace (prefixWord ++ tailWord_4029713) baseStart_4029713 baseEnd_4029713 := by
    simpa [prefixWord, tailWord_4029713, baseEnd_4029713] using wordTrace_append hprefix tailTrace_4029713
  have hstable : (prefixWord ++ tailWord_4029713).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4029713).length < 2 ^ (prefixWord ++ tailWord_4029713).sum := by decide
  have hdescent : baseEnd_4029713 < baseStart_4029713 := by decide
  rcases family_descends (prefixWord ++ tailWord_4029713) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4029720 : List Nat := [2, 1, 2, 3, 1, 4, 2, 1, 1, 1, 5]
def baseStart_4029720 : Nat := 118140960795 + 4029720 * 2 ^ 59
def prefixEnd_4029720 : Nat := 4983230072969 + 3 ^ 40 * 4029720 * 2
def baseEnd_4029720 : Nat := 2069183263036078935667661

theorem tailTrace_4029720 : CollatzResearch.WordTrace tailWord_4029720 prefixEnd_4029720 2069183263036078935667661 := by
  unfold tailWord_4029720
  simp only [CollatzResearch.WordTrace]
  refine ⟨73487981480510068114503307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97983975307346757486004409 73487981480510068114503307)
  ·
    refine ⟨110231972220765102171754961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73487981480510068114503307 110231972220765102171754961)
    ·
      refine ⟨82673979165573826628816221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 110231972220765102171754961 82673979165573826628816221)
      ·
        refine ⟨31002742187090184985806083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 82673979165573826628816221 31002742187090184985806083)
        ·
          refine ⟨46504113280635277478709125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31002742187090184985806083 46504113280635277478709125)
          ·
            refine ⟨8719521240119114527257961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 46504113280635277478709125 8719521240119114527257961)
            ·
              refine ⟨6539640930089335895443471, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8719521240119114527257961 6539640930089335895443471)
              ·
                refine ⟨9809461395134003843165207, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6539640930089335895443471 9809461395134003843165207)
                ·
                  refine ⟨14714192092701005764747811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9809461395134003843165207 14714192092701005764747811)
                  ·
                    refine ⟨22071288139051508647121717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14714192092701005764747811 22071288139051508647121717)
                    ·
                      refine ⟨2069183263036078935667661, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 22071288139051508647121717 2069183263036078935667661)
                      ·
                        rfl

theorem cell23_4029720_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 4, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 4, 2, 1, 1, 1, 5].length) (baseStart_4029720 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4029720 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4029720 prefixEnd_4029720 := by exact prefixLift 4029720
  have htrace : WordTrace (prefixWord ++ tailWord_4029720) baseStart_4029720 baseEnd_4029720 := by
    simpa [prefixWord, tailWord_4029720, baseEnd_4029720] using wordTrace_append hprefix tailTrace_4029720
  have hstable : (prefixWord ++ tailWord_4029720).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4029720).length < 2 ^ (prefixWord ++ tailWord_4029720).sum := by decide
  have hdescent : baseEnd_4029720 < baseStart_4029720 := by decide
  rcases family_descends (prefixWord ++ tailWord_4029720) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4029793 : List Nat := [1, 2, 3, 1, 1, 1, 1, 4, 1, 3, 5]
def baseStart_4029793 : Nat := 118140960795 + 4029793 * 2 ^ 59
def prefixEnd_4029793 : Nat := 4983230072969 + 3 ^ 40 * 4029793 * 2
def baseEnd_4029793 : Nat := 2069220747123857150054825

theorem tailTrace_4029793 : CollatzResearch.WordTrace tailWord_4029793 prefixEnd_4029793 2069220747123857150054825 := by
  unfold tailWord_4029793
  simp only [CollatzResearch.WordTrace]
  refine ⟨146978625489755669696414033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97985750326503779797609355 146978625489755669696414033)
  ·
    refine ⟨110233969117316752272310525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 146978625489755669696414033 110233969117316752272310525)
    ·
      refine ⟨41337738418993782102116447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 110233969117316752272310525 41337738418993782102116447)
      ·
        refine ⟨62006607628490673153174671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41337738418993782102116447 62006607628490673153174671)
        ·
          refine ⟨93009911442736009729762007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62006607628490673153174671 93009911442736009729762007)
          ·
            refine ⟨139514867164104014594643011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 93009911442736009729762007 139514867164104014594643011)
            ·
              refine ⟨209272300746156021891964517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 139514867164104014594643011 209272300746156021891964517)
              ·
                refine ⟨39238556389904254104743347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 209272300746156021891964517 39238556389904254104743347)
                ·
                  refine ⟨58857834584856381157115021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39238556389904254104743347 58857834584856381157115021)
                  ·
                    refine ⟨22071687969321142933918133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 58857834584856381157115021 22071687969321142933918133)
                    ·
                      refine ⟨2069220747123857150054825, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 22071687969321142933918133 2069220747123857150054825)
                      ·
                        rfl

theorem cell23_4029793_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 1, 4, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 1, 4, 1, 3, 5].length) (baseStart_4029793 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4029793 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4029793 prefixEnd_4029793 := by exact prefixLift 4029793
  have htrace : WordTrace (prefixWord ++ tailWord_4029793) baseStart_4029793 baseEnd_4029793 := by
    simpa [prefixWord, tailWord_4029793, baseEnd_4029793] using wordTrace_append hprefix tailTrace_4029793
  have hstable : (prefixWord ++ tailWord_4029793).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4029793).length < 2 ^ (prefixWord ++ tailWord_4029793).sum := by decide
  have hdescent : baseEnd_4029793 < baseStart_4029793 := by decide
  rcases family_descends (prefixWord ++ tailWord_4029793) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4029807 : List Nat := [1, 1, 2, 1, 3, 1, 6, 1, 1, 4, 2]
def baseStart_4029807 : Nat := 118140960795 + 4029807 * 2 ^ 59
def prefixEnd_4029807 : Nat := 4983230072969 + 3 ^ 40 * 4029807 * 2
def baseEnd_4029807 : Nat := 2069227935853020095279761

theorem tailTrace_4029807 : CollatzResearch.WordTrace tailWord_4029807 prefixEnd_4029807 2069227935853020095279761 := by
  unfold tailWord_4029807
  simp only [CollatzResearch.WordTrace]
  refine ⟨146979136111704950087423675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97986090741136633391615783 146979136111704950087423675)
  ·
    refine ⟨220468704167557425131135513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146979136111704950087423675 220468704167557425131135513)
    ·
      refine ⟨165351528125668068848351635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 220468704167557425131135513 165351528125668068848351635)
      ·
        refine ⟨248027292188502103272527453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 165351528125668068848351635 248027292188502103272527453)
        ·
          refine ⟨93010234570688288727197795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 248027292188502103272527453 93010234570688288727197795)
          ·
            refine ⟨139515351856032433090796693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 93010234570688288727197795 139515351856032433090796693)
            ·
              refine ⟨6539782118251520301131095, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 139515351856032433090796693 6539782118251520301131095)
              ·
                refine ⟨9809673177377280451696643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6539782118251520301131095 9809673177377280451696643)
                ·
                  refine ⟨14714509766065920677544965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9809673177377280451696643 14714509766065920677544965)
                  ·
                    refine ⟨2758970581137360127039681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 14714509766065920677544965 2758970581137360127039681)
                    ·
                      refine ⟨2069227935853020095279761, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2758970581137360127039681 2069227935853020095279761)
                      ·
                        rfl

theorem cell23_4029807_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 6, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 6, 1, 1, 4, 2].length) (baseStart_4029807 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4029807 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4029807 prefixEnd_4029807 := by exact prefixLift 4029807
  have htrace : WordTrace (prefixWord ++ tailWord_4029807) baseStart_4029807 baseEnd_4029807 := by
    simpa [prefixWord, tailWord_4029807, baseEnd_4029807] using wordTrace_append hprefix tailTrace_4029807
  have hstable : (prefixWord ++ tailWord_4029807).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4029807).length < 2 ^ (prefixWord ++ tailWord_4029807).sum := by decide
  have hdescent : baseEnd_4029807 < baseStart_4029807 := by decide
  rcases family_descends (prefixWord ++ tailWord_4029807) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4029810 : List Nat := [3, 2, 1, 2, 1, 2, 1, 2, 2, 4, 3]
def baseStart_4029810 : Nat := 118140960795 + 4029810 * 2 ^ 59
def prefixEnd_4029810 : Nat := 4983230072969 + 3 ^ 40 * 4029810 * 2
def baseEnd_4029810 : Nat := 2069229476294983583542247

theorem tailTrace_4029810 : CollatzResearch.WordTrace tailWord_4029810 prefixEnd_4029810 2069229476294983583542247 := by
  unfold tailWord_4029810
  simp only [CollatzResearch.WordTrace]
  refine ⟨36744811382673520399945721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 97986163687129387733188589 36744811382673520399945721)
  ·
    refine ⟨27558608537005140299959291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36744811382673520399945721 27558608537005140299959291)
    ·
      refine ⟨41337912805507710449938937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27558608537005140299959291 41337912805507710449938937)
      ·
        refine ⟨31003434604130782837454203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41337912805507710449938937 31003434604130782837454203)
        ·
          refine ⟨46505151906196174256181305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31003434604130782837454203 46505151906196174256181305)
          ·
            refine ⟨34878863929647130692135979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46505151906196174256181305 34878863929647130692135979)
            ·
              refine ⟨52318295894470696038203969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34878863929647130692135979 52318295894470696038203969)
              ·
                refine ⟨39238721920853022028652977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 52318295894470696038203969 39238721920853022028652977)
                ·
                  refine ⟨29429041440639766521489733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 39238721920853022028652977 29429041440639766521489733)
                  ·
                    refine ⟨5517945270119956222779325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 29429041440639766521489733 5517945270119956222779325)
                    ·
                      refine ⟨2069229476294983583542247, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5517945270119956222779325 2069229476294983583542247)
                      ·
                        rfl

theorem cell23_4029810_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 1, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 1, 2, 2, 4, 3].length) (baseStart_4029810 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4029810 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4029810 prefixEnd_4029810 := by exact prefixLift 4029810
  have htrace : WordTrace (prefixWord ++ tailWord_4029810) baseStart_4029810 baseEnd_4029810 := by
    simpa [prefixWord, tailWord_4029810, baseEnd_4029810] using wordTrace_append hprefix tailTrace_4029810
  have hstable : (prefixWord ++ tailWord_4029810).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4029810).length < 2 ^ (prefixWord ++ tailWord_4029810).sum := by decide
  have hdescent : baseEnd_4029810 < baseStart_4029810 := by decide
  rcases family_descends (prefixWord ++ tailWord_4029810) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4029858 : List Nat := [3, 3, 1, 2, 1, 3, 3, 1, 2, 2, 2]
def baseStart_4029858 : Nat := 118140960795 + 4029858 * 2 ^ 59
def prefixEnd_4029858 : Nat := 4983230072969 + 3 ^ 40 * 4029858 * 2
def baseEnd_4029858 : Nat := 2069254123366399395742027

theorem tailTrace_4029858 : CollatzResearch.WordTrace tailWord_4029858 prefixEnd_4029858 2069254123366399395742027 := by
  unfold tailWord_4029858
  simp only [CollatzResearch.WordTrace]
  refine ⟨36745249058630046449382557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 97987330823013457198353485 36745249058630046449382557)
  ·
    refine ⟨13779468396986267418518459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 36745249058630046449382557 13779468396986267418518459)
    ·
      refine ⟨20669202595479401127777689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13779468396986267418518459 20669202595479401127777689)
      ·
        refine ⟨15501901946609550845833267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20669202595479401127777689 15501901946609550845833267)
        ·
          refine ⟨23252852919914326268749901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15501901946609550845833267 23252852919914326268749901)
          ·
            refine ⟨8719819844967872350781213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23252852919914326268749901 8719819844967872350781213)
            ·
              refine ⟨3269932441862952131542955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8719819844967872350781213 3269932441862952131542955)
              ·
                refine ⟨4904898662794428197314433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3269932441862952131542955 4904898662794428197314433)
                ·
                  refine ⟨3678673997095821147985825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4904898662794428197314433 3678673997095821147985825)
                  ·
                    refine ⟨2759005497821865860989369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3678673997095821147985825 2759005497821865860989369)
                    ·
                      refine ⟨2069254123366399395742027, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2759005497821865860989369 2069254123366399395742027)
                      ·
                        rfl

theorem cell23_4029858_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 3, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 3, 3, 1, 2, 2, 2].length) (baseStart_4029858 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4029858 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4029858 prefixEnd_4029858 := by exact prefixLift 4029858
  have htrace : WordTrace (prefixWord ++ tailWord_4029858) baseStart_4029858 baseEnd_4029858 := by
    simpa [prefixWord, tailWord_4029858, baseEnd_4029858] using wordTrace_append hprefix tailTrace_4029858
  have hstable : (prefixWord ++ tailWord_4029858).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4029858).length < 2 ^ (prefixWord ++ tailWord_4029858).sum := by decide
  have hdescent : baseEnd_4029858 < baseStart_4029858 := by decide
  rcases family_descends (prefixWord ++ tailWord_4029858) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4029880 : List Nat := [2, 1, 2, 1, 2, 2, 4, 1, 1, 3, 4]
def baseStart_4029880 : Nat := 118140960795 + 4029880 * 2 ^ 59
def prefixEnd_4029880 : Nat := 4983230072969 + 3 ^ 40 * 4029880 * 2
def baseEnd_4029880 : Nat := 2069265419940798309666925

theorem tailTrace_4029880 : CollatzResearch.WordTrace tailWord_4029880 prefixEnd_4029880 2069265419940798309666925 := by
  unfold tailWord_4029880
  simp only [CollatzResearch.WordTrace]
  refine ⟨73490899320220241777415547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97987865760293655703220729 73490899320220241777415547)
  ·
    refine ⟨110236348980330362666123321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73490899320220241777415547 110236348980330362666123321)
    ·
      refine ⟨82677261735247771999592491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 110236348980330362666123321 82677261735247771999592491)
      ·
        refine ⟨124015892602871657999388737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82677261735247771999592491 124015892602871657999388737)
        ·
          refine ⟨93011919452153743499541553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 124015892602871657999388737 93011919452153743499541553)
          ·
            refine ⟨69758939589115307624656165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 93011919452153743499541553 69758939589115307624656165)
            ·
              refine ⟨13079801172959120179623031, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 69758939589115307624656165 13079801172959120179623031)
              ·
                refine ⟨19619701759438680269434547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13079801172959120179623031 19619701759438680269434547)
                ·
                  refine ⟨29429552639158020404151821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19619701759438680269434547 29429552639158020404151821)
                  ·
                    refine ⟨11036082239684257651556933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 29429552639158020404151821 11036082239684257651556933)
                    ·
                      refine ⟨2069265419940798309666925, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11036082239684257651556933 2069265419940798309666925)
                      ·
                        rfl

theorem cell23_4029880_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 4, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 4, 1, 1, 3, 4].length) (baseStart_4029880 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4029880 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4029880 prefixEnd_4029880 := by exact prefixLift 4029880
  have htrace : WordTrace (prefixWord ++ tailWord_4029880) baseStart_4029880 baseEnd_4029880 := by
    simpa [prefixWord, tailWord_4029880, baseEnd_4029880] using wordTrace_append hprefix tailTrace_4029880
  have hstable : (prefixWord ++ tailWord_4029880).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4029880).length < 2 ^ (prefixWord ++ tailWord_4029880).sum := by decide
  have hdescent : baseEnd_4029880 < baseStart_4029880 := by decide
  rcases family_descends (prefixWord ++ tailWord_4029880) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4029881 : List Nat := [1, 2, 1, 4, 5, 1, 1, 3, 5]
def baseStart_4029881 : Nat := 118140960795 + 4029881 * 2 ^ 59
def prefixEnd_4029881 : Nat := 4983230072969 + 3 ^ 40 * 4029881 * 2
def baseEnd_4029881 : Nat := 229918437046828089528269

theorem tailTrace_4029881 : CollatzResearch.WordTrace tailWord_4029881 prefixEnd_4029881 229918437046828089528269 := by
  unfold tailWord_4029881
  simp only [CollatzResearch.WordTrace]
  refine ⟨146981835113436860725617497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97987890075624573817078331 146981835113436860725617497)
  ·
    refine ⟨110236376335077645544213123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 146981835113436860725617497 110236376335077645544213123)
    ·
      refine ⟨165354564502616468316319685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110236376335077645544213123 165354564502616468316319685)
      ·
        refine ⟨31003980844240587809309941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 165354564502616468316319685 31003980844240587809309941)
        ·
          refine ⟨2906623204147555107122807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 31003980844240587809309941 2906623204147555107122807)
          ·
            refine ⟨4359934806221332660684211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2906623204147555107122807 4359934806221332660684211)
            ·
              refine ⟨6539902209331998991026317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4359934806221332660684211 6539902209331998991026317)
              ·
                refine ⟨2452463328499499621634869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6539902209331998991026317 2452463328499499621634869)
                ·
                  refine ⟨229918437046828089528269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2452463328499499621634869 229918437046828089528269)
                  ·
                    rfl

theorem cell23_4029881_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 5, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 5, 1, 1, 3, 5].length) (baseStart_4029881 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4029881 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4029881 prefixEnd_4029881 := by exact prefixLift 4029881
  have htrace : WordTrace (prefixWord ++ tailWord_4029881) baseStart_4029881 baseEnd_4029881 := by
    simpa [prefixWord, tailWord_4029881, baseEnd_4029881] using wordTrace_append hprefix tailTrace_4029881
  have hstable : (prefixWord ++ tailWord_4029881).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4029881).length < 2 ^ (prefixWord ++ tailWord_4029881).sum := by decide
  have hdescent : baseEnd_4029881 < baseStart_4029881 := by decide
  rcases family_descends (prefixWord ++ tailWord_4029881) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4029883 : List Nat := [1, 1, 1, 1, 1, 2, 2, 1, 1, 1, 11]
def baseStart_4029883 : Nat := 118140960795 + 4029883 * 2 ^ 59
def prefixEnd_4029883 : Nat := 4983230072969 + 3 ^ 40 * 4029883 * 2
def baseEnd_4029883 : Nat := 2069266960382761797929411

theorem tailTrace_4029883 : CollatzResearch.WordTrace tailWord_4029883 prefixEnd_4029883 2069266960382761797929411 := by
  unfold tailWord_4029883
  simp only [CollatzResearch.WordTrace]
  refine ⟨146981908059429615067190303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97987938706286410044793535 146981908059429615067190303)
  ·
    refine ⟨220472862089144422600785455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146981908059429615067190303 220472862089144422600785455)
    ·
      refine ⟨330709293133716633901178183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 220472862089144422600785455 330709293133716633901178183)
      ·
        refine ⟨496063939700574950851767275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 330709293133716633901178183 496063939700574950851767275)
        ·
          refine ⟨744095909550862426277650913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 496063939700574950851767275 744095909550862426277650913)
          ·
            refine ⟨558071932163146819708238185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 744095909550862426277650913 558071932163146819708238185)
            ·
              refine ⟨418553949122360114781178639, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 558071932163146819708238185 418553949122360114781178639)
              ·
                refine ⟨627830923683540172171767959, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 418553949122360114781178639 627830923683540172171767959)
                ·
                  refine ⟨941746385525310258257651939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 627830923683540172171767959 941746385525310258257651939)
                  ·
                    refine ⟨1412619578287965387386477909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 941746385525310258257651939 1412619578287965387386477909)
                    ·
                      refine ⟨2069266960382761797929411, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 11 1412619578287965387386477909 2069266960382761797929411)
                      ·
                        rfl

theorem cell23_4029883_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 1, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 1, 1, 1, 11].length) (baseStart_4029883 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4029883 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4029883 prefixEnd_4029883 := by exact prefixLift 4029883
  have htrace : WordTrace (prefixWord ++ tailWord_4029883) baseStart_4029883 baseEnd_4029883 := by
    simpa [prefixWord, tailWord_4029883, baseEnd_4029883] using wordTrace_append hprefix tailTrace_4029883
  have hstable : (prefixWord ++ tailWord_4029883).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4029883).length < 2 ^ (prefixWord ++ tailWord_4029883).sum := by decide
  have hdescent : baseEnd_4029883 < baseStart_4029883 := by decide
  rcases family_descends (prefixWord ++ tailWord_4029883) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4029934 : List Nat := [4, 1, 2, 1, 2, 1, 4, 1, 2, 2, 3]
def baseStart_4029934 : Nat := 118140960795 + 4029934 * 2 ^ 59
def prefixEnd_4029934 : Nat := 4983230072969 + 3 ^ 40 * 4029934 * 2
def baseEnd_4029934 : Nat := 2069293147896141098391677

theorem tailTrace_4029934 : CollatzResearch.WordTrace tailWord_4029934 prefixEnd_4029934 2069293147896141098391677 := by
  unfold tailWord_4029934
  simp only [CollatzResearch.WordTrace]
  refine ⟨18372971022780606347162107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 97989178788163233851531237 18372971022780606347162107)
  ·
    refine ⟨27559456534170909520743161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18372971022780606347162107 27559456534170909520743161)
    ·
      refine ⟨20669592400628182140557371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27559456534170909520743161 20669592400628182140557371)
      ·
        refine ⟨31004388600942273210836057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20669592400628182140557371 31004388600942273210836057)
        ·
          refine ⟨23253291450706704908127043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31004388600942273210836057 23253291450706704908127043)
          ·
            refine ⟨34879937176060057362190565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23253291450706704908127043 34879937176060057362190565)
            ·
              refine ⟨6539988220511260755410731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 34879937176060057362190565 6539988220511260755410731)
              ·
                refine ⟨9809982330766891133116097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6539988220511260755410731 9809982330766891133116097)
                ·
                  refine ⟨7357486748075168349837073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9809982330766891133116097 7357486748075168349837073)
                  ·
                    refine ⟨5518115061056376262377805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7357486748075168349837073 5518115061056376262377805)
                    ·
                      refine ⟨2069293147896141098391677, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5518115061056376262377805 2069293147896141098391677)
                      ·
                        rfl

theorem cell23_4029934_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 4, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 4, 1, 2, 2, 3].length) (baseStart_4029934 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4029934 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4029934 prefixEnd_4029934 := by exact prefixLift 4029934
  have htrace : WordTrace (prefixWord ++ tailWord_4029934) baseStart_4029934 baseEnd_4029934 := by
    simpa [prefixWord, tailWord_4029934, baseEnd_4029934] using wordTrace_append hprefix tailTrace_4029934
  have hstable : (prefixWord ++ tailWord_4029934).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4029934).length < 2 ^ (prefixWord ++ tailWord_4029934).sum := by decide
  have hdescent : baseEnd_4029934 < baseStart_4029934 := by decide
  rcases family_descends (prefixWord ++ tailWord_4029934) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4029947 : List Nat := [1, 1, 1, 1, 1, 3, 2, 4, 5, 1, 3]
def baseStart_4029947 : Nat := 118140960795 + 4029947 * 2 ^ 59
def prefixEnd_4029947 : Nat := 4983230072969 + 3 ^ 40 * 4029947 * 2
def baseEnd_4029947 : Nat := 2069299823144649547529117

theorem tailTrace_4029947 : CollatzResearch.WordTrace tailWord_4029947 prefixEnd_4029947 2069299823144649547529117 := by
  unfold tailWord_4029947
  simp only [CollatzResearch.WordTrace]
  refine ⟨146984242331197753997520095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97989494887465169331680063 146984242331197753997520095)
  ·
    refine ⟨220476363496796630996280143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146984242331197753997520095 220476363496796630996280143)
    ·
      refine ⟨330714545245194946494420215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 220476363496796630996280143 330714545245194946494420215)
      ·
        refine ⟨496071817867792419741630323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 330714545245194946494420215 496071817867792419741630323)
        ·
          refine ⟨744107726801688629612445485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 496071817867792419741630323 744107726801688629612445485)
          ·
            refine ⟨279040397550633236104667057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 744107726801688629612445485 279040397550633236104667057)
            ·
              refine ⟨209280298162974927078500293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 279040397550633236104667057 209280298162974927078500293)
              ·
                refine ⟨39240055905557798827218805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 209280298162974927078500293 39240055905557798827218805)
                ·
                  refine ⟨3678755241146043640051763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 39240055905557798827218805 3678755241146043640051763)
                  ·
                    refine ⟨5518132861719065460077645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3678755241146043640051763 5518132861719065460077645)
                    ·
                      refine ⟨2069299823144649547529117, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5518132861719065460077645 2069299823144649547529117)
                      ·
                        rfl

theorem cell23_4029947_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 2, 4, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 2, 4, 5, 1, 3].length) (baseStart_4029947 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4029947 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4029947 prefixEnd_4029947 := by exact prefixLift 4029947
  have htrace : WordTrace (prefixWord ++ tailWord_4029947) baseStart_4029947 baseEnd_4029947 := by
    simpa [prefixWord, tailWord_4029947, baseEnd_4029947] using wordTrace_append hprefix tailTrace_4029947
  have hstable : (prefixWord ++ tailWord_4029947).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4029947).length < 2 ^ (prefixWord ++ tailWord_4029947).sum := by decide
  have hdescent : baseEnd_4029947 < baseStart_4029947 := by decide
  rcases family_descends (prefixWord ++ tailWord_4029947) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4029954 : List Nat := [3, 4, 1, 2, 1, 1, 1, 4, 6]
def baseStart_4029954 : Nat := 118140960795 + 4029954 * 2 ^ 59
def prefixEnd_4029954 : Nat := 4983230072969 + 3 ^ 40 * 4029954 * 2
def baseEnd_4029954 : Nat := 229922601945470113349065

theorem tailTrace_4029954 : CollatzResearch.WordTrace tailWord_4029954 prefixEnd_4029954 229922601945470113349065 := by
  unfold tailWord_4029954
  simp only [CollatzResearch.WordTrace]
  refine ⟨36746124410543098548256229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 97989665094781596128683277 36746124410543098548256229)
  ·
    refine ⟨6889898326976830977798043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 36746124410543098548256229 6889898326976830977798043)
    ·
      refine ⟨10334847490465246466697065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6889898326976830977798043 10334847490465246466697065)
      ·
        refine ⟨7751135617848934850022799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10334847490465246466697065 7751135617848934850022799)
        ·
          refine ⟨11626703426773402275034199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7751135617848934850022799 11626703426773402275034199)
          ·
            refine ⟨17440055140160103412551299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11626703426773402275034199 17440055140160103412551299)
            ·
              refine ⟨26160082710240155118826949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17440055140160103412551299 26160082710240155118826949)
              ·
                refine ⟨4905015508170029084780053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 26160082710240155118826949 4905015508170029084780053)
                ·
                  refine ⟨229922601945470113349065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4905015508170029084780053 229922601945470113349065)
                  ·
                    rfl

theorem cell23_4029954_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 1, 1, 4, 6].length) (baseStart_4029954 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4029954 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4029954 prefixEnd_4029954 := by exact prefixLift 4029954
  have htrace : WordTrace (prefixWord ++ tailWord_4029954) baseStart_4029954 baseEnd_4029954 := by
    simpa [prefixWord, tailWord_4029954, baseEnd_4029954] using wordTrace_append hprefix tailTrace_4029954
  have hstable : (prefixWord ++ tailWord_4029954).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4029954).length < 2 ^ (prefixWord ++ tailWord_4029954).sum := by decide
  have hdescent : baseEnd_4029954 < baseStart_4029954 := by decide
  rcases family_descends (prefixWord ++ tailWord_4029954) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4029957 : List Nat := [1, 3, 1, 1, 2, 2, 1, 2, 3, 5, 2]
def baseStart_4029957 : Nat := 118140960795 + 4029957 * 2 ^ 59
def prefixEnd_4029957 : Nat := 4983230072969 + 3 ^ 40 * 4029957 * 2
def baseEnd_4029957 : Nat := 2069304957951194508404071

theorem tailTrace_4029957 : CollatzResearch.WordTrace tailWord_4029957 prefixEnd_4029957 2069304957951194508404071 := by
  unfold tailWord_4029957
  simp only [CollatzResearch.WordTrace]
  refine ⟨146984607061161525705384125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97989738040774350470256083 146984607061161525705384125)
  ·
    refine ⟨55119227647935572139519047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 146984607061161525705384125 55119227647935572139519047)
    ·
      refine ⟨82678841471903358209278571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55119227647935572139519047 82678841471903358209278571)
      ·
        refine ⟨124018262207855037313917857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82678841471903358209278571 124018262207855037313917857)
        ·
          refine ⟨93013696655891277985438393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 124018262207855037313917857 93013696655891277985438393)
          ·
            refine ⟨69760272491918458489078795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 93013696655891277985438393 69760272491918458489078795)
            ·
              refine ⟨104640408737877687733618193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 69760272491918458489078795 104640408737877687733618193)
              ·
                refine ⟨78480306553408265800213645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 104640408737877687733618193 78480306553408265800213645)
                ·
                  refine ⟨29430114957528099675080117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 78480306553408265800213645 29430114957528099675080117)
                  ·
                    refine ⟨2759073277268259344538761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 29430114957528099675080117 2759073277268259344538761)
                    ·
                      refine ⟨2069304957951194508404071, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2759073277268259344538761 2069304957951194508404071)
                      ·
                        rfl

theorem cell23_4029957_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 1, 2, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 1, 2, 3, 5, 2].length) (baseStart_4029957 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4029957 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4029957 prefixEnd_4029957 := by exact prefixLift 4029957
  have htrace : WordTrace (prefixWord ++ tailWord_4029957) baseStart_4029957 baseEnd_4029957 := by
    simpa [prefixWord, tailWord_4029957, baseEnd_4029957] using wordTrace_append hprefix tailTrace_4029957
  have hstable : (prefixWord ++ tailWord_4029957).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4029957).length < 2 ^ (prefixWord ++ tailWord_4029957).sum := by decide
  have hdescent : baseEnd_4029957 < baseStart_4029957 := by decide
  rcases family_descends (prefixWord ++ tailWord_4029957) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4029982 : List Nat := [4, 3, 3, 1, 2, 1, 1, 1, 2, 1, 4]
def baseStart_4029982 : Nat := 118140960795 + 4029982 * 2 ^ 59
def prefixEnd_4029982 : Nat := 4983230072969 + 3 ^ 40 * 4029982 * 2
def baseEnd_4029982 : Nat := 2069317794967556910591457

theorem tailTrace_4029982 : CollatzResearch.WordTrace tailWord_4029982 prefixEnd_4029982 2069317794967556910591457 := by
  unfold tailWord_4029982
  simp only [CollatzResearch.WordTrace]
  refine ⟨18373189860758869371880525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 97990345924047303316696133 18373189860758869371880525)
  ·
    refine ⟨6889946197784576014455197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18373189860758869371880525 6889946197784576014455197)
    ·
      refine ⟨2583729824169216005420699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6889946197784576014455197 2583729824169216005420699)
      ·
        refine ⟨3875594736253824008131049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2583729824169216005420699 3875594736253824008131049)
        ·
          refine ⟨2906696052190368006098287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3875594736253824008131049 2906696052190368006098287)
          ·
            refine ⟨4360044078285552009147431, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2906696052190368006098287 4360044078285552009147431)
            ·
              refine ⟨6540066117428328013721147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4360044078285552009147431 6540066117428328013721147)
              ·
                refine ⟨9810099176142492020581721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6540066117428328013721147 9810099176142492020581721)
                ·
                  refine ⟨7357574382106869015436291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9810099176142492020581721 7357574382106869015436291)
                  ·
                    refine ⟨11036361573160303523154437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7357574382106869015436291 11036361573160303523154437)
                    ·
                      refine ⟨2069317794967556910591457, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11036361573160303523154437 2069317794967556910591457)
                      ·
                        rfl

theorem cell23_4029982_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 3, 1, 2, 1, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 3, 1, 2, 1, 1, 1, 2, 1, 4].length) (baseStart_4029982 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4029982 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4029982 prefixEnd_4029982 := by exact prefixLift 4029982
  have htrace : WordTrace (prefixWord ++ tailWord_4029982) baseStart_4029982 baseEnd_4029982 := by
    simpa [prefixWord, tailWord_4029982, baseEnd_4029982] using wordTrace_append hprefix tailTrace_4029982
  have hstable : (prefixWord ++ tailWord_4029982).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4029982).length < 2 ^ (prefixWord ++ tailWord_4029982).sum := by decide
  have hdescent : baseEnd_4029982 < baseStart_4029982 := by decide
  rcases family_descends (prefixWord ++ tailWord_4029982) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4029998 : List Nat := [4, 1, 3, 1, 2, 1, 1, 5, 1, 1, 3]
def baseStart_4029998 : Nat := 118140960795 + 4029998 * 2 ^ 59
def prefixEnd_4029998 : Nat := 4983230072969 + 3 ^ 40 * 4029998 * 2
def baseEnd_4029998 : Nat := 2069326010658028847991383

theorem tailTrace_4029998 : CollatzResearch.WordTrace tailWord_4029998 prefixEnd_4029998 2069326010658028847991383 := by
  unfold tailWord_4029998
  simp only [CollatzResearch.WordTrace]
  refine ⟨18373262806751623713453331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 97990734969341993138417765 18373262806751623713453331)
  ·
    refine ⟨27559894210127435570179997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18373262806751623713453331 27559894210127435570179997)
    ·
      refine ⟨10334960328797788338817499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27559894210127435570179997 10334960328797788338817499)
      ·
        refine ⟨15502440493196682508226249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10334960328797788338817499 15502440493196682508226249)
        ·
          refine ⟨11626830369897511881169687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15502440493196682508226249 11626830369897511881169687)
          ·
            refine ⟨17440245554846267821754531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11626830369897511881169687 17440245554846267821754531)
            ·
              refine ⟨26160368332269401732631797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17440245554846267821754531 26160368332269401732631797)
              ·
                refine ⟨2452534531150256412434231, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 26160368332269401732631797 2452534531150256412434231)
                ·
                  refine ⟨3678801796725384618651347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2452534531150256412434231 3678801796725384618651347)
                  ·
                    refine ⟨5518202695088076927977021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3678801796725384618651347 5518202695088076927977021)
                    ·
                      refine ⟨2069326010658028847991383, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5518202695088076927977021 2069326010658028847991383)
                      ·
                        rfl

theorem cell23_4029998_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 1, 1, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 1, 1, 5, 1, 1, 3].length) (baseStart_4029998 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4029998 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4029998 prefixEnd_4029998 := by exact prefixLift 4029998
  have htrace : WordTrace (prefixWord ++ tailWord_4029998) baseStart_4029998 baseEnd_4029998 := by
    simpa [prefixWord, tailWord_4029998, baseEnd_4029998] using wordTrace_append hprefix tailTrace_4029998
  have hstable : (prefixWord ++ tailWord_4029998).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4029998).length < 2 ^ (prefixWord ++ tailWord_4029998).sum := by decide
  have hdescent : baseEnd_4029998 < baseStart_4029998 := by decide
  rcases family_descends (prefixWord ++ tailWord_4029998) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4030000 : List Nat := [2, 1, 1, 1, 2, 3, 1, 2, 3, 1, 6]
def baseStart_4030000 : Nat := 118140960795 + 4030000 * 2 ^ 59
def prefixEnd_4030000 : Nat := 4983230072969 + 3 ^ 40 * 4030000 * 2
def baseEnd_4030000 : Nat := 2069327037619337840166373

theorem tailTrace_4030000 : CollatzResearch.WordTrace tailWord_4030000 prefixEnd_4030000 2069327037619337840166373 := by
  unfold tailWord_4030000
  simp only [CollatzResearch.WordTrace]
  refine ⟨73493087700002872024599727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97990783600003829366132969 73493087700002872024599727)
  ·
    refine ⟨110239631550004308036899591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73493087700002872024599727 110239631550004308036899591)
    ·
      refine ⟨165359447325006462055349387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110239631550004308036899591 165359447325006462055349387)
      ·
        refine ⟨248039170987509693083024081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 165359447325006462055349387 248039170987509693083024081)
        ·
          refine ⟨186029378240632269812268061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 248039170987509693083024081 186029378240632269812268061)
          ·
            refine ⟨69761016840237101179600523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 186029378240632269812268061 69761016840237101179600523)
            ·
              refine ⟨104641525260355651769400785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 69761016840237101179600523 104641525260355651769400785)
              ·
                refine ⟨78481143945266738827050589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 104641525260355651769400785 78481143945266738827050589)
                ·
                  refine ⟨29430428979475027060143971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 78481143945266738827050589 29430428979475027060143971)
                  ·
                    refine ⟨44145643469212540590215957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 29430428979475027060143971 44145643469212540590215957)
                    ·
                      refine ⟨2069327037619337840166373, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 44145643469212540590215957 2069327037619337840166373)
                      ·
                        rfl

theorem cell23_4030000_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 1, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 1, 2, 3, 1, 6].length) (baseStart_4030000 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4030000 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4030000 prefixEnd_4030000 := by exact prefixLift 4030000
  have htrace : WordTrace (prefixWord ++ tailWord_4030000) baseStart_4030000 baseEnd_4030000 := by
    simpa [prefixWord, tailWord_4030000, baseEnd_4030000] using wordTrace_append hprefix tailTrace_4030000
  have hstable : (prefixWord ++ tailWord_4030000).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4030000).length < 2 ^ (prefixWord ++ tailWord_4030000).sum := by decide
  have hdescent : baseEnd_4030000 < baseStart_4030000 := by decide
  rcases family_descends (prefixWord ++ tailWord_4030000) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4030010 : List Nat := [3, 1, 1, 1, 3, 2, 12]
def baseStart_4030010 : Nat := 118140960795 + 4030010 * 2 ^ 59
def prefixEnd_4030010 : Nat := 4983230072969 + 3 ^ 40 * 4030010 * 2
def baseEnd_4030010 : Nat := 25547310770689911123967

theorem tailTrace_4030010 : CollatzResearch.WordTrace tailWord_4030010 prefixEnd_4030010 25547310770689911123967 := by
  unfold tailWord_4030010
  simp only [CollatzResearch.WordTrace]
  refine ⟨36746635032492378939265871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 97991026753313010504708989 36746635032492378939265871)
  ·
    refine ⟨55119952548738568408898807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36746635032492378939265871 55119952548738568408898807)
    ·
      refine ⟨82679928823107852613348211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55119952548738568408898807 82679928823107852613348211)
      ·
        refine ⟨124019893234661778920022317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82679928823107852613348211 124019893234661778920022317)
        ·
          refine ⟨46507459962998167095008369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 124019893234661778920022317 46507459962998167095008369)
          ·
            refine ⟨34880594972248625321256277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46507459962998167095008369 34880594972248625321256277)
            ·
              refine ⟨25547310770689911123967, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 12 34880594972248625321256277 25547310770689911123967)
              ·
                rfl

theorem cell23_4030010_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 12].length) (baseStart_4030010 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4030010 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4030010 prefixEnd_4030010 := by exact prefixLift 4030010
  have htrace : WordTrace (prefixWord ++ tailWord_4030010) baseStart_4030010 baseEnd_4030010 := by
    simpa [prefixWord, tailWord_4030010, baseEnd_4030010] using wordTrace_append hprefix tailTrace_4030010
  have hstable : (prefixWord ++ tailWord_4030010).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4030010).length < 2 ^ (prefixWord ++ tailWord_4030010).sum := by decide
  have hdescent : baseEnd_4030010 < baseStart_4030010 := by decide
  rcases family_descends (prefixWord ++ tailWord_4030010) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4030017 : List Nat := [1, 2, 5, 1, 1, 1, 2, 2, 1, 1, 6]
def baseStart_4030017 : Nat := 118140960795 + 4030017 * 2 ^ 59
def prefixEnd_4030017 : Nat := 4983230072969 + 3 ^ 40 * 4030017 * 2
def baseEnd_4030017 : Nat := 2069335766790464273653795

theorem tailTrace_4030017 : CollatzResearch.WordTrace tailWord_4030017 prefixEnd_4030017 2069335766790464273653795 := by
  unfold tailWord_4030017
  simp only [CollatzResearch.WordTrace]
  refine ⟨146986795440944155952568305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97991196960629437301712203 146986795440944155952568305)
  ·
    refine ⟨110240096580708116964426229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 146986795440944155952568305 110240096580708116964426229)
    ·
      refine ⟨10335009054441385965414959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 110240096580708116964426229 10335009054441385965414959)
      ·
        refine ⟨15502513581662078948122439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10335009054441385965414959 15502513581662078948122439)
        ·
          refine ⟨23253770372493118422183659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15502513581662078948122439 23253770372493118422183659)
          ·
            refine ⟨34880655558739677633275489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23253770372493118422183659 34880655558739677633275489)
            ·
              refine ⟨26160491669054758224956617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34880655558739677633275489 26160491669054758224956617)
              ·
                refine ⟨19620368751791068668717463, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26160491669054758224956617 19620368751791068668717463)
                ·
                  refine ⟨29430553127686603003076195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19620368751791068668717463 29430553127686603003076195)
                  ·
                    refine ⟨44145829691529904504614293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 29430553127686603003076195 44145829691529904504614293)
                    ·
                      refine ⟨2069335766790464273653795, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 44145829691529904504614293 2069335766790464273653795)
                      ·
                        rfl

theorem cell23_4030017_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 2, 2, 1, 1, 6].length) (baseStart_4030017 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4030017 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4030017 prefixEnd_4030017 := by exact prefixLift 4030017
  have htrace : WordTrace (prefixWord ++ tailWord_4030017) baseStart_4030017 baseEnd_4030017 := by
    simpa [prefixWord, tailWord_4030017, baseEnd_4030017] using wordTrace_append hprefix tailTrace_4030017
  have hstable : (prefixWord ++ tailWord_4030017).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4030017).length < 2 ^ (prefixWord ++ tailWord_4030017).sum := by decide
  have hdescent : baseEnd_4030017 < baseStart_4030017 := by decide
  rcases family_descends (prefixWord ++ tailWord_4030017) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4030021 : List Nat := [1, 3, 1, 1, 1, 4, 4, 1, 3, 2, 2]
def baseStart_4030021 : Nat := 118140960795 + 4030021 * 2 ^ 59
def prefixEnd_4030021 : Nat := 4983230072969 + 3 ^ 40 * 4030021 * 2
def baseEnd_4030021 : Nat := 2069337820713082258003777

theorem tailTrace_4030021 : CollatzResearch.WordTrace tailWord_4030021 prefixEnd_4030021 2069337820713082258003777 := by
  unfold tailWord_4030021
  simp only [CollatzResearch.WordTrace]
  refine ⟨146986941332929664635713917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97991294221953109757142611 146986941332929664635713917)
  ·
    refine ⟨55120102999848624238392719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 146986941332929664635713917 55120102999848624238392719)
    ·
      refine ⟨82680154499772936357589079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55120102999848624238392719 82680154499772936357589079)
      ·
        refine ⟨124020231749659404536383619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82680154499772936357589079 124020231749659404536383619)
        ·
          refine ⟨186030347624489106804575429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 124020231749659404536383619 186030347624489106804575429)
          ·
            refine ⟨34880690179591707525857893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 186030347624489106804575429 34880690179591707525857893)
            ·
              refine ⟨6540129408673445161098355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 34880690179591707525857893 6540129408673445161098355)
              ·
                refine ⟨9810194113010167741647533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6540129408673445161098355 9810194113010167741647533)
                ·
                  refine ⟨3678822792378812903117825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9810194113010167741647533 3678822792378812903117825)
                  ·
                    refine ⟨2759117094284109677338369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3678822792378812903117825 2759117094284109677338369)
                    ·
                      refine ⟨2069337820713082258003777, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2759117094284109677338369 2069337820713082258003777)
                      ·
                        rfl

theorem cell23_4030021_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 4, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 4, 1, 3, 2, 2].length) (baseStart_4030021 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4030021 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4030021 prefixEnd_4030021 := by exact prefixLift 4030021
  have htrace : WordTrace (prefixWord ++ tailWord_4030021) baseStart_4030021 baseEnd_4030021 := by
    simpa [prefixWord, tailWord_4030021, baseEnd_4030021] using wordTrace_append hprefix tailTrace_4030021
  have hstable : (prefixWord ++ tailWord_4030021).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4030021).length < 2 ^ (prefixWord ++ tailWord_4030021).sum := by decide
  have hdescent : baseEnd_4030021 < baseStart_4030021 := by decide
  rcases family_descends (prefixWord ++ tailWord_4030021) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4030034 : List Nat := [3, 2, 2, 1, 2, 2, 3, 1, 1, 2, 4]
def baseStart_4030034 : Nat := 118140960795 + 4030034 * 2 ^ 59
def prefixEnd_4030034 : Nat := 4983230072969 + 3 ^ 40 * 4030034 * 2
def baseEnd_4030034 : Nat := 2069344495961590707141217

theorem tailTrace_4030034 : CollatzResearch.WordTrace tailWord_4030034 prefixEnd_4030034 2069344495961590707141217 := by
  unfold tailWord_4030034
  simp only [CollatzResearch.WordTrace]
  refine ⟨36746853870470641963984289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 97991610321255045237291437 36746853870470641963984289)
  ·
    refine ⟨27560140402852981472988217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36746853870470641963984289 27560140402852981472988217)
    ·
      refine ⟨20670105302139736104741163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27560140402852981472988217 20670105302139736104741163)
      ·
        refine ⟨31005157953209604157111745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20670105302139736104741163 31005157953209604157111745)
        ·
          refine ⟨23253868464907203117833809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31005157953209604157111745 23253868464907203117833809)
          ·
            refine ⟨17440401348680402338375357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23253868464907203117833809 17440401348680402338375357)
            ·
              refine ⟨6540150505755150876890759, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17440401348680402338375357 6540150505755150876890759)
              ·
                refine ⟨9810225758632726315336139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6540150505755150876890759 9810225758632726315336139)
                ·
                  refine ⟨14715338637949089473004209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9810225758632726315336139 14715338637949089473004209)
                  ·
                    refine ⟨11036503978461817104753157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14715338637949089473004209 11036503978461817104753157)
                    ·
                      refine ⟨2069344495961590707141217, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11036503978461817104753157 2069344495961590707141217)
                      ·
                        rfl

theorem cell23_4030034_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 2, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 2, 3, 1, 1, 2, 4].length) (baseStart_4030034 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4030034 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4030034 prefixEnd_4030034 := by exact prefixLift 4030034
  have htrace : WordTrace (prefixWord ++ tailWord_4030034) baseStart_4030034 baseEnd_4030034 := by
    simpa [prefixWord, tailWord_4030034, baseEnd_4030034] using wordTrace_append hprefix tailTrace_4030034
  have hstable : (prefixWord ++ tailWord_4030034).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4030034).length < 2 ^ (prefixWord ++ tailWord_4030034).sum := by decide
  have hdescent : baseEnd_4030034 < baseStart_4030034 := by decide
  rcases family_descends (prefixWord ++ tailWord_4030034) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4030044 : List Nat := [2, 2, 4, 1, 2, 1, 4, 7]
def baseStart_4030044 : Nat := 118140960795 + 4030044 * 2 ^ 59
def prefixEnd_4030044 : Nat := 4983230072969 + 3 ^ 40 * 4030044 * 2
def baseEnd_4030044 : Nat := 76642578917338358074673

theorem tailTrace_4030044 : CollatzResearch.WordTrace tailWord_4030044 prefixEnd_4030044 76642578917338358074673 := by
  unfold tailWord_4030044
  simp only [CollatzResearch.WordTrace]
  refine ⟨73493890105923169781900593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97991853474564226375867457 73493890105923169781900593)
  ·
    refine ⟨55120417579442377336425445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73493890105923169781900593 55120417579442377336425445)
    ·
      refine ⟨10335078296145445750579771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 55120417579442377336425445 10335078296145445750579771)
      ·
        refine ⟨15502617444218168625869657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10335078296145445750579771 15502617444218168625869657)
        ·
          refine ⟨11626963083163626469402243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15502617444218168625869657 11626963083163626469402243)
          ·
            refine ⟨17440444624745439704103365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11626963083163626469402243 17440444624745439704103365)
            ·
              refine ⟨3270083367139769944519381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17440444624745439704103365 3270083367139769944519381)
              ·
                refine ⟨76642578917338358074673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3270083367139769944519381 76642578917338358074673)
                ·
                  rfl

theorem cell23_4030044_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 1, 4, 7].length) (baseStart_4030044 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4030044 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4030044 prefixEnd_4030044 := by exact prefixLift 4030044
  have htrace : WordTrace (prefixWord ++ tailWord_4030044) baseStart_4030044 baseEnd_4030044 := by
    simpa [prefixWord, tailWord_4030044, baseEnd_4030044] using wordTrace_append hprefix tailTrace_4030044
  have hstable : (prefixWord ++ tailWord_4030044).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4030044).length < 2 ^ (prefixWord ++ tailWord_4030044).sum := by decide
  have hdescent : baseEnd_4030044 < baseStart_4030044 := by decide
  rcases family_descends (prefixWord ++ tailWord_4030044) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4030097 : List Nat := [1, 2, 2, 1, 1, 1, 1, 3, 4, 4, 3]
def baseStart_4030097 : Nat := 118140960795 + 4030097 * 2 ^ 59
def prefixEnd_4030097 : Nat := 4983230072969 + 3 ^ 40 * 4030097 * 2
def baseEnd_4030097 : Nat := 2069376845242823960653427

theorem tailTrace_4030097 : CollatzResearch.WordTrace tailWord_4030097 prefixEnd_4030097 2069376845242823960653427 := by
  unfold tailWord_4030097
  simp only [CollatzResearch.WordTrace]
  refine ⟨146989713280654329615480545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97993142187102886410320363 146989713280654329615480545)
  ·
    refine ⟨110242284960490747211610409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 146989713280654329615480545 110242284960490747211610409)
    ·
      refine ⟨82681713720368060408707807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 110242284960490747211610409 82681713720368060408707807)
      ·
        refine ⟨124022570580552090613061711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82681713720368060408707807 124022570580552090613061711)
        ·
          refine ⟨186033855870828135919592567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 124022570580552090613061711 186033855870828135919592567)
          ·
            refine ⟨279050783806242203879388851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 186033855870828135919592567 279050783806242203879388851)
            ·
              refine ⟨418576175709363305819083277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 279050783806242203879388851 418576175709363305819083277)
              ·
                refine ⟨156966065891011239682156229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 418576175709363305819083277 156966065891011239682156229)
                ·
                  refine ⟨29431137354564607440404293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 156966065891011239682156229 29431137354564607440404293)
                  ·
                    refine ⟨5518338253980863895075805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 29431137354564607440404293 5518338253980863895075805)
                    ·
                      refine ⟨2069376845242823960653427, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5518338253980863895075805 2069376845242823960653427)
                      ·
                        rfl

theorem cell23_4030097_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 4, 3].length) (baseStart_4030097 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4030097 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4030097 prefixEnd_4030097 := by exact prefixLift 4030097
  have htrace : WordTrace (prefixWord ++ tailWord_4030097) baseStart_4030097 baseEnd_4030097 := by
    simpa [prefixWord, tailWord_4030097, baseEnd_4030097] using wordTrace_append hprefix tailTrace_4030097
  have hstable : (prefixWord ++ tailWord_4030097).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4030097).length < 2 ^ (prefixWord ++ tailWord_4030097).sum := by decide
  have hdescent : baseEnd_4030097 < baseStart_4030097 := by decide
  rcases family_descends (prefixWord ++ tailWord_4030097) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4030098 : List Nat := [3, 2, 3, 1, 3, 1, 1, 1, 3, 3, 2]
def baseStart_4030098 : Nat := 118140960795 + 4030098 * 2 ^ 59
def prefixEnd_4030098 : Nat := 4983230072969 + 3 ^ 40 * 4030098 * 2
def baseEnd_4030098 : Nat := 2069377358723478456740923

theorem tailTrace_4030098 : CollatzResearch.WordTrace tailWord_4030098 prefixEnd_4030098 2069377358723478456740923 := by
  unfold tailWord_4030098
  simp only [CollatzResearch.WordTrace]
  refine ⟨36747437438412676696566737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 97993166502433804524177965 36747437438412676696566737)
  ·
    refine ⟨27560578078809507522425053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36747437438412676696566737 27560578078809507522425053)
    ·
      refine ⟨10335216779553565320909395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27560578078809507522425053 10335216779553565320909395)
      ·
        refine ⟨15502825169330347981364093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10335216779553565320909395 15502825169330347981364093)
        ·
          refine ⟨5813559438498880493011535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15502825169330347981364093 5813559438498880493011535)
          ·
            refine ⟨8720339157748320739517303, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5813559438498880493011535 8720339157748320739517303)
            ·
              refine ⟨13080508736622481109275955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8720339157748320739517303 13080508736622481109275955)
              ·
                refine ⟨19620763104933721663913933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13080508736622481109275955 19620763104933721663913933)
                ·
                  refine ⟨7357786164350145623967725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19620763104933721663913933 7357786164350145623967725)
                  ·
                    refine ⟨2759169811631304608987897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7357786164350145623967725 2759169811631304608987897)
                    ·
                      refine ⟨2069377358723478456740923, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2759169811631304608987897 2069377358723478456740923)
                      ·
                        rfl

theorem cell23_4030098_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 3, 1, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 3, 1, 1, 1, 3, 3, 2].length) (baseStart_4030098 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4030098 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4030098 prefixEnd_4030098 := by exact prefixLift 4030098
  have htrace : WordTrace (prefixWord ++ tailWord_4030098) baseStart_4030098 baseEnd_4030098 := by
    simpa [prefixWord, tailWord_4030098, baseEnd_4030098] using wordTrace_append hprefix tailTrace_4030098
  have hstable : (prefixWord ++ tailWord_4030098).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4030098).length < 2 ^ (prefixWord ++ tailWord_4030098).sum := by decide
  have hdescent : baseEnd_4030098 < baseStart_4030098 := by decide
  rcases family_descends (prefixWord ++ tailWord_4030098) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4030144 : List Nat := [2, 1, 1, 2, 4, 1, 3, 1, 2, 3, 3]
def baseStart_4030144 : Nat := 118140960795 + 4030144 * 2 ^ 59
def prefixEnd_4030144 : Nat := 4983230072969 + 3 ^ 40 * 4030144 * 2
def baseEnd_4030144 : Nat := 2069400978833585276765711

theorem tailTrace_4030144 : CollatzResearch.WordTrace tailWord_4030144 prefixEnd_4030144 2069400978833585276765711 := by
  unfold tailWord_4030144
  simp only [CollatzResearch.WordTrace]
  refine ⟨73495713755742028321220743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97994285007656037761627657 73495713755742028321220743)
  ·
    refine ⟨110243570633613042481831115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73495713755742028321220743 110243570633613042481831115)
    ·
      refine ⟨165365355950419563722746673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110243570633613042481831115 165365355950419563722746673)
      ·
        refine ⟨124024016962814672792060005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 165365355950419563722746673 124024016962814672792060005)
        ·
          refine ⟨23254503180527751148511251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 124024016962814672792060005 23254503180527751148511251)
          ·
            refine ⟨34881754770791626722766877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23254503180527751148511251 34881754770791626722766877)
            ·
              refine ⟨13080658039046860021037579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34881754770791626722766877 13080658039046860021037579)
              ·
                refine ⟨19620987058570290031556369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13080658039046860021037579 19620987058570290031556369)
                ·
                  refine ⟨14715740293927717523667277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19620987058570290031556369 14715740293927717523667277)
                  ·
                    refine ⟨5518402610222894071375229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14715740293927717523667277 5518402610222894071375229)
                    ·
                      refine ⟨2069400978833585276765711, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5518402610222894071375229 2069400978833585276765711)
                      ·
                        rfl

theorem cell23_4030144_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 3, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 3, 1, 2, 3, 3].length) (baseStart_4030144 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4030144 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4030144 prefixEnd_4030144 := by exact prefixLift 4030144
  have htrace : WordTrace (prefixWord ++ tailWord_4030144) baseStart_4030144 baseEnd_4030144 := by
    simpa [prefixWord, tailWord_4030144, baseEnd_4030144] using wordTrace_append hprefix tailTrace_4030144
  have hstable : (prefixWord ++ tailWord_4030144).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4030144).length < 2 ^ (prefixWord ++ tailWord_4030144).sum := by decide
  have hdescent : baseEnd_4030144 < baseStart_4030144 := by decide
  rcases family_descends (prefixWord ++ tailWord_4030144) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4030166 : List Nat := [5, 2, 1, 3, 2, 1, 2, 1, 1, 3, 2]
def baseStart_4030166 : Nat := 118140960795 + 4030166 * 2 ^ 59
def prefixEnd_4030166 : Nat := 4983230072969 + 3 ^ 40 * 4030166 * 2
def baseEnd_4030166 : Nat := 2069412275407984190690611

theorem tailTrace_4030166 : CollatzResearch.WordTrace tailWord_4030166 prefixEnd_4030166 2069412275407984190690611 := by
  unfold tailWord_4030166
  simp only [CollatzResearch.WordTrace]
  refine ⟨9187014369837772149983897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 97994819944936236266494901 9187014369837772149983897)
  ·
    refine ⟨6890260777378329112487923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9187014369837772149983897 6890260777378329112487923)
    ·
      refine ⟨10335391166067493668731885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6890260777378329112487923 10335391166067493668731885)
      ·
        refine ⟨3875771687275310125774457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10335391166067493668731885 3875771687275310125774457)
        ·
          refine ⟨2906828765456482594330843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3875771687275310125774457 2906828765456482594330843)
          ·
            refine ⟨4360243148184723891496265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2906828765456482594330843 4360243148184723891496265)
            ·
              refine ⟨3270182361138542918622199, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4360243148184723891496265 3270182361138542918622199)
              ·
                refine ⟨4905273541707814377933299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3270182361138542918622199 4905273541707814377933299)
                ·
                  refine ⟨7357910312561721566899949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4905273541707814377933299 7357910312561721566899949)
                  ·
                    refine ⟨2759216367210645587587481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7357910312561721566899949 2759216367210645587587481)
                    ·
                      refine ⟨2069412275407984190690611, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2759216367210645587587481 2069412275407984190690611)
                      ·
                        rfl

theorem cell23_4030166_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 3, 2, 1, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 3, 2, 1, 2, 1, 1, 3, 2].length) (baseStart_4030166 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4030166 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4030166 prefixEnd_4030166 := by exact prefixLift 4030166
  have htrace : WordTrace (prefixWord ++ tailWord_4030166) baseStart_4030166 baseEnd_4030166 := by
    simpa [prefixWord, tailWord_4030166, baseEnd_4030166] using wordTrace_append hprefix tailTrace_4030166
  have hstable : (prefixWord ++ tailWord_4030166).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4030166).length < 2 ^ (prefixWord ++ tailWord_4030166).sum := by decide
  have hdescent : baseEnd_4030166 < baseStart_4030166 := by decide
  rcases family_descends (prefixWord ++ tailWord_4030166) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4030187 : List Nat := [1, 1, 1, 1, 2, 4, 2, 1, 2, 3, 5]
def baseStart_4030187 : Nat := 118140960795 + 4030187 * 2 ^ 59
def prefixEnd_4030187 : Nat := 4983230072969 + 3 ^ 40 * 4030187 * 2
def baseEnd_4030187 : Nat := 2069423058501728608528013

theorem tailTrace_4030187 : CollatzResearch.WordTrace tailWord_4030187 prefixEnd_4030187 2069423058501728608528013 := by
  unfold tailWord_4030187
  simp only [CollatzResearch.WordTrace]
  refine ⟨146992995850328274986256815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97995330566885516657504543 146992995850328274986256815)
  ·
    refine ⟨220489493775492412479385223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146992995850328274986256815 220489493775492412479385223)
    ·
      refine ⟨330734240663238618719077835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 220489493775492412479385223 330734240663238618719077835)
      ·
        refine ⟨496101360994857928078616753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 330734240663238618719077835 496101360994857928078616753)
        ·
          refine ⟨372076020746143446058962565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 496101360994857928078616753 372076020746143446058962565)
          ·
            refine ⟨69764253889901896136055481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 372076020746143446058962565 69764253889901896136055481)
            ·
              refine ⟨52323190417426422102041611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 69764253889901896136055481 52323190417426422102041611)
              ·
                refine ⟨78484785626139633153062417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52323190417426422102041611 78484785626139633153062417)
                ·
                  refine ⟨58863589219604724864796813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 78484785626139633153062417 58863589219604724864796813)
                  ·
                    refine ⟨22073845957351771824298805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 58863589219604724864796813 22073845957351771824298805)
                    ·
                      refine ⟨2069423058501728608528013, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 22073845957351771824298805 2069423058501728608528013)
                      ·
                        rfl

theorem cell23_4030187_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 2, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 2, 1, 2, 3, 5].length) (baseStart_4030187 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4030187 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4030187 prefixEnd_4030187 := by exact prefixLift 4030187
  have htrace : WordTrace (prefixWord ++ tailWord_4030187) baseStart_4030187 baseEnd_4030187 := by
    simpa [prefixWord, tailWord_4030187, baseEnd_4030187] using wordTrace_append hprefix tailTrace_4030187
  have hstable : (prefixWord ++ tailWord_4030187).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4030187).length < 2 ^ (prefixWord ++ tailWord_4030187).sum := by decide
  have hdescent : baseEnd_4030187 < baseStart_4030187 := by decide
  rcases family_descends (prefixWord ++ tailWord_4030187) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4030204 : List Nat := [2, 2, 2, 1, 3, 1, 1, 1, 3, 4, 3]
def baseStart_4030204 : Nat := 118140960795 + 4030204 * 2 ^ 59
def prefixEnd_4030204 : Nat := 4983230072969 + 3 ^ 40 * 4030204 * 2
def baseEnd_4030204 : Nat := 2069431787672855042015435

theorem tailTrace_4030204 : CollatzResearch.WordTrace tailWord_4030204 prefixEnd_4030204 2069431787672855042015435 := by
  unfold tailWord_4030204
  simp only [CollatzResearch.WordTrace]
  refine ⟨73496807945633343444812833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 97995743927511124593083777 73496807945633343444812833)
  ·
    refine ⟨55122605959225007583609625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73496807945633343444812833 55122605959225007583609625)
    ·
      refine ⟨41341954469418755687707219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55122605959225007583609625 41341954469418755687707219)
      ·
        refine ⟨62012931704128133531560829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41341954469418755687707219 62012931704128133531560829)
        ·
          refine ⟨23254849389048050074335311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 62012931704128133531560829 23254849389048050074335311)
          ·
            refine ⟨34882274083572075111502967, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23254849389048050074335311 34882274083572075111502967)
            ·
              refine ⟨52323411125358112667254451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34882274083572075111502967 52323411125358112667254451)
              ·
                refine ⟨78485116688037169000881677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52323411125358112667254451 78485116688037169000881677)
                ·
                  refine ⟨29431918758013938375330629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 78485116688037169000881677 29431918758013938375330629)
                  ·
                    refine ⟨5518484767127613445374493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 29431918758013938375330629 5518484767127613445374493)
                    ·
                      refine ⟨2069431787672855042015435, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5518484767127613445374493 2069431787672855042015435)
                      ·
                        rfl

theorem cell23_4030204_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 1, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 1, 1, 3, 4, 3].length) (baseStart_4030204 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4030204 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4030204 prefixEnd_4030204 := by exact prefixLift 4030204
  have htrace : WordTrace (prefixWord ++ tailWord_4030204) baseStart_4030204 baseEnd_4030204 := by
    simpa [prefixWord, tailWord_4030204, baseEnd_4030204] using wordTrace_append hprefix tailTrace_4030204
  have hstable : (prefixWord ++ tailWord_4030204).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4030204).length < 2 ^ (prefixWord ++ tailWord_4030204).sum := by decide
  have hdescent : baseEnd_4030204 < baseStart_4030204 := by decide
  rcases family_descends (prefixWord ++ tailWord_4030204) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4030227 : List Nat := [1, 1, 1, 2, 1, 3, 2, 2, 1, 1, 8]
def baseStart_4030227 : Nat := 118140960795 + 4030227 * 2 ^ 59
def prefixEnd_4030227 : Nat := 4983230072969 + 3 ^ 40 * 4030227 * 2
def baseEnd_4030227 : Nat := 2069443597727908452027829

theorem tailTrace_4030227 : CollatzResearch.WordTrace tailWord_4030227 prefixEnd_4030227 2069443597727908452027829 := by
  unfold tailWord_4030227
  simp only [CollatzResearch.WordTrace]
  refine ⟨146994454770183361817712935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97996303180122241211808623 146994454770183361817712935)
  ·
    refine ⟨220491682155275042726569403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146994454770183361817712935 220491682155275042726569403)
    ·
      refine ⟨330737523232912564089854105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 220491682155275042726569403 330737523232912564089854105)
      ·
        refine ⟨248053142424684423067390579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 330737523232912564089854105 248053142424684423067390579)
        ·
          refine ⟨372079713637026634601085869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 248053142424684423067390579 372079713637026634601085869)
          ·
            refine ⟨139529892613884987975407201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 372079713637026634601085869 139529892613884987975407201)
            ·
              refine ⟨104647419460413740981555401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 139529892613884987975407201 104647419460413740981555401)
              ·
                refine ⟨78485564595310305736166551, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 104647419460413740981555401 78485564595310305736166551)
                ·
                  refine ⟨117728346892965458604249827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 78485564595310305736166551 117728346892965458604249827)
                  ·
                    refine ⟨176592520339448187906374741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 117728346892965458604249827 176592520339448187906374741)
                    ·
                      refine ⟨2069443597727908452027829, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 176592520339448187906374741 2069443597727908452027829)
                      ·
                        rfl

theorem cell23_4030227_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 2, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 2, 2, 1, 1, 8].length) (baseStart_4030227 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4030227 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4030227 prefixEnd_4030227 := by exact prefixLift 4030227
  have htrace : WordTrace (prefixWord ++ tailWord_4030227) baseStart_4030227 baseEnd_4030227 := by
    simpa [prefixWord, tailWord_4030227, baseEnd_4030227] using wordTrace_append hprefix tailTrace_4030227
  have hstable : (prefixWord ++ tailWord_4030227).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4030227).length < 2 ^ (prefixWord ++ tailWord_4030227).sum := by decide
  have hdescent : baseEnd_4030227 < baseStart_4030227 := by decide
  rcases family_descends (prefixWord ++ tailWord_4030227) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4030245 : List Nat := [1, 3, 1, 2, 3, 3, 3, 2, 1, 4]
def baseStart_4030245 : Nat := 118140960795 + 4030245 * 2 ^ 59
def prefixEnd_4030245 : Nat := 4983230072969 + 3 ^ 40 * 4030245 * 2
def baseEnd_4030245 : Nat := 689817613459896460534249

theorem tailTrace_4030245 : CollatzResearch.WordTrace tailWord_4030245 prefixEnd_4030245 689817613459896460534249 := by
  unfold tailWord_4030245
  simp only [CollatzResearch.WordTrace]
  refine ⟨146995111284118150891868189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97996740856078767261245459 146995111284118150891868189)
  ·
    refine ⟨55123166731544306584450571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 146995111284118150891868189 55123166731544306584450571)
    ·
      refine ⟨82684750097316459876675857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55123166731544306584450571 82684750097316459876675857)
      ·
        refine ⟨62013562572987344907506893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 82684750097316459876675857 62013562572987344907506893)
        ·
          refine ⟨23255085964870254340315085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 62013562572987344907506893 23255085964870254340315085)
          ·
            refine ⟨8720657236826345377618157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23255085964870254340315085 8720657236826345377618157)
            ·
              refine ⟨3270246463809879516606809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8720657236826345377618157 3270246463809879516606809)
              ·
                refine ⟨2452684847857409637455107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3270246463809879516606809 2452684847857409637455107)
                ·
                  refine ⟨3679027271786114456182661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2452684847857409637455107 3679027271786114456182661)
                  ·
                    refine ⟨689817613459896460534249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3679027271786114456182661 689817613459896460534249)
                    ·
                      rfl

theorem cell23_4030245_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 3, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 3, 3, 2, 1, 4].length) (baseStart_4030245 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4030245 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4030245 prefixEnd_4030245 := by exact prefixLift 4030245
  have htrace : WordTrace (prefixWord ++ tailWord_4030245) baseStart_4030245 baseEnd_4030245 := by
    simpa [prefixWord, tailWord_4030245, baseEnd_4030245] using wordTrace_append hprefix tailTrace_4030245
  have hstable : (prefixWord ++ tailWord_4030245).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4030245).length < 2 ^ (prefixWord ++ tailWord_4030245).sum := by decide
  have hdescent : baseEnd_4030245 < baseStart_4030245 := by decide
  rcases family_descends (prefixWord ++ tailWord_4030245) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4030258 : List Nat := [3, 2, 1, 1, 3, 4, 2, 1, 6]
def baseStart_4030258 : Nat := 118140960795 + 4030258 * 2 ^ 59
def prefixEnd_4030258 : Nat := 4983230072969 + 3 ^ 40 * 4030258 * 2
def baseEnd_4030258 : Nat := 229939946180910870082243

theorem tailTrace_4030258 : CollatzResearch.WordTrace tailWord_4030258 prefixEnd_4030258 229939946180910870082243 := by
  unfold tailWord_4030258
  simp only [CollatzResearch.WordTrace]
  refine ⟨36748896358267763528022857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 97997056955380702741394285 36748896358267763528022857)
  ·
    refine ⟨27561672268700822646017143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36748896358267763528022857 27561672268700822646017143)
    ·
      refine ⟨41342508403051233969025715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27561672268700822646017143 41342508403051233969025715)
      ·
        refine ⟨62013762604576850953538573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41342508403051233969025715 62013762604576850953538573)
        ·
          refine ⟨23255160976716319107576965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 62013762604576850953538573 23255160976716319107576965)
          ·
            refine ⟨4360342683134309832670681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 23255160976716319107576965 4360342683134309832670681)
            ·
              refine ⟨3270257012350732374503011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4360342683134309832670681 3270257012350732374503011)
              ·
                refine ⟨4905385518526098561754517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3270257012350732374503011 4905385518526098561754517)
                ·
                  refine ⟨229939946180910870082243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4905385518526098561754517 229939946180910870082243)
                  ·
                    rfl

theorem cell23_4030258_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 4, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 4, 2, 1, 6].length) (baseStart_4030258 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4030258 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4030258 prefixEnd_4030258 := by exact prefixLift 4030258
  have htrace : WordTrace (prefixWord ++ tailWord_4030258) baseStart_4030258 baseEnd_4030258 := by
    simpa [prefixWord, tailWord_4030258, baseEnd_4030258] using wordTrace_append hprefix tailTrace_4030258
  have hstable : (prefixWord ++ tailWord_4030258).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4030258).length < 2 ^ (prefixWord ++ tailWord_4030258).sum := by decide
  have hdescent : baseEnd_4030258 < baseStart_4030258 := by decide
  rcases family_descends (prefixWord ++ tailWord_4030258) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4030271 : List Nat := [1, 1, 2, 2, 6, 1, 1, 1, 3, 5]
def baseStart_4030271 : Nat := 118140960795 + 4030271 * 2 ^ 59
def prefixEnd_4030271 : Nat := 4983230072969 + 3 ^ 40 * 4030271 * 2
def baseEnd_4030271 : Nat := 689822063625568759959209

theorem tailTrace_4030271 : CollatzResearch.WordTrace tailWord_4030271 prefixEnd_4030271 689822063625568759959209 := by
  unfold tailWord_4030271
  simp only [CollatzResearch.WordTrace]
  refine ⟨146996059582023957332314667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97997373054682638221543111 146996059582023957332314667)
  ·
    refine ⟨220494089373035935998472001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146996059582023957332314667 220494089373035935998472001)
    ·
      refine ⟨165370567029776951998854001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 220494089373035935998472001 165370567029776951998854001)
      ·
        refine ⟨124027925272332713999140501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 165370567029776951998854001 124027925272332713999140501)
        ·
          refine ⟨5813808997140595968709711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 124027925272332713999140501 5813808997140595968709711)
          ·
            refine ⟨8720713495710893953064567, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5813808997140595968709711 8720713495710893953064567)
            ·
              refine ⟨13081070243566340929596851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8720713495710893953064567 13081070243566340929596851)
              ·
                refine ⟨19621605365349511394395277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13081070243566340929596851 19621605365349511394395277)
                ·
                  refine ⟨7358102012006066772898229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19621605365349511394395277 7358102012006066772898229)
                  ·
                    refine ⟨689822063625568759959209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7358102012006066772898229 689822063625568759959209)
                    ·
                      rfl

theorem cell23_4030271_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 6, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 6, 1, 1, 1, 3, 5].length) (baseStart_4030271 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4030271 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4030271 prefixEnd_4030271 := by exact prefixLift 4030271
  have htrace : WordTrace (prefixWord ++ tailWord_4030271) baseStart_4030271 baseEnd_4030271 := by
    simpa [prefixWord, tailWord_4030271, baseEnd_4030271] using wordTrace_append hprefix tailTrace_4030271
  have hstable : (prefixWord ++ tailWord_4030271).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4030271).length < 2 ^ (prefixWord ++ tailWord_4030271).sum := by decide
  have hdescent : baseEnd_4030271 < baseStart_4030271 := by decide
  rcases family_descends (prefixWord ++ tailWord_4030271) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4030311 : List Nat := [1, 1, 5, 1, 2, 1, 1, 1, 5, 2, 3]
def baseStart_4030311 : Nat := 118140960795 + 4030311 * 2 ^ 59
def prefixEnd_4030311 : Nat := 4983230072969 + 3 ^ 40 * 4030311 * 2
def baseEnd_4030311 : Nat := 2069486730102886123377443

theorem tailTrace_4030311 : CollatzResearch.WordTrace tailWord_4030311 prefixEnd_4030311 2069486730102886123377443 := by
  unfold tailWord_4030311
  simp only [CollatzResearch.WordTrace]
  refine ⟨146997518501879044163770787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97998345667919362775847191 146997518501879044163770787)
  ·
    refine ⟨220496277752818566245656181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146997518501879044163770787 220496277752818566245656181)
    ·
      refine ⟨20671526039326740585530267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 220496277752818566245656181 20671526039326740585530267)
      ·
        refine ⟨31007289058990110878295401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20671526039326740585530267 31007289058990110878295401)
        ·
          refine ⟨23255466794242583158721551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31007289058990110878295401 23255466794242583158721551)
          ·
            refine ⟨34883200191363874738082327, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23255466794242583158721551 34883200191363874738082327)
            ·
              refine ⟨52324800287045812107123491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34883200191363874738082327 52324800287045812107123491)
              ·
                refine ⟨78487200430568718160685237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52324800287045812107123491 78487200430568718160685237)
                ·
                  refine ⟨7358175040365817327564241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 78487200430568718160685237 7358175040365817327564241)
                  ·
                    refine ⟨5518631280274362995673181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7358175040365817327564241 5518631280274362995673181)
                    ·
                      refine ⟨2069486730102886123377443, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5518631280274362995673181 2069486730102886123377443)
                      ·
                        rfl

theorem cell23_4030311_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 1, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 1, 1, 5, 2, 3].length) (baseStart_4030311 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4030311 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4030311 prefixEnd_4030311 := by exact prefixLift 4030311
  have htrace : WordTrace (prefixWord ++ tailWord_4030311) baseStart_4030311 baseEnd_4030311 := by
    simpa [prefixWord, tailWord_4030311, baseEnd_4030311] using wordTrace_append hprefix tailTrace_4030311
  have hstable : (prefixWord ++ tailWord_4030311).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4030311).length < 2 ^ (prefixWord ++ tailWord_4030311).sum := by decide
  have hdescent : baseEnd_4030311 < baseStart_4030311 := by decide
  rcases family_descends (prefixWord ++ tailWord_4030311) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4030318 : List Nat := [4, 1, 2, 3, 1, 2, 2, 1, 1, 6]
def baseStart_4030318 : Nat := 118140960795 + 4030318 * 2 ^ 59
def prefixEnd_4030318 : Nat := 4983230072969 + 3 ^ 40 * 4030318 * 2
def baseEnd_4030318 : Nat := 689830108155822531996637

theorem tailTrace_4030318 : CollatzResearch.WordTrace tailWord_4030318 prefixEnd_4030318 689830108155822531996637 := by
  unfold tailWord_4030318
  simp only [CollatzResearch.WordTrace]
  refine ⟨18374721726606710544909451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 97998515875235789572850405 18374721726606710544909451)
  ·
    refine ⟨27562082589910065817364177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18374721726606710544909451 27562082589910065817364177)
    ·
      refine ⟨20671561942432549363023133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27562082589910065817364177 20671561942432549363023133)
      ·
        refine ⟨7751835728412206011133675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20671561942432549363023133 7751835728412206011133675)
        ·
          refine ⟨11627753592618309016700513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7751835728412206011133675 11627753592618309016700513)
          ·
            refine ⟨8720815194463731762525385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11627753592618309016700513 8720815194463731762525385)
            ·
              refine ⟨6540611395847798821894039, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8720815194463731762525385 6540611395847798821894039)
              ·
                refine ⟨9810917093771698232841059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6540611395847798821894039 9810917093771698232841059)
                ·
                  refine ⟨14716375640657547349261589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9810917093771698232841059 14716375640657547349261589)
                  ·
                    refine ⟨689830108155822531996637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 14716375640657547349261589 689830108155822531996637)
                    ·
                      rfl

theorem cell23_4030318_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 2, 2, 1, 1, 6].length) (baseStart_4030318 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4030318 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4030318 prefixEnd_4030318 := by exact prefixLift 4030318
  have htrace : WordTrace (prefixWord ++ tailWord_4030318) baseStart_4030318 baseEnd_4030318 := by
    simpa [prefixWord, tailWord_4030318, baseEnd_4030318] using wordTrace_append hprefix tailTrace_4030318
  have hstable : (prefixWord ++ tailWord_4030318).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4030318).length < 2 ^ (prefixWord ++ tailWord_4030318).sum := by decide
  have hdescent : baseEnd_4030318 < baseStart_4030318 := by decide
  rcases family_descends (prefixWord ++ tailWord_4030318) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4030321 : List Nat := [1, 2, 2, 2, 1, 3, 4, 1, 1, 2, 4]
def baseStart_4030321 : Nat := 118140960795 + 4030321 * 2 ^ 59
def prefixEnd_4030321 : Nat := 4983230072969 + 3 ^ 40 * 4030321 * 2
def baseEnd_4030321 : Nat := 2069491864909431084252397

theorem tailTrace_4030321 : CollatzResearch.WordTrace tailWord_4030321 prefixEnd_4030321 2069491864909431084252397 := by
  unfold tailWord_4030321
  simp only [CollatzResearch.WordTrace]
  refine ⟨146997883231842815871634817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97998588821228543914423211 146997883231842815871634817)
  ·
    refine ⟨110248412423882111903726113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 146997883231842815871634817 110248412423882111903726113)
    ·
      refine ⟨82686309317911583927794585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 110248412423882111903726113 82686309317911583927794585)
      ·
        refine ⟨62014731988433687945845939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 82686309317911583927794585 62014731988433687945845939)
        ·
          refine ⟨93022097982650531918768909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62014731988433687945845939 93022097982650531918768909)
          ·
            refine ⟨34883286743493949469538341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 93022097982650531918768909 34883286743493949469538341)
            ·
              refine ⟨6540616264405115525538439, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 34883286743493949469538341 6540616264405115525538439)
              ·
                refine ⟨9810924396607673288307659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6540616264405115525538439 9810924396607673288307659)
                ·
                  refine ⟨14716386594911509932461489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9810924396607673288307659 14716386594911509932461489)
                  ·
                    refine ⟨11037289946183632449346117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14716386594911509932461489 11037289946183632449346117)
                    ·
                      refine ⟨2069491864909431084252397, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11037289946183632449346117 2069491864909431084252397)
                      ·
                        rfl

theorem cell23_4030321_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 4, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 4, 1, 1, 2, 4].length) (baseStart_4030321 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4030321 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4030321 prefixEnd_4030321 := by exact prefixLift 4030321
  have htrace : WordTrace (prefixWord ++ tailWord_4030321) baseStart_4030321 baseEnd_4030321 := by
    simpa [prefixWord, tailWord_4030321, baseEnd_4030321] using wordTrace_append hprefix tailTrace_4030321
  have hstable : (prefixWord ++ tailWord_4030321).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4030321).length < 2 ^ (prefixWord ++ tailWord_4030321).sum := by decide
  have hdescent : baseEnd_4030321 < baseStart_4030321 := by decide
  rcases family_descends (prefixWord ++ tailWord_4030321) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4030325 : List Nat := [1, 3, 4, 1, 1, 1, 3, 2, 3, 2, 2]
def baseStart_4030325 : Nat := 118140960795 + 4030325 * 2 ^ 59
def prefixEnd_4030325 : Nat := 4983230072969 + 3 ^ 40 * 4030325 * 2
def baseEnd_4030325 : Nat := 2069493918832049068602379

theorem tailTrace_4030325 : CollatzResearch.WordTrace tailWord_4030325 prefixEnd_4030325 2069493918832049068602379 := by
  unfold tailWord_4030325
  simp only [CollatzResearch.WordTrace]
  refine ⟨146998029123828324554780429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97998686082552216369853619 146998029123828324554780429)
  ·
    refine ⟨55124260921435621708042661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 146998029123828324554780429 55124260921435621708042661)
    ·
      refine ⟨10335798922769179070257999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 55124260921435621708042661 10335798922769179070257999)
      ·
        refine ⟨15503698384153768605386999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10335798922769179070257999 15503698384153768605386999)
        ·
          refine ⟨23255547576230652908080499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15503698384153768605386999 23255547576230652908080499)
          ·
            refine ⟨34883321364345979362120749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23255547576230652908080499 34883321364345979362120749)
            ·
              refine ⟨13081245511629742260795281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34883321364345979362120749 13081245511629742260795281)
              ·
                refine ⟨9810934133722306695596461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13081245511629742260795281 9810934133722306695596461)
                ·
                  refine ⟨3679100300145865010848673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9810934133722306695596461 3679100300145865010848673)
                  ·
                    refine ⟨2759325225109398758136505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3679100300145865010848673 2759325225109398758136505)
                    ·
                      refine ⟨2069493918832049068602379, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2759325225109398758136505 2069493918832049068602379)
                      ·
                        rfl

theorem cell23_4030325_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 3, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 3, 2, 3, 2, 2].length) (baseStart_4030325 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4030325 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4030325 prefixEnd_4030325 := by exact prefixLift 4030325
  have htrace : WordTrace (prefixWord ++ tailWord_4030325) baseStart_4030325 baseEnd_4030325 := by
    simpa [prefixWord, tailWord_4030325, baseEnd_4030325] using wordTrace_append hprefix tailTrace_4030325
  have hstable : (prefixWord ++ tailWord_4030325).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4030325).length < 2 ^ (prefixWord ++ tailWord_4030325).sum := by decide
  have hdescent : baseEnd_4030325 < baseStart_4030325 := by decide
  rcases family_descends (prefixWord ++ tailWord_4030325) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4030341 : List Nat := [1, 3, 1, 1, 3, 2, 1, 4, 1, 3, 3]
def baseStart_4030341 : Nat := 118140960795 + 4030341 * 2 ^ 59
def prefixEnd_4030341 : Nat := 4983230072969 + 3 ^ 40 * 4030341 * 2
def baseEnd_4030341 : Nat := 2069502134522521006002305

theorem tailTrace_4030341 : CollatzResearch.WordTrace tailWord_4030341 prefixEnd_4030341 2069502134522521006002305 := by
  unfold tailWord_4030341
  simp only [CollatzResearch.WordTrace]
  refine ⟨146998612691770359287362877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97999075127846906191575251 146998612691770359287362877)
  ·
    refine ⟨55124479759413884732761079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 146998612691770359287362877 55124479759413884732761079)
    ·
      refine ⟨82686719639120827099141619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55124479759413884732761079 82686719639120827099141619)
      ·
        refine ⟨124030079458681240648712429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82686719639120827099141619 124030079458681240648712429)
        ·
          refine ⟨46511279797005465243267161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 124030079458681240648712429 46511279797005465243267161)
          ·
            refine ⟨34883459847754098932450371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46511279797005465243267161 34883459847754098932450371)
            ·
              refine ⟨52325189771631148398675557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34883459847754098932450371 52325189771631148398675557)
              ·
                refine ⟨9810973082180840324751667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 52325189771631148398675557 9810973082180840324751667)
                ·
                  refine ⟨14716459623271260487127501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9810973082180840324751667 14716459623271260487127501)
                  ·
                    refine ⟨5518672358726722682672813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14716459623271260487127501 5518672358726722682672813)
                    ·
                      refine ⟨2069502134522521006002305, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5518672358726722682672813 2069502134522521006002305)
                      ·
                        rfl

theorem cell23_4030341_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 1, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 1, 4, 1, 3, 3].length) (baseStart_4030341 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4030341 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4030341 prefixEnd_4030341 := by exact prefixLift 4030341
  have htrace : WordTrace (prefixWord ++ tailWord_4030341) baseStart_4030341 baseEnd_4030341 := by
    simpa [prefixWord, tailWord_4030341, baseEnd_4030341] using wordTrace_append hprefix tailTrace_4030341
  have hstable : (prefixWord ++ tailWord_4030341).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4030341).length < 2 ^ (prefixWord ++ tailWord_4030341).sum := by decide
  have hdescent : baseEnd_4030341 < baseStart_4030341 := by decide
  rcases family_descends (prefixWord ++ tailWord_4030341) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4030375 : List Nat := [1, 1, 6, 1, 2, 3, 1, 1, 1, 3, 3]
def baseStart_4030375 : Nat := 118140960795 + 4030375 * 2 ^ 59
def prefixEnd_4030375 : Nat := 4983230072969 + 3 ^ 40 * 4030375 * 2
def baseEnd_4030375 : Nat := 2069519592864773872977149

theorem tailTrace_4030375 : CollatzResearch.WordTrace tailWord_4030375 prefixEnd_4030375 2069519592864773872977149 := by
  unfold tailWord_4030375
  simp only [CollatzResearch.WordTrace]
  refine ⟨146999852773647183094100579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 97999901849098122062733719 146999852773647183094100579)
  ·
    refine ⟨220499779160470774641150869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146999852773647183094100579 220499779160470774641150869)
    ·
      refine ⟨10335927148147067561303947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 220499779160470774641150869 10335927148147067561303947)
      ·
        refine ⟨15503890722220601341955921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10335927148147067561303947 15503890722220601341955921)
        ·
          refine ⟨11627918041665451006466941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15503890722220601341955921 11627918041665451006466941)
          ·
            refine ⟨4360469265624544127425103, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11627918041665451006466941 4360469265624544127425103)
            ·
              refine ⟨6540703898436816191137655, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4360469265624544127425103 6540703898436816191137655)
              ·
                refine ⟨9811055847655224286706483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6540703898436816191137655 9811055847655224286706483)
                ·
                  refine ⟨14716583771482836430059725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9811055847655224286706483 14716583771482836430059725)
                  ·
                    refine ⟨5518718914306063661272397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14716583771482836430059725 5518718914306063661272397)
                    ·
                      refine ⟨2069519592864773872977149, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5518718914306063661272397 2069519592864773872977149)
                      ·
                        rfl

theorem cell23_4030375_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 3, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 3, 1, 1, 1, 3, 3].length) (baseStart_4030375 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4030375 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4030375 prefixEnd_4030375 := by exact prefixLift 4030375
  have htrace : WordTrace (prefixWord ++ tailWord_4030375) baseStart_4030375 baseEnd_4030375 := by
    simpa [prefixWord, tailWord_4030375, baseEnd_4030375] using wordTrace_append hprefix tailTrace_4030375
  have hstable : (prefixWord ++ tailWord_4030375).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4030375).length < 2 ^ (prefixWord ++ tailWord_4030375).sum := by decide
  have hdescent : baseEnd_4030375 < baseStart_4030375 := by decide
  rcases family_descends (prefixWord ++ tailWord_4030375) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4030384 : List Nat := [2, 1, 1, 1, 2, 1, 1, 1, 5, 3, 5]
def baseStart_4030384 : Nat := 118140960795 + 4030384 * 2 ^ 59
def prefixEnd_4030384 : Nat := 4983230072969 + 3 ^ 40 * 4030384 * 2
def baseEnd_4030384 : Nat := 2069524214190664337764607

theorem tailTrace_4030384 : CollatzResearch.WordTrace tailWord_4030384 prefixEnd_4030384 2069524214190664337764607 := by
  unfold tailWord_4030384
  simp only [CollatzResearch.WordTrace]
  refine ⟨73500090515307288815589103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98000120687076385087452137 73500090515307288815589103)
  ·
    refine ⟨110250135772960933223383655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73500090515307288815589103 110250135772960933223383655)
    ·
      refine ⟨165375203659441399835075483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110250135772960933223383655 165375203659441399835075483)
      ·
        refine ⟨248062805489162099752613225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 165375203659441399835075483 248062805489162099752613225)
        ·
          refine ⟨186047104116871574814459919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 248062805489162099752613225 186047104116871574814459919)
          ·
            refine ⟨279070656175307362221689879, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 186047104116871574814459919 279070656175307362221689879)
            ·
              refine ⟨418605984262961043332534819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 279070656175307362221689879 418605984262961043332534819)
              ·
                refine ⟨627908976394441564998802229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 418605984262961043332534819 627908976394441564998802229)
                ·
                  refine ⟨58866466536978896718637709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 627908976394441564998802229 58866466536978896718637709)
                  ·
                    refine ⟨22074924951367086269489141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 58866466536978896718637709 22074924951367086269489141)
                    ·
                      refine ⟨2069524214190664337764607, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 22074924951367086269489141 2069524214190664337764607)
                      ·
                        rfl

theorem cell23_4030384_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 1, 5, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 1, 5, 3, 5].length) (baseStart_4030384 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4030384 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4030384 prefixEnd_4030384 := by exact prefixLift 4030384
  have htrace : WordTrace (prefixWord ++ tailWord_4030384) baseStart_4030384 baseEnd_4030384 := by
    simpa [prefixWord, tailWord_4030384, baseEnd_4030384] using wordTrace_append hprefix tailTrace_4030384
  have hstable : (prefixWord ++ tailWord_4030384).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4030384).length < 2 ^ (prefixWord ++ tailWord_4030384).sum := by decide
  have hdescent : baseEnd_4030384 < baseStart_4030384 := by decide
  rcases family_descends (prefixWord ++ tailWord_4030384) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4030385 : List Nat := [1, 2, 2, 4, 2, 1, 1, 4, 1, 3, 2]
def baseStart_4030385 : Nat := 118140960795 + 4030385 * 2 ^ 59
def prefixEnd_4030385 : Nat := 4983230072969 + 3 ^ 40 * 4030385 * 2
def baseEnd_4030385 : Nat := 2069524727671318833852103

theorem tailTrace_4030385 : CollatzResearch.WordTrace tailWord_4030385 prefixEnd_4030385 2069524727671318833852103 := by
  unfold tailWord_4030385
  simp only [CollatzResearch.WordTrace]
  refine ⟨147000217503610954801964609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98000145002407303201309739 147000217503610954801964609)
  ·
    refine ⟨110250163127708216101473457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 147000217503610954801964609 110250163127708216101473457)
    ·
      refine ⟨82687622345781162076105093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 110250163127708216101473457 82687622345781162076105093)
      ·
        refine ⟨15503929189833967889269705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 82687622345781162076105093 15503929189833967889269705)
        ·
          refine ⟨11627946892375475916952279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15503929189833967889269705 11627946892375475916952279)
          ·
            refine ⟨17441920338563213875428419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11627946892375475916952279 17441920338563213875428419)
            ·
              refine ⟨26162880507844820813142629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17441920338563213875428419 26162880507844820813142629)
              ·
                refine ⟨4905540095220903902464243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 26162880507844820813142629 4905540095220903902464243)
                ·
                  refine ⟨7358310142831355853696365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4905540095220903902464243 7358310142831355853696365)
                  ·
                    refine ⟨2759366303561758445136137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7358310142831355853696365 2759366303561758445136137)
                    ·
                      refine ⟨2069524727671318833852103, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2759366303561758445136137 2069524727671318833852103)
                      ·
                        rfl

theorem cell23_4030385_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 1, 1, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 1, 1, 4, 1, 3, 2].length) (baseStart_4030385 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4030385 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4030385 prefixEnd_4030385 := by exact prefixLift 4030385
  have htrace : WordTrace (prefixWord ++ tailWord_4030385) baseStart_4030385 baseEnd_4030385 := by
    simpa [prefixWord, tailWord_4030385, baseEnd_4030385] using wordTrace_append hprefix tailTrace_4030385
  have hstable : (prefixWord ++ tailWord_4030385).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4030385).length < 2 ^ (prefixWord ++ tailWord_4030385).sum := by decide
  have hdescent : baseEnd_4030385 < baseStart_4030385 := by decide
  rcases family_descends (prefixWord ++ tailWord_4030385) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4030415 : List Nat := [1, 1, 2, 1, 1, 5, 2, 4, 2, 2, 2]
def baseStart_4030415 : Nat := 118140960795 + 4030415 * 2 ^ 59
def prefixEnd_4030415 : Nat := 4983230072969 + 3 ^ 40 * 4030415 * 2
def baseEnd_4030415 : Nat := 2069540132090953716476965

theorem tailTrace_4030415 : CollatzResearch.WordTrace tailWord_4030415 prefixEnd_4030415 2069540132090953716476965 := by
  unfold tailWord_4030415
  simp only [CollatzResearch.WordTrace]
  refine ⟨147001311693502269925556699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98000874462334846617037799 147001311693502269925556699)
  ·
    refine ⟨220501967540253404888335049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147001311693502269925556699 220501967540253404888335049)
    ·
      refine ⟨165376475655190053666251287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 220501967540253404888335049 165376475655190053666251287)
      ·
        refine ⟨248064713482785080499376931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 165376475655190053666251287 248064713482785080499376931)
        ·
          refine ⟨372097070224177620749065397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 248064713482785080499376931 372097070224177620749065397)
          ·
            refine ⟨34884100333516651945224881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 372097070224177620749065397 34884100333516651945224881)
            ·
              refine ⟨26163075250137488958918661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34884100333516651945224881 26163075250137488958918661)
              ·
                refine ⟨4905576609400779179797249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 26163075250137488958918661 4905576609400779179797249)
                ·
                  refine ⟨3679182457050584384847937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4905576609400779179797249 3679182457050584384847937)
                  ·
                    refine ⟨2759386842787938288635953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3679182457050584384847937 2759386842787938288635953)
                    ·
                      refine ⟨2069540132090953716476965, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2759386842787938288635953 2069540132090953716476965)
                      ·
                        rfl

theorem cell23_4030415_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 2, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 2, 4, 2, 2, 2].length) (baseStart_4030415 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4030415 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4030415 prefixEnd_4030415 := by exact prefixLift 4030415
  have htrace : WordTrace (prefixWord ++ tailWord_4030415) baseStart_4030415 baseEnd_4030415 := by
    simpa [prefixWord, tailWord_4030415, baseEnd_4030415] using wordTrace_append hprefix tailTrace_4030415
  have hstable : (prefixWord ++ tailWord_4030415).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4030415).length < 2 ^ (prefixWord ++ tailWord_4030415).sum := by decide
  have hdescent : baseEnd_4030415 < baseStart_4030415 := by decide
  rcases family_descends (prefixWord ++ tailWord_4030415) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4030461 : List Nat := [1, 4, 1, 1, 1, 2, 3, 2, 1, 2, 5]
def baseStart_4030461 : Nat := 118140960795 + 4030461 * 2 ^ 59
def prefixEnd_4030461 : Nat := 4983230072969 + 3 ^ 40 * 4030461 * 2
def baseEnd_4030461 : Nat := 2069563752201060536501753

theorem tailTrace_4030461 : CollatzResearch.WordTrace tailWord_4030461 prefixEnd_4030461 2069563752201060536501753 := by
  unfold tailWord_4030461
  simp only [CollatzResearch.WordTrace]
  refine ⟨147002989451335619781731237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98001992967557079854487491 147002989451335619781731237)
  ·
    refine ⟨27563060522125428709074607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 147002989451335619781731237 27563060522125428709074607)
    ·
      refine ⟨41344590783188143063611911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27563060522125428709074607 41344590783188143063611911)
      ·
        refine ⟨62016886174782214595417867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41344590783188143063611911 62016886174782214595417867)
        ·
          refine ⟨93025329262173321893126801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62016886174782214595417867 93025329262173321893126801)
          ·
            refine ⟨69768996946629991419845101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 93025329262173321893126801 69768996946629991419845101)
            ·
              refine ⟨26163373854986246782441913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 69768996946629991419845101 26163373854986246782441913)
              ·
                refine ⟨19622530391239685086831435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26163373854986246782441913 19622530391239685086831435)
                ·
                  refine ⟨29433795586859527630247153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19622530391239685086831435 29433795586859527630247153)
                  ·
                    refine ⟨22075346690144645722685365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 29433795586859527630247153 22075346690144645722685365)
                    ·
                      refine ⟨2069563752201060536501753, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 22075346690144645722685365 2069563752201060536501753)
                      ·
                        rfl

theorem cell23_4030461_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 3, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 3, 2, 1, 2, 5].length) (baseStart_4030461 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4030461 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4030461 prefixEnd_4030461 := by exact prefixLift 4030461
  have htrace : WordTrace (prefixWord ++ tailWord_4030461) baseStart_4030461 baseEnd_4030461 := by
    simpa [prefixWord, tailWord_4030461, baseEnd_4030461] using wordTrace_append hprefix tailTrace_4030461
  have hstable : (prefixWord ++ tailWord_4030461).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4030461).length < 2 ^ (prefixWord ++ tailWord_4030461).sum := by decide
  have hdescent : baseEnd_4030461 < baseStart_4030461 := by decide
  rcases family_descends (prefixWord ++ tailWord_4030461) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4030508 : List Nat := [2, 2, 1, 1, 1, 2, 2, 5, 2, 2, 3]
def baseStart_4030508 : Nat := 118140960795 + 4030508 * 2 ^ 59
def prefixEnd_4030508 : Nat := 4983230072969 + 3 ^ 40 * 4030508 * 2
def baseEnd_4030508 : Nat := 2069587885791821852614037

theorem tailTrace_4030508 : CollatzResearch.WordTrace tailWord_4030508 prefixEnd_4030508 2069587885791821852614037 := by
  unfold tailWord_4030508
  simp only [CollatzResearch.WordTrace]
  refine ⟨73502351841082673404346089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98003135788110231205794785 73502351841082673404346089)
  ·
    refine ⟨55126763880812005053259567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73502351841082673404346089 55126763880812005053259567)
    ·
      refine ⟨82690145821218007579889351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55126763880812005053259567 82690145821218007579889351)
      ·
        refine ⟨124035218731827011369834027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82690145821218007579889351 124035218731827011369834027)
        ·
          refine ⟨186052828097740517054751041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 124035218731827011369834027 186052828097740517054751041)
          ·
            refine ⟨139539621073305387791063281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 186052828097740517054751041 139539621073305387791063281)
            ·
              refine ⟨104654715804979040843297461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 139539621073305387791063281 104654715804979040843297461)
              ·
                refine ⟨9811379606716785079059137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 104654715804979040843297461 9811379606716785079059137)
                ·
                  refine ⟨7358534705037588809294353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9811379606716785079059137 7358534705037588809294353)
                  ·
                    refine ⟨5518901028778191606970765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7358534705037588809294353 5518901028778191606970765)
                    ·
                      refine ⟨2069587885791821852614037, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5518901028778191606970765 2069587885791821852614037)
                      ·
                        rfl

theorem cell23_4030508_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 2, 2, 3].length) (baseStart_4030508 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4030508 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4030508 prefixEnd_4030508 := by exact prefixLift 4030508
  have htrace : WordTrace (prefixWord ++ tailWord_4030508) baseStart_4030508 baseEnd_4030508 := by
    simpa [prefixWord, tailWord_4030508, baseEnd_4030508] using wordTrace_append hprefix tailTrace_4030508
  have hstable : (prefixWord ++ tailWord_4030508).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4030508).length < 2 ^ (prefixWord ++ tailWord_4030508).sum := by decide
  have hdescent : baseEnd_4030508 < baseStart_4030508 := by decide
  rcases family_descends (prefixWord ++ tailWord_4030508) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4030515 : List Nat := [1, 1, 1, 2, 4, 1, 3, 5, 1, 4]
def baseStart_4030515 : Nat := 118140960795 + 4030515 * 2 ^ 59
def prefixEnd_4030515 : Nat := 4983230072969 + 3 ^ 40 * 4030515 * 2
def baseEnd_4030515 : Nat := 689863826718801108408835

theorem tailTrace_4030515 : CollatzResearch.WordTrace tailWord_4030515 prefixEnd_4030515 689863826718801108408835 := by
  unfold tailWord_4030515
  simp only [CollatzResearch.WordTrace]
  refine ⟨147004958993139987004196999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98003305995426658002797999 147004958993139987004196999)
  ·
    refine ⟨220507438489709980506295499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147004958993139987004196999 220507438489709980506295499)
    ·
      refine ⟨330761157734564970759443249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 220507438489709980506295499 330761157734564970759443249)
      ·
        refine ⟨248070868300923728069582437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 330761157734564970759443249 248070868300923728069582437)
        ·
          refine ⟨46513287806423199013046707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 248070868300923728069582437 46513287806423199013046707)
          ·
            refine ⟨69769931709634798519570061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46513287806423199013046707 69769931709634798519570061)
            ·
              refine ⟨26163724391113049444838773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 69769931709634798519570061 26163724391113049444838773)
              ·
                refine ⟨2452849161666848385453635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 26163724391113049444838773 2452849161666848385453635)
                ·
                  refine ⟨3679273742500272578180453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2452849161666848385453635 3679273742500272578180453)
                  ·
                    refine ⟨689863826718801108408835, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3679273742500272578180453 689863826718801108408835)
                    ·
                      rfl

theorem cell23_4030515_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 3, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 3, 5, 1, 4].length) (baseStart_4030515 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4030515 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4030515 prefixEnd_4030515 := by exact prefixLift 4030515
  have htrace : WordTrace (prefixWord ++ tailWord_4030515) baseStart_4030515 baseEnd_4030515 := by
    simpa [prefixWord, tailWord_4030515, baseEnd_4030515] using wordTrace_append hprefix tailTrace_4030515
  have hstable : (prefixWord ++ tailWord_4030515).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4030515).length < 2 ^ (prefixWord ++ tailWord_4030515).sum := by decide
  have hdescent : baseEnd_4030515 < baseStart_4030515 := by decide
  rcases family_descends (prefixWord ++ tailWord_4030515) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4030518 : List Nat := [5, 1, 2, 1, 1, 1, 1, 1, 1, 3, 6]
def baseStart_4030518 : Nat := 118140960795 + 4030518 * 2 ^ 59
def prefixEnd_4030518 : Nat := 4983230072969 + 3 ^ 40 * 4030518 * 2
def baseEnd_4030518 : Nat := 2069593020598366813488991

theorem tailTrace_4030518 : CollatzResearch.WordTrace tailWord_4030518 prefixEnd_4030518 2069593020598366813488991 := by
  unfold tailWord_4030518
  simp only [CollatzResearch.WordTrace]
  refine ⟨9187816775758069907284763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 98003378941419412344370805 9187816775758069907284763)
  ·
    refine ⟨13781725163637104860927145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9187816775758069907284763 13781725163637104860927145)
    ·
      refine ⟨10336293872727828645695359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13781725163637104860927145 10336293872727828645695359)
      ·
        refine ⟨15504440809091742968543039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10336293872727828645695359 15504440809091742968543039)
        ·
          refine ⟨23256661213637614452814559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15504440809091742968543039 23256661213637614452814559)
          ·
            refine ⟨34884991820456421679221839, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23256661213637614452814559 34884991820456421679221839)
            ·
              refine ⟨52327487730684632518832759, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34884991820456421679221839 52327487730684632518832759)
              ·
                refine ⟨78491231596026948778249139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52327487730684632518832759 78491231596026948778249139)
                ·
                  refine ⟨117736847394040423167373709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 78491231596026948778249139 117736847394040423167373709)
                  ·
                    refine ⟨44151317772765158687765141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 117736847394040423167373709 44151317772765158687765141)
                    ·
                      refine ⟨2069593020598366813488991, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 44151317772765158687765141 2069593020598366813488991)
                      ·
                        rfl

theorem cell23_4030518_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 1, 1, 1, 3, 6].length) (baseStart_4030518 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4030518 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4030518 prefixEnd_4030518 := by exact prefixLift 4030518
  have htrace : WordTrace (prefixWord ++ tailWord_4030518) baseStart_4030518 baseEnd_4030518 := by
    simpa [prefixWord, tailWord_4030518, baseEnd_4030518] using wordTrace_append hprefix tailTrace_4030518
  have hstable : (prefixWord ++ tailWord_4030518).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4030518).length < 2 ^ (prefixWord ++ tailWord_4030518).sum := by decide
  have hdescent : baseEnd_4030518 < baseStart_4030518 := by decide
  rcases family_descends (prefixWord ++ tailWord_4030518) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4030528 : List Nat := [2, 1, 1, 2, 2, 4, 3, 2, 6]
def baseStart_4030528 : Nat := 118140960795 + 4030528 * 2 ^ 59
def prefixEnd_4030528 : Nat := 4983230072969 + 3 ^ 40 * 4030528 * 2
def baseEnd_4030528 : Nat := 229955350600545752707105

theorem tailTrace_4030528 : CollatzResearch.WordTrace tailWord_4030528 prefixEnd_4030528 229955350600545752707105 := by
  unfold tailWord_4030528
  simp only [CollatzResearch.WordTrace]
  refine ⟨73502716571046445112210119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98003622094728593482946825 73502716571046445112210119)
  ·
    refine ⟨110254074856569667668315179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73502716571046445112210119 110254074856569667668315179)
    ·
      refine ⟨165381112284854501502472769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110254074856569667668315179 165381112284854501502472769)
      ·
        refine ⟨124035834213640876126854577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 165381112284854501502472769 124035834213640876126854577)
        ·
          refine ⟨93026875660230657095140933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 124035834213640876126854577 93026875660230657095140933)
          ·
            refine ⟨17442539186293248205338925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 93026875660230657095140933 17442539186293248205338925)
            ·
              refine ⟨6540952194859968077002097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17442539186293248205338925 6540952194859968077002097)
              ·
                refine ⟨4905714146144976057751573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6540952194859968077002097 4905714146144976057751573)
                ·
                  refine ⟨229955350600545752707105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4905714146144976057751573 229955350600545752707105)
                  ·
                    rfl

theorem cell23_4030528_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 4, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 4, 3, 2, 6].length) (baseStart_4030528 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4030528 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4030528 prefixEnd_4030528 := by exact prefixLift 4030528
  have htrace : WordTrace (prefixWord ++ tailWord_4030528) baseStart_4030528 baseEnd_4030528 := by
    simpa [prefixWord, tailWord_4030528, baseEnd_4030528] using wordTrace_append hprefix tailTrace_4030528
  have hstable : (prefixWord ++ tailWord_4030528).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4030528).length < 2 ^ (prefixWord ++ tailWord_4030528).sum := by decide
  have hdescent : baseEnd_4030528 < baseStart_4030528 := by decide
  rcases family_descends (prefixWord ++ tailWord_4030528) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4030551 : List Nat := [1, 1, 3, 2, 2, 1, 2, 1, 2, 1, 7]
def baseStart_4030551 : Nat := 118140960795 + 4030551 * 2 ^ 59
def prefixEnd_4030551 : Nat := 4983230072969 + 3 ^ 40 * 4030551 * 2
def baseEnd_4030551 : Nat := 2069609965459965184376339

theorem tailTrace_4030551 : CollatzResearch.WordTrace tailWord_4030551 prefixEnd_4030551 2069609965459965184376339 := by
  unfold tailWord_4030551
  simp only [CollatzResearch.WordTrace]
  refine ⟨147006272021009565152507507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98004181347339710101671671 147006272021009565152507507)
  ·
    refine ⟨220509408031514347728761261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147006272021009565152507507 220509408031514347728761261)
    ·
      refine ⟨82691028011817880398285473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 220509408031514347728761261 82691028011817880398285473)
      ·
        refine ⟨62018271008863410298714105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 82691028011817880398285473 62018271008863410298714105)
        ·
          refine ⟨46513703256647557724035579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62018271008863410298714105 46513703256647557724035579)
          ·
            refine ⟨69770554884971336586053369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46513703256647557724035579 69770554884971336586053369)
            ·
              refine ⟨52327916163728502439540027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 69770554884971336586053369 52327916163728502439540027)
              ·
                refine ⟨78491874245592753659310041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52327916163728502439540027 78491874245592753659310041)
                ·
                  refine ⟨58868905684194565244482531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 78491874245592753659310041 58868905684194565244482531)
                  ·
                    refine ⟨88303358526291847866723797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 58868905684194565244482531 88303358526291847866723797)
                    ·
                      refine ⟨2069609965459965184376339, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 88303358526291847866723797 2069609965459965184376339)
                      ·
                        rfl

theorem cell23_4030551_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 2, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 2, 1, 2, 1, 7].length) (baseStart_4030551 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4030551 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4030551 prefixEnd_4030551 := by exact prefixLift 4030551
  have htrace : WordTrace (prefixWord ++ tailWord_4030551) baseStart_4030551 baseEnd_4030551 := by
    simpa [prefixWord, tailWord_4030551, baseEnd_4030551] using wordTrace_append hprefix tailTrace_4030551
  have hstable : (prefixWord ++ tailWord_4030551).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4030551).length < 2 ^ (prefixWord ++ tailWord_4030551).sum := by decide
  have hdescent : baseEnd_4030551 < baseStart_4030551 := by decide
  rcases family_descends (prefixWord ++ tailWord_4030551) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4030565 : List Nat := [1, 3, 1, 3, 2, 2, 2, 1, 1, 5, 2]
def baseStart_4030565 : Nat := 118140960795 + 4030565 * 2 ^ 59
def prefixEnd_4030565 : Nat := 4983230072969 + 3 ^ 40 * 4030565 * 2
def baseEnd_4030565 : Nat := 2069617154189128129601275

theorem tailTrace_4030565 : CollatzResearch.WordTrace tailWord_4030565 prefixEnd_4030565 2069617154189128129601275 := by
  unfold tailWord_4030565
  simp only [CollatzResearch.WordTrace]
  refine ⟨147006782642958845543517149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98004521761972563695678099 147006782642958845543517149)
  ·
    refine ⟨55127543491109567078818931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 147006782642958845543517149 55127543491109567078818931)
    ·
      refine ⟨82691315236664350618228397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55127543491109567078818931 82691315236664350618228397)
      ·
        refine ⟨31009243213749131481835649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 82691315236664350618228397 31009243213749131481835649)
        ·
          refine ⟨23256932410311848611376737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31009243213749131481835649 23256932410311848611376737)
          ·
            refine ⟨17442699307733886458532553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23256932410311848611376737 17442699307733886458532553)
            ·
              refine ⟨13082024480800414843899415, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17442699307733886458532553 13082024480800414843899415)
              ·
                refine ⟨19623036721200622265849123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13082024480800414843899415 19623036721200622265849123)
                ·
                  refine ⟨29434555081800933398773685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19623036721200622265849123 29434555081800933398773685)
                  ·
                    refine ⟨2759489538918837506135033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 29434555081800933398773685 2759489538918837506135033)
                    ·
                      refine ⟨2069617154189128129601275, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2759489538918837506135033 2069617154189128129601275)
                      ·
                        rfl

theorem cell23_4030565_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 2, 2, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 2, 2, 1, 1, 5, 2].length) (baseStart_4030565 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4030565 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4030565 prefixEnd_4030565 := by exact prefixLift 4030565
  have htrace : WordTrace (prefixWord ++ tailWord_4030565) baseStart_4030565 baseEnd_4030565 := by
    simpa [prefixWord, tailWord_4030565, baseEnd_4030565] using wordTrace_append hprefix tailTrace_4030565
  have hstable : (prefixWord ++ tailWord_4030565).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4030565).length < 2 ^ (prefixWord ++ tailWord_4030565).sum := by decide
  have hdescent : baseEnd_4030565 < baseStart_4030565 := by decide
  rcases family_descends (prefixWord ++ tailWord_4030565) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4030582 : List Nat := [5, 1, 1, 2, 1, 2, 1, 1, 4, 3, 2]
def baseStart_4030582 : Nat := 118140960795 + 4030582 * 2 ^ 59
def prefixEnd_4030582 : Nat := 4983230072969 + 3 ^ 40 * 4030582 * 2
def baseEnd_4030582 : Nat := 2069625883360254563088697

theorem tailTrace_4030582 : CollatzResearch.WordTrace tailWord_4030582 prefixEnd_4030582 2069625883360254563088697 := by
  unfold tailWord_4030582
  simp only [CollatzResearch.WordTrace]
  refine ⟨9187962667743578590430375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 98004935122598171631257333 9187962667743578590430375)
  ·
    refine ⟨13781944001615367885645563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9187962667743578590430375 13781944001615367885645563)
    ·
      refine ⟨20672916002423051828468345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13781944001615367885645563 20672916002423051828468345)
      ·
        refine ⟨15504687001817288871351259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20672916002423051828468345 15504687001817288871351259)
        ·
          refine ⟨23257030502725933307026889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15504687001817288871351259 23257030502725933307026889)
          ·
            refine ⟨17442772877044449980270167, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23257030502725933307026889 17442772877044449980270167)
            ·
              refine ⟨26164159315566674970405251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17442772877044449980270167 26164159315566674970405251)
              ·
                refine ⟨39246238973350012455607877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26164159315566674970405251 39246238973350012455607877)
                ·
                  refine ⟨7358669807503127335426477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 39246238973350012455607877 7358669807503127335426477)
                  ·
                    refine ⟨2759501177813672750784929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7358669807503127335426477 2759501177813672750784929)
                    ·
                      refine ⟨2069625883360254563088697, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2759501177813672750784929 2069625883360254563088697)
                      ·
                        rfl

theorem cell23_4030582_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 2, 1, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 2, 1, 1, 4, 3, 2].length) (baseStart_4030582 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4030582 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4030582 prefixEnd_4030582 := by exact prefixLift 4030582
  have htrace : WordTrace (prefixWord ++ tailWord_4030582) baseStart_4030582 baseEnd_4030582 := by
    simpa [prefixWord, tailWord_4030582, baseEnd_4030582] using wordTrace_append hprefix tailTrace_4030582
  have hstable : (prefixWord ++ tailWord_4030582).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4030582).length < 2 ^ (prefixWord ++ tailWord_4030582).sum := by decide
  have hdescent : baseEnd_4030582 < baseStart_4030582 := by decide
  rcases family_descends (prefixWord ++ tailWord_4030582) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4030608 : List Nat := [2, 1, 1, 1, 1, 1, 6, 3, 1, 2, 4]
def baseStart_4030608 : Nat := 118140960795 + 4030608 * 2 ^ 59
def prefixEnd_4030608 : Nat := 4983230072969 + 3 ^ 40 * 4030608 * 2
def baseEnd_4030608 : Nat := 2069639233857271461363577

theorem tailTrace_4030608 : CollatzResearch.WordTrace tailWord_4030608 prefixEnd_4030608 2069639233857271461363577 := by
  unfold tailWord_4030608
  simp only [CollatzResearch.WordTrace]
  refine ⟨73504175490901531943666239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98005567321202042591554985 73504175490901531943666239)
  ·
    refine ⟨110256263236352297915499359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73504175490901531943666239 110256263236352297915499359)
    ·
      refine ⟨165384394854528446873249039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110256263236352297915499359 165384394854528446873249039)
      ·
        refine ⟨248076592281792670309873559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 165384394854528446873249039 248076592281792670309873559)
        ·
          refine ⟨372114888422689005464810339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 248076592281792670309873559 372114888422689005464810339)
          ·
            refine ⟨558172332634033508197215509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 372114888422689005464810339 558172332634033508197215509)
            ·
              refine ⟨26164328092220320696744477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 558172332634033508197215509 26164328092220320696744477)
              ·
                refine ⟨9811623034582620261279179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26164328092220320696744477 9811623034582620261279179)
                ·
                  refine ⟨14717434551873930391918769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9811623034582620261279179 14717434551873930391918769)
                  ·
                    refine ⟨11038075913905447793939077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14717434551873930391918769 11038075913905447793939077)
                    ·
                      refine ⟨2069639233857271461363577, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11038075913905447793939077 2069639233857271461363577)
                      ·
                        rfl

theorem cell23_4030608_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 6, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 6, 3, 1, 2, 4].length) (baseStart_4030608 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4030608 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4030608 prefixEnd_4030608 := by exact prefixLift 4030608
  have htrace : WordTrace (prefixWord ++ tailWord_4030608) baseStart_4030608 baseEnd_4030608 := by
    simpa [prefixWord, tailWord_4030608, baseEnd_4030608] using wordTrace_append hprefix tailTrace_4030608
  have hstable : (prefixWord ++ tailWord_4030608).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4030608).length < 2 ^ (prefixWord ++ tailWord_4030608).sum := by decide
  have hdescent : baseEnd_4030608 < baseStart_4030608 := by decide
  rcases family_descends (prefixWord ++ tailWord_4030608) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4030622 : List Nat := [4, 3, 1, 1, 3, 1, 1, 2, 1, 6]
def baseStart_4030622 : Nat := 118140960795 + 4030622 * 2 ^ 59
def prefixEnd_4030622 : Nat := 4983230072969 + 3 ^ 40 * 4030622 * 2
def baseEnd_4030622 : Nat := 689882140862144802196171

theorem tailTrace_4030622 : CollatzResearch.WordTrace tailWord_4030622 prefixEnd_4030622 689882140862144802196171 := by
  unfold tailWord_4030622
  simp only [CollatzResearch.WordTrace]
  refine ⟨18376107700469043034792765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 98005907735834896185561413 18376107700469043034792765)
  ·
    refine ⟨6891040387675891138047287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18376107700469043034792765 6891040387675891138047287)
    ·
      refine ⟨10336560581513836707070931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6891040387675891138047287 10336560581513836707070931)
      ·
        refine ⟨15504840872270755060606397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10336560581513836707070931 15504840872270755060606397)
        ·
          refine ⟨5814315327101533147727399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15504840872270755060606397 5814315327101533147727399)
          ·
            refine ⟨8721472990652299721591099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5814315327101533147727399 8721472990652299721591099)
            ·
              refine ⟨13082209485978449582386649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8721472990652299721591099 13082209485978449582386649)
              ·
                refine ⟨9811657114483837186789987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13082209485978449582386649 9811657114483837186789987)
                ·
                  refine ⟨14717485671725755780184981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9811657114483837186789987 14717485671725755780184981)
                  ·
                    refine ⟨689882140862144802196171, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 14717485671725755780184981 689882140862144802196171)
                    ·
                      rfl

theorem cell23_4030622_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 3, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 3, 1, 1, 2, 1, 6].length) (baseStart_4030622 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4030622 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4030622 prefixEnd_4030622 := by exact prefixLift 4030622
  have htrace : WordTrace (prefixWord ++ tailWord_4030622) baseStart_4030622 baseEnd_4030622 := by
    simpa [prefixWord, tailWord_4030622, baseEnd_4030622] using wordTrace_append hprefix tailTrace_4030622
  have hstable : (prefixWord ++ tailWord_4030622).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4030622).length < 2 ^ (prefixWord ++ tailWord_4030622).sum := by decide
  have hdescent : baseEnd_4030622 < baseStart_4030622 := by decide
  rcases family_descends (prefixWord ++ tailWord_4030622) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4030625 : List Nat := [1, 2, 3, 3, 1, 3, 1, 2, 1, 2, 4]
def baseStart_4030625 : Nat := 118140960795 + 4030625 * 2 ^ 59
def prefixEnd_4030625 : Nat := 4983230072969 + 3 ^ 40 * 4030625 * 2
def baseEnd_4030625 : Nat := 2069647963028397894850999

theorem tailTrace_4030625 : CollatzResearch.WordTrace tailWord_4030625 prefixEnd_4030625 2069647963028397894850999 := by
  unfold tailWord_4030625
  simp only [CollatzResearch.WordTrace]
  refine ⟨147008971022741475790701329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98005980681827650527134219 147008971022741475790701329)
  ·
    refine ⟨110256728267056106843025997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 147008971022741475790701329 110256728267056106843025997)
    ·
      refine ⟨41346273100146040066134749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 110256728267056106843025997 41346273100146040066134749)
      ·
        refine ⟨15504852412554765024800531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 41346273100146040066134749 15504852412554765024800531)
        ·
          refine ⟨23257278618832147537200797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15504852412554765024800531 23257278618832147537200797)
          ·
            refine ⟨8721479482062055326450299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23257278618832147537200797 8721479482062055326450299)
            ·
              refine ⟨13082219223093082989675449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8721479482062055326450299 13082219223093082989675449)
              ·
                refine ⟨9811664417319812242256587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13082219223093082989675449 9811664417319812242256587)
                ·
                  refine ⟨14717496625979718363384881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9811664417319812242256587 14717496625979718363384881)
                  ·
                    refine ⟨11038122469484788772538661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14717496625979718363384881 11038122469484788772538661)
                    ·
                      refine ⟨2069647963028397894850999, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11038122469484788772538661 2069647963028397894850999)
                      ·
                        rfl

theorem cell23_4030625_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 3, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 3, 1, 2, 1, 2, 4].length) (baseStart_4030625 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4030625 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4030625 prefixEnd_4030625 := by exact prefixLift 4030625
  have htrace : WordTrace (prefixWord ++ tailWord_4030625) baseStart_4030625 baseEnd_4030625 := by
    simpa [prefixWord, tailWord_4030625, baseEnd_4030625] using wordTrace_append hprefix tailTrace_4030625
  have hstable : (prefixWord ++ tailWord_4030625).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4030625).length < 2 ^ (prefixWord ++ tailWord_4030625).sum := by decide
  have hdescent : baseEnd_4030625 < baseStart_4030625 := by decide
  rcases family_descends (prefixWord ++ tailWord_4030625) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4030629 : List Nat := [1, 3, 1, 2, 1, 3, 2, 5, 1, 2, 2]
def baseStart_4030629 : Nat := 118140960795 + 4030629 * 2 ^ 59
def prefixEnd_4030629 : Nat := 4983230072969 + 3 ^ 40 * 4030629 * 2
def baseEnd_4030629 : Nat := 2069650016951015879200981

theorem tailTrace_4030629 : CollatzResearch.WordTrace tailWord_4030629 prefixEnd_4030629 2069650016951015879200981 := by
  unfold tailWord_4030629
  simp only [CollatzResearch.WordTrace]
  refine ⟨147009116914726984473846941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98006077943151322982564627 147009116914726984473846941)
  ·
    refine ⟨55128418843022619177692603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 147009116914726984473846941 55128418843022619177692603)
    ·
      refine ⟨82692628264533928766538905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55128418843022619177692603 82692628264533928766538905)
      ·
        refine ⟨62019471198400446574904179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 82692628264533928766538905 62019471198400446574904179)
        ·
          refine ⟨93029206797600669862356269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62019471198400446574904179 93029206797600669862356269)
          ·
            refine ⟨34885952549100251198383601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 93029206797600669862356269 34885952549100251198383601)
            ·
              refine ⟨26164464411825188398787701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34885952549100251198383601 26164464411825188398787701)
              ·
                refine ⟨2452918538608611412386347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 26164464411825188398787701 2452918538608611412386347)
                ·
                  refine ⟨3679377807912917118579521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2452918538608611412386347 3679377807912917118579521)
                  ·
                    refine ⟨2759533355934687838934641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3679377807912917118579521 2759533355934687838934641)
                    ·
                      refine ⟨2069650016951015879200981, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2759533355934687838934641 2069650016951015879200981)
                      ·
                        rfl

theorem cell23_4030629_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 2, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 2, 5, 1, 2, 2].length) (baseStart_4030629 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4030629 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4030629 prefixEnd_4030629 := by exact prefixLift 4030629
  have htrace : WordTrace (prefixWord ++ tailWord_4030629) baseStart_4030629 baseEnd_4030629 := by
    simpa [prefixWord, tailWord_4030629, baseEnd_4030629] using wordTrace_append hprefix tailTrace_4030629
  have hstable : (prefixWord ++ tailWord_4030629).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4030629).length < 2 ^ (prefixWord ++ tailWord_4030629).sum := by decide
  have hdescent : baseEnd_4030629 < baseStart_4030629 := by decide
  rcases family_descends (prefixWord ++ tailWord_4030629) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4030652 : List Nat := [2, 2, 2, 3, 4, 1, 1, 8]
def baseStart_4030652 : Nat := 118140960795 + 4030652 * 2 ^ 59
def prefixEnd_4030652 : Nat := 4983230072969 + 3 ^ 40 * 4030652 * 2
def baseEnd_4030652 : Nat := 76654141740965529230125

theorem tailTrace_4030652 : CollatzResearch.WordTrace tailWord_4030652 prefixEnd_4030652 76654141740965529230125 := by
  unfold tailWord_4030652
  simp only [CollatzResearch.WordTrace]
  refine ⟨73504977896821829700967105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98006637195762439601289473 73504977896821829700967105)
  ·
    refine ⟨55128733422616372275725329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73504977896821829700967105 55128733422616372275725329)
    ·
      refine ⟨41346550066962279206793997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55128733422616372275725329 41346550066962279206793997)
      ·
        refine ⟨15504956275110854702547749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 41346550066962279206793997 15504956275110854702547749)
        ·
          refine ⟨2907179301583285256727703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 15504956275110854702547749 2907179301583285256727703)
          ·
            refine ⟨4360768952374927885091555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2907179301583285256727703 4360768952374927885091555)
            ·
              refine ⟨6541153428562391827637333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4360768952374927885091555 6541153428562391827637333)
              ·
                refine ⟨76654141740965529230125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 6541153428562391827637333 76654141740965529230125)
                ·
                  rfl

theorem cell23_4030652_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 4, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 4, 1, 1, 8].length) (baseStart_4030652 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4030652 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4030652 prefixEnd_4030652 := by exact prefixLift 4030652
  have htrace : WordTrace (prefixWord ++ tailWord_4030652) baseStart_4030652 baseEnd_4030652 := by
    simpa [prefixWord, tailWord_4030652, baseEnd_4030652] using wordTrace_append hprefix tailTrace_4030652
  have hstable : (prefixWord ++ tailWord_4030652).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4030652).length < 2 ^ (prefixWord ++ tailWord_4030652).sum := by decide
  have hdescent : baseEnd_4030652 < baseStart_4030652 := by decide
  rcases family_descends (prefixWord ++ tailWord_4030652) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4030688 : List Nat := [2, 1, 1, 3, 1, 3, 2, 1, 1, 3, 5]
def baseStart_4030688 : Nat := 118140960795 + 4030688 * 2 ^ 59
def prefixEnd_4030688 : Nat := 4983230072969 + 3 ^ 40 * 4030688 * 2
def baseEnd_4030688 : Nat := 2069680312309631148363209

theorem tailTrace_4030688 : CollatzResearch.WordTrace tailWord_4030688 prefixEnd_4030688 2069680312309631148363209 := by
  unfold tailWord_4030688
  simp only [CollatzResearch.WordTrace]
  refine ⟨73505634410756618775122359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98007512547675491700163145 73505634410756618775122359)
  ·
    refine ⟨110258451616134928162683539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73505634410756618775122359 110258451616134928162683539)
    ·
      refine ⟨165387677424202392244025309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110258451616134928162683539 165387677424202392244025309)
      ·
        refine ⟨62020379034075897091509491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 165387677424202392244025309 62020379034075897091509491)
        ·
          refine ⟨93030568551113845637264237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62020379034075897091509491 93030568551113845637264237)
          ·
            refine ⟨34886463206667692113974089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 93030568551113845637264237 34886463206667692113974089)
            ·
              refine ⟨26164847405000769085480567, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34886463206667692113974089 26164847405000769085480567)
              ·
                refine ⟨39247271107501153628220851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26164847405000769085480567 39247271107501153628220851)
                ·
                  refine ⟨58870906661251730442331277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39247271107501153628220851 58870906661251730442331277)
                  ·
                    refine ⟨22076589997969398915874229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 58870906661251730442331277 22076589997969398915874229)
                    ·
                      refine ⟨2069680312309631148363209, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 22076589997969398915874229 2069680312309631148363209)
                      ·
                        rfl

theorem cell23_4030688_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 2, 1, 1, 3, 5].length) (baseStart_4030688 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4030688 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4030688 prefixEnd_4030688 := by exact prefixLift 4030688
  have htrace : WordTrace (prefixWord ++ tailWord_4030688) baseStart_4030688 baseEnd_4030688 := by
    simpa [prefixWord, tailWord_4030688, baseEnd_4030688] using wordTrace_append hprefix tailTrace_4030688
  have hstable : (prefixWord ++ tailWord_4030688).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4030688).length < 2 ^ (prefixWord ++ tailWord_4030688).sum := by decide
  have hdescent : baseEnd_4030688 < baseStart_4030688 := by decide
  rcases family_descends (prefixWord ++ tailWord_4030688) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4030690 : List Nat := [3, 3, 4, 1, 2, 1, 1, 2, 2, 4]
def baseStart_4030690 : Nat := 118140960795 + 4030690 * 2 ^ 59
def prefixEnd_4030690 : Nat := 4983230072969 + 3 ^ 40 * 4030690 * 2
def baseEnd_4030690 : Nat := 689893779756980046846067

theorem tailTrace_4030690 : CollatzResearch.WordTrace tailWord_4030690 prefixEnd_4030690 689893779756980046846067 := by
  unfold tailWord_4030690
  simp only [CollatzResearch.WordTrace]
  refine ⟨36752835441876497972954381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 98007561178337327927878349 36752835441876497972954381)
  ·
    refine ⟨13782313290703686739857893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 36752835441876497972954381 13782313290703686739857893)
    ·
      refine ⟨2584183742006941263723355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 13782313290703686739857893 2584183742006941263723355)
      ·
        refine ⟨3876275613010411895585033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2584183742006941263723355 3876275613010411895585033)
        ·
          refine ⟨2907206709757808921688775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3876275613010411895585033 2907206709757808921688775)
          ·
            refine ⟨4360810064636713382533163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2907206709757808921688775 4360810064636713382533163)
            ·
              refine ⟨6541215096955070073799745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4360810064636713382533163 6541215096955070073799745)
              ·
                refine ⟨4905911322716302555349809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6541215096955070073799745 4905911322716302555349809)
                ·
                  refine ⟨3679433492037226916512357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4905911322716302555349809 3679433492037226916512357)
                  ·
                    refine ⟨689893779756980046846067, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3679433492037226916512357 689893779756980046846067)
                    ·
                      rfl

theorem cell23_4030690_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 4, 1, 2, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 4, 1, 2, 1, 1, 2, 2, 4].length) (baseStart_4030690 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4030690 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4030690 prefixEnd_4030690 := by exact prefixLift 4030690
  have htrace : WordTrace (prefixWord ++ tailWord_4030690) baseStart_4030690 baseEnd_4030690 := by
    simpa [prefixWord, tailWord_4030690, baseEnd_4030690] using wordTrace_append hprefix tailTrace_4030690
  have hstable : (prefixWord ++ tailWord_4030690).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4030690).length < 2 ^ (prefixWord ++ tailWord_4030690).sum := by decide
  have hdescent : baseEnd_4030690 < baseStart_4030690 := by decide
  rcases family_descends (prefixWord ++ tailWord_4030690) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4030695 : List Nat := [1, 1, 5, 3, 1, 1, 1, 2, 2, 6]
def baseStart_4030695 : Nat := 118140960795 + 4030695 * 2 ^ 59
def prefixEnd_4030695 : Nat := 4983230072969 + 3 ^ 40 * 4030695 * 2
def baseEnd_4030695 : Nat := 689894635558070873658559

theorem tailTrace_4030695 : CollatzResearch.WordTrace tailWord_4030695 prefixEnd_4030695 689894635558070873658559 := by
  unfold tailWord_4030695
  simp only [CollatzResearch.WordTrace]
  refine ⟨147011524132487877745749539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98007682754991918497166359 147011524132487877745749539)
  ·
    refine ⟨220517286198731816618624309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147011524132487877745749539 220517286198731816618624309)
    ·
      refine ⟨20673495581131107807996029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 220517286198731816618624309 20673495581131107807996029)
      ·
        refine ⟨7752560842924165427998511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20673495581131107807996029 7752560842924165427998511)
        ·
          refine ⟨11628841264386248141997767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7752560842924165427998511 11628841264386248141997767)
          ·
            refine ⟨17443261896579372212996651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11628841264386248141997767 17443261896579372212996651)
            ·
              refine ⟨26164892844869058319494977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17443261896579372212996651 26164892844869058319494977)
              ·
                refine ⟨19623669633651793739621233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26164892844869058319494977 19623669633651793739621233)
                ·
                  refine ⟨14717752225238845304715925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19623669633651793739621233 14717752225238845304715925)
                  ·
                    refine ⟨689894635558070873658559, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 14717752225238845304715925 689894635558070873658559)
                    ·
                      rfl

theorem cell23_4030695_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 1, 1, 2, 2, 6].length) (baseStart_4030695 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4030695 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4030695 prefixEnd_4030695 := by exact prefixLift 4030695
  have htrace : WordTrace (prefixWord ++ tailWord_4030695) baseStart_4030695 baseEnd_4030695 := by
    simpa [prefixWord, tailWord_4030695, baseEnd_4030695] using wordTrace_append hprefix tailTrace_4030695
  have hstable : (prefixWord ++ tailWord_4030695).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4030695).length < 2 ^ (prefixWord ++ tailWord_4030695).sum := by decide
  have hdescent : baseEnd_4030695 < baseStart_4030695 := by decide
  rcases family_descends (prefixWord ++ tailWord_4030695) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4030755 : List Nat := [1, 1, 1, 4, 2, 2, 3, 2, 2, 5]
def baseStart_4030755 : Nat := 118140960795 + 4030755 * 2 ^ 59
def prefixEnd_4030755 : Nat := 4983230072969 + 3 ^ 40 * 4030755 * 2
def baseEnd_4030755 : Nat := 689904905171160795408467

theorem tailTrace_4030755 : CollatzResearch.WordTrace tailWord_4030755 prefixEnd_4030755 689904905171160795408467 := by
  unfold tailWord_4030755
  simp only [CollatzResearch.WordTrace]
  refine ⟨147013712512270507992933719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98009141674847005328622479 147013712512270507992933719)
  ·
    refine ⟨220520568768405761989400579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147013712512270507992933719 220520568768405761989400579)
    ·
      refine ⟨330780853152608642984100869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 220520568768405761989400579 330780853152608642984100869)
      ·
        refine ⟨62021409966114120559518913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 330780853152608642984100869 62021409966114120559518913)
        ·
          refine ⟨46516057474585590419639185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62021409966114120559518913 46516057474585590419639185)
          ·
            refine ⟨34887043105939192814729389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46516057474585590419639185 34887043105939192814729389)
            ·
              refine ⟨13082641164727197305523521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34887043105939192814729389 13082641164727197305523521)
              ·
                refine ⟨9811980873545397979142641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13082641164727197305523521 9811980873545397979142641)
                ·
                  refine ⟨7358985655159048484356981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9811980873545397979142641 7358985655159048484356981)
                  ·
                    refine ⟨689904905171160795408467, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7358985655159048484356981 689904905171160795408467)
                    ·
                      rfl

theorem cell23_4030755_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 3, 2, 2, 5].length) (baseStart_4030755 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4030755 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4030755 prefixEnd_4030755 := by exact prefixLift 4030755
  have htrace : WordTrace (prefixWord ++ tailWord_4030755) baseStart_4030755 baseEnd_4030755 := by
    simpa [prefixWord, tailWord_4030755, baseEnd_4030755] using wordTrace_append hprefix tailTrace_4030755
  have hstable : (prefixWord ++ tailWord_4030755).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4030755).length < 2 ^ (prefixWord ++ tailWord_4030755).sum := by decide
  have hdescent : baseEnd_4030755 < baseStart_4030755 := by decide
  rcases family_descends (prefixWord ++ tailWord_4030755) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4030768 : List Nat := [2, 1, 1, 1, 2, 2, 2, 2, 2, 8]
def baseStart_4030768 : Nat := 118140960795 + 4030768 * 2 ^ 59
def prefixEnd_4030768 : Nat := 4983230072969 + 3 ^ 40 * 4030768 * 2
def baseEnd_4030768 : Nat := 689907130253996945120947

theorem tailTrace_4030768 : CollatzResearch.WordTrace tailWord_4030768 prefixEnd_4030768 689907130253996945120947 := by
  unfold tailWord_4030768
  simp only [CollatzResearch.WordTrace]
  refine ⟨73507093330611705606578479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98009457774148940808771305 73507093330611705606578479)
  ·
    refine ⟨110260639995917558409867719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73507093330611705606578479 110260639995917558409867719)
    ·
      refine ⟨165390959993876337614801579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110260639995917558409867719 165390959993876337614801579)
      ·
        refine ⟨248086439990814506422202369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 165390959993876337614801579 248086439990814506422202369)
        ·
          refine ⟨186064829993110879816651777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 248086439990814506422202369 186064829993110879816651777)
          ·
            refine ⟨139548622494833159862488833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 186064829993110879816651777 139548622494833159862488833)
            ·
              refine ⟨104661466871124869896866625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 139548622494833159862488833 104661466871124869896866625)
              ·
                refine ⟨78496100153343652422649969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 104661466871124869896866625 78496100153343652422649969)
                ·
                  refine ⟨58872075115007739316987477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 78496100153343652422649969 58872075115007739316987477)
                  ·
                    refine ⟨689907130253996945120947, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 58872075115007739316987477 689907130253996945120947)
                    ·
                      rfl

theorem cell23_4030768_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 2, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 2, 2, 2, 8].length) (baseStart_4030768 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4030768 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4030768 prefixEnd_4030768 := by exact prefixLift 4030768
  have htrace : WordTrace (prefixWord ++ tailWord_4030768) baseStart_4030768 baseEnd_4030768 := by
    simpa [prefixWord, tailWord_4030768, baseEnd_4030768] using wordTrace_append hprefix tailTrace_4030768
  have hstable : (prefixWord ++ tailWord_4030768).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4030768).length < 2 ^ (prefixWord ++ tailWord_4030768).sum := by decide
  have hdescent : baseEnd_4030768 < baseStart_4030768 := by decide
  rcases family_descends (prefixWord ++ tailWord_4030768) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4030770 : List Nat := [3, 2, 1, 1, 6, 1, 2, 1, 2, 2, 2]
def baseStart_4030770 : Nat := 118140960795 + 4030770 * 2 ^ 59
def prefixEnd_4030770 : Nat := 4983230072969 + 3 ^ 40 * 4030770 * 2
def baseEnd_4030770 : Nat := 2069722417723299827537833

theorem tailTrace_4030770 : CollatzResearch.WordTrace tailWord_4030770 prefixEnd_4030770 2069722417723299827537833 := by
  unfold tailWord_4030770
  simp only [CollatzResearch.WordTrace]
  refine ⟨36753564901804041388682441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 98009506404810777036486509 36753564901804041388682441)
  ·
    refine ⟨27565173676353031041511831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36753564901804041388682441 27565173676353031041511831)
    ·
      refine ⟨41347760514529546562267747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27565173676353031041511831 41347760514529546562267747)
      ·
        refine ⟨62021640771794319843401621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41347760514529546562267747 62021640771794319843401621)
        ·
          refine ⟨2907264411177858742659451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 62021640771794319843401621 2907264411177858742659451)
          ·
            refine ⟨4360896616766788113989177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2907264411177858742659451 4360896616766788113989177)
            ·
              refine ⟨3270672462575091085491883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4360896616766788113989177 3270672462575091085491883)
              ·
                refine ⟨4906008693862636628237825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3270672462575091085491883 4906008693862636628237825)
                ·
                  refine ⟨3679506520396977471178369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4906008693862636628237825 3679506520396977471178369)
                  ·
                    refine ⟨2759629890297733103383777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3679506520396977471178369 2759629890297733103383777)
                    ·
                      refine ⟨2069722417723299827537833, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2759629890297733103383777 2069722417723299827537833)
                      ·
                        rfl

theorem cell23_4030770_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 6, 1, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 6, 1, 2, 1, 2, 2, 2].length) (baseStart_4030770 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4030770 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4030770 prefixEnd_4030770 := by exact prefixLift 4030770
  have htrace : WordTrace (prefixWord ++ tailWord_4030770) baseStart_4030770 baseEnd_4030770 := by
    simpa [prefixWord, tailWord_4030770, baseEnd_4030770] using wordTrace_append hprefix tailTrace_4030770
  have hstable : (prefixWord ++ tailWord_4030770).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4030770).length < 2 ^ (prefixWord ++ tailWord_4030770).sum := by decide
  have hdescent : baseEnd_4030770 < baseStart_4030770 := by decide
  rcases family_descends (prefixWord ++ tailWord_4030770) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4030815 : List Nat := [1, 1, 2, 3, 1, 2, 3, 4, 6]
def baseStart_4030815 : Nat := 118140960795 + 4030815 * 2 ^ 59
def prefixEnd_4030815 : Nat := 4983230072969 + 3 ^ 40 * 4030815 * 2
def baseEnd_4030815 : Nat := 229971724928083572386125

theorem tailTrace_4030815 : CollatzResearch.WordTrace tailWord_4030815 prefixEnd_4030815 229971724928083572386125 := by
  unfold tailWord_4030815
  simp only [CollatzResearch.WordTrace]
  refine ⟨147015900892053138240117899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98010600594702092160078599 147015900892053138240117899)
  ·
    refine ⟨220523851338079707360176849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147015900892053138240117899 220523851338079707360176849)
    ·
      refine ⟨165392888503559780520132637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 220523851338079707360176849 165392888503559780520132637)
      ·
        refine ⟨62022333188834917695049739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 165392888503559780520132637 62022333188834917695049739)
        ·
          refine ⟨93033499783252376542574609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62022333188834917695049739 93033499783252376542574609)
          ·
            refine ⟨69775124837439282406930957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 93033499783252376542574609 69775124837439282406930957)
            ·
              refine ⟨26165671814039730902599109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 69775124837439282406930957 26165671814039730902599109)
              ·
                refine ⟨4906063465132449544237333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 26165671814039730902599109 4906063465132449544237333)
                ·
                  refine ⟨229971724928083572386125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4906063465132449544237333 229971724928083572386125)
                  ·
                    rfl

theorem cell23_4030815_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 3, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 3, 4, 6].length) (baseStart_4030815 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4030815 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4030815 prefixEnd_4030815 := by exact prefixLift 4030815
  have htrace : WordTrace (prefixWord ++ tailWord_4030815) baseStart_4030815 baseEnd_4030815 := by
    simpa [prefixWord, tailWord_4030815, baseEnd_4030815] using wordTrace_append hprefix tailTrace_4030815
  have hstable : (prefixWord ++ tailWord_4030815).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4030815).length < 2 ^ (prefixWord ++ tailWord_4030815).sum := by decide
  have hdescent : baseEnd_4030815 < baseStart_4030815 := by decide
  rcases family_descends (prefixWord ++ tailWord_4030815) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4030819 : List Nat := [1, 1, 1, 5, 2, 1, 3, 4, 1, 4]
def baseStart_4030819 : Nat := 118140960795 + 4030819 * 2 ^ 59
def prefixEnd_4030819 : Nat := 4983230072969 + 3 ^ 40 * 4030819 * 2
def baseEnd_4030819 : Nat := 689915859425123378608369

theorem tailTrace_4030819 : CollatzResearch.WordTrace tailWord_4030819 prefixEnd_4030819 689915859425123378608369 := by
  unfold tailWord_4030819
  simp only [CollatzResearch.WordTrace]
  refine ⟨147016046784038646923263511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98010697856025764615509007 147016046784038646923263511)
  ·
    refine ⟨220524070176057970384895267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147016046784038646923263511 220524070176057970384895267)
    ·
      refine ⟨330786105264086955577342901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 220524070176057970384895267 330786105264086955577342901)
      ·
        refine ⟨31011197368508152085375897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 330786105264086955577342901 31011197368508152085375897)
        ·
          refine ⟨23258398026381114064031923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31011197368508152085375897 23258398026381114064031923)
          ·
            refine ⟨34887597039571671096047885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23258398026381114064031923 34887597039571671096047885)
            ·
              refine ⟨13082848889839376661017957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34887597039571671096047885 13082848889839376661017957)
              ·
                refine ⟨2453034166844883123940867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13082848889839376661017957 2453034166844883123940867)
                ·
                  refine ⟨3679551250267324685911301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2453034166844883123940867 3679551250267324685911301)
                  ·
                    refine ⟨689915859425123378608369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3679551250267324685911301 689915859425123378608369)
                    ·
                      rfl

theorem cell23_4030819_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 3, 4, 1, 4].length) (baseStart_4030819 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4030819 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4030819 prefixEnd_4030819 := by exact prefixLift 4030819
  have htrace : WordTrace (prefixWord ++ tailWord_4030819) baseStart_4030819 baseEnd_4030819 := by
    simpa [prefixWord, tailWord_4030819, baseEnd_4030819] using wordTrace_append hprefix tailTrace_4030819
  have hstable : (prefixWord ++ tailWord_4030819).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4030819).length < 2 ^ (prefixWord ++ tailWord_4030819).sum := by decide
  have hdescent : baseEnd_4030819 < baseStart_4030819 := by decide
  rcases family_descends (prefixWord ++ tailWord_4030819) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4030870 : List Nat := [5, 3, 1, 2, 1, 1, 2, 1, 3, 4]
def baseStart_4030870 : Nat := 118140960795 + 4030870 * 2 ^ 59
def prefixEnd_4030870 : Nat := 4983230072969 + 3 ^ 40 * 4030870 * 2
def baseEnd_4030870 : Nat := 689924588596249812095791

theorem tailTrace_4030870 : CollatzResearch.WordTrace tailWord_4030870 prefixEnd_4030870 689924588596249812095791 := by
  unfold tailWord_4030870
  simp only [CollatzResearch.WordTrace]
  refine ⟨9188619181678367664585629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 98011937937902588422246709 9188619181678367664585629)
  ·
    refine ⟨3445732193129387874219611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9188619181678367664585629 3445732193129387874219611)
    ·
      refine ⟨5168598289694081811329417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3445732193129387874219611 5168598289694081811329417)
      ·
        refine ⟨3876448717270561358497063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5168598289694081811329417 3876448717270561358497063)
        ·
          refine ⟨5814673075905842037745595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3876448717270561358497063 5814673075905842037745595)
          ·
            refine ⟨8722009613858763056618393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5814673075905842037745595 8722009613858763056618393)
            ·
              refine ⟨6541507210394072292463795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8722009613858763056618393 6541507210394072292463795)
              ·
                refine ⟨9812260815591108438695693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6541507210394072292463795 9812260815591108438695693)
                ·
                  refine ⟨3679597805846665664510885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9812260815591108438695693 3679597805846665664510885)
                  ·
                    refine ⟨689924588596249812095791, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3679597805846665664510885 689924588596249812095791)
                    ·
                      rfl

theorem cell23_4030870_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 2, 1, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 2, 1, 1, 2, 1, 3, 4].length) (baseStart_4030870 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4030870 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4030870 prefixEnd_4030870 := by exact prefixLift 4030870
  have htrace : WordTrace (prefixWord ++ tailWord_4030870) baseStart_4030870 baseEnd_4030870 := by
    simpa [prefixWord, tailWord_4030870, baseEnd_4030870] using wordTrace_append hprefix tailTrace_4030870
  have hstable : (prefixWord ++ tailWord_4030870).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4030870).length < 2 ^ (prefixWord ++ tailWord_4030870).sum := by decide
  have hdescent : baseEnd_4030870 < baseStart_4030870 := by decide
  rcases family_descends (prefixWord ++ tailWord_4030870) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4030919 : List Nat := [1, 1, 4, 1, 1, 4, 2, 3, 1, 2, 3]
def baseStart_4030919 : Nat := 118140960795 + 4030919 * 2 ^ 59
def prefixEnd_4030919 : Nat := 4983230072969 + 3 ^ 40 * 4030919 * 2
def baseEnd_4030919 : Nat := 2069798926340819744574647

theorem tailTrace_4030919 : CollatzResearch.WordTrace tailWord_4030919 prefixEnd_4030919 2069798926340819744574647 := by
  unfold tailWord_4030919
  simp only [CollatzResearch.WordTrace]
  refine ⟨147019694083676364001903811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98013129389117576001269207 147019694083676364001903811)
  ·
    refine ⟨220529541125514546002855717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147019694083676364001903811 220529541125514546002855717)
    ·
      refine ⟨41349288961033977375535447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 220529541125514546002855717 41349288961033977375535447)
      ·
        refine ⟨62023933441550966063303171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41349288961033977375535447 62023933441550966063303171)
        ·
          refine ⟨93035900162326449094954757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62023933441550966063303171 93035900162326449094954757)
          ·
            refine ⟨17444231280436209205304017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 93035900162326449094954757 17444231280436209205304017)
            ·
              refine ⟨13083173460327156903978013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17444231280436209205304017 13083173460327156903978013)
              ·
                refine ⟨4906190047622683838991755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13083173460327156903978013 4906190047622683838991755)
                ·
                  refine ⟨7359285071434025758487633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4906190047622683838991755 7359285071434025758487633)
                  ·
                    refine ⟨5519463803575519318865725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7359285071434025758487633 5519463803575519318865725)
                    ·
                      refine ⟨2069798926340819744574647, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5519463803575519318865725 2069798926340819744574647)
                      ·
                        rfl

theorem cell23_4030919_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 4, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 4, 2, 3, 1, 2, 3].length) (baseStart_4030919 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4030919 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4030919 prefixEnd_4030919 := by exact prefixLift 4030919
  have htrace : WordTrace (prefixWord ++ tailWord_4030919) baseStart_4030919 baseEnd_4030919 := by
    simpa [prefixWord, tailWord_4030919, baseEnd_4030919] using wordTrace_append hprefix tailTrace_4030919
  have hstable : (prefixWord ++ tailWord_4030919).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4030919).length < 2 ^ (prefixWord ++ tailWord_4030919).sum := by decide
  have hdescent : baseEnd_4030919 < baseStart_4030919 := by decide
  rcases family_descends (prefixWord ++ tailWord_4030919) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4030933 : List Nat := [1, 3, 2, 3, 1, 4, 1, 1, 3, 2, 2]
def baseStart_4030933 : Nat := 118140960795 + 4030933 * 2 ^ 59
def prefixEnd_4030933 : Nat := 4983230072969 + 3 ^ 40 * 4030933 * 2
def baseEnd_4030933 : Nat := 2069806115069982689799583

theorem tailTrace_4030933 : CollatzResearch.WordTrace tailWord_4030933 prefixEnd_4030933 2069806115069982689799583 := by
  unfold tailWord_4030933
  simp only [CollatzResearch.WordTrace]
  refine ⟨147020204705625644392913453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98013469803750429595275635 147020204705625644392913453)
  ·
    refine ⟨55132576764609616647342545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 147020204705625644392913453 55132576764609616647342545)
    ·
      refine ⟨41349432573457212485506909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55132576764609616647342545 41349432573457212485506909)
      ·
        refine ⟨15506037215046454682065091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 41349432573457212485506909 15506037215046454682065091)
        ·
          refine ⟨23259055822569682023097637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15506037215046454682065091 23259055822569682023097637)
          ·
            refine ⟨4361072966731815379330807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 23259055822569682023097637 4361072966731815379330807)
            ·
              refine ⟨6541609450097723068996211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4361072966731815379330807 6541609450097723068996211)
              ·
                refine ⟨9812414175146584603494317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6541609450097723068996211 9812414175146584603494317)
                ·
                  refine ⟨3679655315679969226310369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9812414175146584603494317 3679655315679969226310369)
                  ·
                    refine ⟨2759741486759976919732777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3679655315679969226310369 2759741486759976919732777)
                    ·
                      refine ⟨2069806115069982689799583, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2759741486759976919732777 2069806115069982689799583)
                      ·
                        rfl

theorem cell23_4030933_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 4, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 4, 1, 1, 3, 2, 2].length) (baseStart_4030933 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4030933 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4030933 prefixEnd_4030933 := by exact prefixLift 4030933
  have htrace : WordTrace (prefixWord ++ tailWord_4030933) baseStart_4030933 baseEnd_4030933 := by
    simpa [prefixWord, tailWord_4030933, baseEnd_4030933] using wordTrace_append hprefix tailTrace_4030933
  have hstable : (prefixWord ++ tailWord_4030933).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4030933).length < 2 ^ (prefixWord ++ tailWord_4030933).sum := by decide
  have hdescent : baseEnd_4030933 < baseStart_4030933 := by decide
  rcases family_descends (prefixWord ++ tailWord_4030933) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4030983 : List Nat := [1, 1, 4, 3, 3, 1, 2, 2, 2, 1, 3]
def baseStart_4030983 : Nat := 118140960795 + 4030983 * 2 ^ 59
def prefixEnd_4030983 : Nat := 4983230072969 + 3 ^ 40 * 4030983 * 2
def baseEnd_4030983 : Nat := 2069831789102707494174353

theorem tailTrace_4030983 : CollatzResearch.WordTrace tailWord_4030983 prefixEnd_4030983 2069831789102707494174353 := by
  unfold tailWord_4030983
  simp only [CollatzResearch.WordTrace]
  refine ⟨147022028355444502932233603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98014685570296335288155735 147022028355444502932233603)
  ·
    refine ⟨220533042533166754398350405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147022028355444502932233603 220533042533166754398350405)
    ·
      refine ⟨41349945474968766449690701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 220533042533166754398350405 41349945474968766449690701)
      ·
        refine ⟨15506229553113287418634013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 41349945474968766449690701 15506229553113287418634013)
        ·
          refine ⟨5814836082417482781987755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15506229553113287418634013 5814836082417482781987755)
          ·
            refine ⟨8722254123626224172981633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5814836082417482781987755 8722254123626224172981633)
            ·
              refine ⟨6541690592719668129736225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8722254123626224172981633 6541690592719668129736225)
              ·
                refine ⟨4906267944539751097302169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6541690592719668129736225 4906267944539751097302169)
                ·
                  refine ⟨3679700958404813322976627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4906267944539751097302169 3679700958404813322976627)
                  ·
                    refine ⟨5519551437607219984464941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3679700958404813322976627 5519551437607219984464941)
                    ·
                      refine ⟨2069831789102707494174353, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5519551437607219984464941 2069831789102707494174353)
                      ·
                        rfl

theorem cell23_4030983_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 3, 1, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 3, 1, 2, 2, 2, 1, 3].length) (baseStart_4030983 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4030983 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4030983 prefixEnd_4030983 := by exact prefixLift 4030983
  have htrace : WordTrace (prefixWord ++ tailWord_4030983) baseStart_4030983 baseEnd_4030983 := by
    simpa [prefixWord, tailWord_4030983, baseEnd_4030983] using wordTrace_append hprefix tailTrace_4030983
  have hstable : (prefixWord ++ tailWord_4030983).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4030983).length < 2 ^ (prefixWord ++ tailWord_4030983).sum := by decide
  have hdescent : baseEnd_4030983 < baseStart_4030983 := by decide
  rcases family_descends (prefixWord ++ tailWord_4030983) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4031002 : List Nat := [3, 1, 1, 3, 1, 1, 3, 1, 1, 4, 4]
def baseStart_4031002 : Nat := 118140960795 + 4031002 * 2 ^ 59
def prefixEnd_4031002 : Nat := 4983230072969 + 3 ^ 40 * 4031002 * 2
def baseEnd_4031002 : Nat := 2069841545235142919836765

theorem tailTrace_4031002 : CollatzResearch.WordTrace tailWord_4031002 prefixEnd_4031002 2069841545235142919836765 := by
  unfold tailWord_4031002
  simp only [CollatzResearch.WordTrace]
  refine ⟨36755680335593917294293815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 98015147561583779451450173 36755680335593917294293815)
  ·
    refine ⟨55133520503390875941440723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36755680335593917294293815 55133520503390875941440723)
    ·
      refine ⟨82700280755086313912161085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55133520503390875941440723 82700280755086313912161085)
      ·
        refine ⟨31012605283157367717060407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 82700280755086313912161085 31012605283157367717060407)
        ·
          refine ⟨46518907924736051575590611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31012605283157367717060407 46518907924736051575590611)
          ·
            refine ⟨69778361887104077363385917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46518907924736051575590611 69778361887104077363385917)
            ·
              refine ⟨26166885707664029011269719, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 69778361887104077363385917 26166885707664029011269719)
              ·
                refine ⟨39250328561496043516904579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26166885707664029011269719 39250328561496043516904579)
                ·
                  refine ⟨58875492842244065275356869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39250328561496043516904579 58875492842244065275356869)
                  ·
                    refine ⟨11039154907920762239129413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 58875492842244065275356869 11039154907920762239129413)
                    ·
                      refine ⟨2069841545235142919836765, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11039154907920762239129413 2069841545235142919836765)
                      ·
                        rfl

theorem cell23_4031002_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 3, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 3, 1, 1, 4, 4].length) (baseStart_4031002 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4031002 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4031002 prefixEnd_4031002 := by exact prefixLift 4031002
  have htrace : WordTrace (prefixWord ++ tailWord_4031002) baseStart_4031002 baseEnd_4031002 := by
    simpa [prefixWord, tailWord_4031002, baseEnd_4031002] using wordTrace_append hprefix tailTrace_4031002
  have hstable : (prefixWord ++ tailWord_4031002).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4031002).length < 2 ^ (prefixWord ++ tailWord_4031002).sum := by decide
  have hdescent : baseEnd_4031002 < baseStart_4031002 := by decide
  rcases family_descends (prefixWord ++ tailWord_4031002) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4031046 : List Nat := [6, 1, 1, 1, 2, 1, 1, 3, 7]
def baseStart_4031046 : Nat := 118140960795 + 4031046 * 2 ^ 59
def prefixEnd_4031046 : Nat := 4983230072969 + 3 ^ 40 * 4031046 * 2
def baseEnd_4031046 : Nat := 229984904264882305298507

theorem tailTrace_4031046 : CollatzResearch.WordTrace tailWord_4031046 prefixEnd_4031046 229984904264882305298507 := by
  unfold tailWord_4031046
  simp only [CollatzResearch.WordTrace]
  refine ⟨4594510192319258271618031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 98016217436144176461184661 4594510192319258271618031)
  ·
    refine ⟨6891765288478887407427047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4594510192319258271618031 6891765288478887407427047)
    ·
      refine ⟨10337647932718331111140571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6891765288478887407427047 10337647932718331111140571)
      ·
        refine ⟨15506471899077496666710857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10337647932718331111140571 15506471899077496666710857)
        ·
          refine ⟨11629853924308122500033143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15506471899077496666710857 11629853924308122500033143)
          ·
            refine ⟨17444780886462183750049715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11629853924308122500033143 17444780886462183750049715)
            ·
              refine ⟨26167171329693275625074573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17444780886462183750049715 26167171329693275625074573)
              ·
                refine ⟨9812689248634978359402965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26167171329693275625074573 9812689248634978359402965)
                ·
                  refine ⟨229984904264882305298507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 9812689248634978359402965 229984904264882305298507)
                  ·
                    rfl

theorem cell23_4031046_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 1, 1, 3, 7].length) (baseStart_4031046 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4031046 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4031046 prefixEnd_4031046 := by exact prefixLift 4031046
  have htrace : WordTrace (prefixWord ++ tailWord_4031046) baseStart_4031046 baseEnd_4031046 := by
    simpa [prefixWord, tailWord_4031046, baseEnd_4031046] using wordTrace_append hprefix tailTrace_4031046
  have hstable : (prefixWord ++ tailWord_4031046).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4031046).length < 2 ^ (prefixWord ++ tailWord_4031046).sum := by decide
  have hdescent : baseEnd_4031046 < baseStart_4031046 := by decide
  rcases family_descends (prefixWord ++ tailWord_4031046) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4031052 : List Nat := [2, 2, 1, 3, 1, 2, 2, 1, 1, 1, 7]
def baseStart_4031052 : Nat := 118140960795 + 4031052 * 2 ^ 59
def prefixEnd_4031052 : Nat := 4983230072969 + 3 ^ 40 * 4031052 * 2
def baseEnd_4031052 : Nat := 2069867219267867724211535

theorem tailTrace_4031052 : CollatzResearch.WordTrace tailWord_4031052 prefixEnd_4031052 2069867219267867724211535 := by
  unfold tailWord_4031052
  simp only [CollatzResearch.WordTrace]
  refine ⟨73512272496097263858247705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98016363328129685144330273 73512272496097263858247705)
  ·
    refine ⟨55134204372072947893685779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73512272496097263858247705 55134204372072947893685779)
    ·
      refine ⟨82701306558109421840528669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55134204372072947893685779 82701306558109421840528669)
      ·
        refine ⟨31012989959291033190198251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 82701306558109421840528669 31012989959291033190198251)
        ·
          refine ⟨46519484938936549785297377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31012989959291033190198251 46519484938936549785297377)
          ·
            refine ⟨34889613704202412338973033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46519484938936549785297377 34889613704202412338973033)
            ·
              refine ⟨26167210278151809254229775, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34889613704202412338973033 26167210278151809254229775)
              ·
                refine ⟨39250815417227713881344663, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26167210278151809254229775 39250815417227713881344663)
                ·
                  refine ⟨58876223125841570822016995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39250815417227713881344663 58876223125841570822016995)
                  ·
                    refine ⟨88314334688762356233025493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 58876223125841570822016995 88314334688762356233025493)
                    ·
                      refine ⟨2069867219267867724211535, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 88314334688762356233025493 2069867219267867724211535)
                      ·
                        rfl

theorem cell23_4031052_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 2, 1, 1, 1, 7].length) (baseStart_4031052 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4031052 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4031052 prefixEnd_4031052 := by exact prefixLift 4031052
  have htrace : WordTrace (prefixWord ++ tailWord_4031052) baseStart_4031052 baseEnd_4031052 := by
    simpa [prefixWord, tailWord_4031052, baseEnd_4031052] using wordTrace_append hprefix tailTrace_4031052
  have hstable : (prefixWord ++ tailWord_4031052).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4031052).length < 2 ^ (prefixWord ++ tailWord_4031052).sum := by decide
  have hdescent : baseEnd_4031052 < baseStart_4031052 := by decide
  rcases family_descends (prefixWord ++ tailWord_4031052) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4031079 : List Nat := [1, 1, 5, 1, 1, 1, 1, 5, 2, 1, 4]
def baseStart_4031079 : Nat := 118140960795 + 4031079 * 2 ^ 59
def prefixEnd_4031079 : Nat := 4983230072969 + 3 ^ 40 * 4031079 * 2
def baseEnd_4031079 : Nat := 2069881083245539118573911

theorem tailTrace_4031079 : CollatzResearch.WordTrace tailWord_4031079 prefixEnd_4031079 2069881083245539118573911 := by
  unfold tailWord_4031079
  simp only [CollatzResearch.WordTrace]
  refine ⟨147025529763096711327728291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98017019842064474218485527 147025529763096711327728291)
  ·
    refine ⟨220538294644645066991592437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147025529763096711327728291 220538294644645066991592437)
    ·
      refine ⟨20675465122935475030461791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 220538294644645066991592437 20675465122935475030461791)
      ·
        refine ⟨31013197684403212545692687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20675465122935475030461791 31013197684403212545692687)
        ·
          refine ⟨46519796526604818818539031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31013197684403212545692687 46519796526604818818539031)
          ·
            refine ⟨69779694789907228227808547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46519796526604818818539031 69779694789907228227808547)
            ·
              refine ⟨104669542184860842341712821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 69779694789907228227808547 104669542184860842341712821)
              ·
                refine ⟨9812769579830703969535577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 104669542184860842341712821 9812769579830703969535577)
                ·
                  refine ⟨7359577184873027977151683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9812769579830703969535577 7359577184873027977151683)
                  ·
                    refine ⟨11039365777309541965727525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7359577184873027977151683 11039365777309541965727525)
                    ·
                      refine ⟨2069881083245539118573911, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11039365777309541965727525 2069881083245539118573911)
                      ·
                        rfl

theorem cell23_4031079_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 1, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 1, 5, 2, 1, 4].length) (baseStart_4031079 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4031079 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4031079 prefixEnd_4031079 := by exact prefixLift 4031079
  have htrace : WordTrace (prefixWord ++ tailWord_4031079) baseStart_4031079 baseEnd_4031079 := by
    simpa [prefixWord, tailWord_4031079, baseEnd_4031079] using wordTrace_append hprefix tailTrace_4031079
  have hstable : (prefixWord ++ tailWord_4031079).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4031079).length < 2 ^ (prefixWord ++ tailWord_4031079).sum := by decide
  have hdescent : baseEnd_4031079 < baseStart_4031079 := by decide
  rcases family_descends (prefixWord ++ tailWord_4031079) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4031080 : List Nat := [2, 1, 4, 3, 3, 1, 1, 3, 5]
def baseStart_4031080 : Nat := 118140960795 + 4031080 * 2 ^ 59
def prefixEnd_4031080 : Nat := 4983230072969 + 3 ^ 40 * 4031080 * 2
def baseEnd_4031080 : Nat := 229986844080688179406823

theorem tailTrace_4031080 : CollatzResearch.WordTrace tailWord_4031080 prefixEnd_4031080 229986844080688179406823 := by
  unfold tailWord_4031080
  simp only [CollatzResearch.WordTrace]
  refine ⟨73512783118046544249257347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98017044157395392332343129 73512783118046544249257347)
  ·
    refine ⟨110269174677069816373886021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73512783118046544249257347 110269174677069816373886021)
    ·
      refine ⟨20675470251950590570103629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 110269174677069816373886021 20675470251950590570103629)
      ·
        refine ⟨7753301344481471463788861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20675470251950590570103629 7753301344481471463788861)
        ·
          refine ⟨2907488004180551798920823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7753301344481471463788861 2907488004180551798920823)
          ·
            refine ⟨4361232006270827698381235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2907488004180551798920823 4361232006270827698381235)
            ·
              refine ⟨6541848009406241547571853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4361232006270827698381235 6541848009406241547571853)
              ·
                refine ⟨2453193003527340580339445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6541848009406241547571853 2453193003527340580339445)
                ·
                  refine ⟨229986844080688179406823, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2453193003527340580339445 229986844080688179406823)
                  ·
                    rfl

theorem cell23_4031080_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 3, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 3, 1, 1, 3, 5].length) (baseStart_4031080 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4031080 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4031080 prefixEnd_4031080 := by exact prefixLift 4031080
  have htrace : WordTrace (prefixWord ++ tailWord_4031080) baseStart_4031080 baseEnd_4031080 := by
    simpa [prefixWord, tailWord_4031080, baseEnd_4031080] using wordTrace_append hprefix tailTrace_4031080
  have hstable : (prefixWord ++ tailWord_4031080).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4031080).length < 2 ^ (prefixWord ++ tailWord_4031080).sum := by decide
  have hdescent : baseEnd_4031080 < baseStart_4031080 := by decide
  rcases family_descends (prefixWord ++ tailWord_4031080) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4031153 : List Nat := [1, 2, 2, 6, 1, 1, 2, 2, 6]
def baseStart_4031153 : Nat := 118140960795 + 4031153 * 2 ^ 59
def prefixEnd_4031153 : Nat := 4983230072969 + 3 ^ 40 * 4031153 * 2
def baseEnd_4031153 : Nat := 229991008979330203227619

theorem tailTrace_4031153 : CollatzResearch.WordTrace tailWord_4031153 prefixEnd_4031153 229991008979330203227619 := by
  unfold tailWord_4031153
  simp only [CollatzResearch.WordTrace]
  refine ⟨147028228764828621965922113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98018819176552414643948075 147028228764828621965922113)
  ·
    refine ⟨110271171573621466474441585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 147028228764828621965922113 110271171573621466474441585)
    ·
      refine ⟨82703378680216099855831189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 110271171573621466474441585 82703378680216099855831189)
      ·
        refine ⟨3876720875635129680742087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 82703378680216099855831189 3876720875635129680742087)
        ·
          refine ⟨5815081313452694521113131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3876720875635129680742087 5815081313452694521113131)
          ·
            refine ⟨8722621970179041781669697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5815081313452694521113131 8722621970179041781669697)
            ·
              refine ⟨6541966477634281336252273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8722621970179041781669697 6541966477634281336252273)
              ·
                refine ⟨4906474858225711002189205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6541966477634281336252273 4906474858225711002189205)
                ·
                  refine ⟨229991008979330203227619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4906474858225711002189205 229991008979330203227619)
                  ·
                    rfl

theorem cell23_4031153_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 6, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 6, 1, 1, 2, 2, 6].length) (baseStart_4031153 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4031153 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4031153 prefixEnd_4031153 := by exact prefixLift 4031153
  have htrace : WordTrace (prefixWord ++ tailWord_4031153) baseStart_4031153 baseEnd_4031153 := by
    simpa [prefixWord, tailWord_4031153, baseEnd_4031153] using wordTrace_append hprefix tailTrace_4031153
  have hstable : (prefixWord ++ tailWord_4031153).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4031153).length < 2 ^ (prefixWord ++ tailWord_4031153).sum := by decide
  have hdescent : baseEnd_4031153 < baseStart_4031153 := by decide
  rcases family_descends (prefixWord ++ tailWord_4031153) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4031157 : List Nat := [1, 3, 3, 3, 1, 3, 2, 2, 1, 4]
def baseStart_4031157 : Nat := 118140960795 + 4031157 * 2 ^ 59
def prefixEnd_4031157 : Nat := 4983230072969 + 3 ^ 40 * 4031157 * 2
def baseEnd_4031157 : Nat := 689973711578863271132851

theorem tailTrace_4031157 : CollatzResearch.WordTrace tailWord_4031157 prefixEnd_4031157 689973711578863271132851 := by
  unfold tailWord_4031157
  simp only [CollatzResearch.WordTrace]
  refine ⟨147028374656814130649067725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98018916437876087099378483 147028374656814130649067725)
  ·
    refine ⟨55135640496305298993400397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 147028374656814130649067725 55135640496305298993400397)
    ·
      refine ⟨20675865186114487122525149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 55135640496305298993400397 20675865186114487122525149)
      ·
        refine ⟨7753449444792932670946931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20675865186114487122525149 7753449444792932670946931)
        ·
          refine ⟨11630174167189399006420397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7753449444792932670946931 11630174167189399006420397)
          ·
            refine ⟨4361315312696024627407649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11630174167189399006420397 4361315312696024627407649)
            ·
              refine ⟨3270986484522018470555737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4361315312696024627407649 3270986484522018470555737)
              ·
                refine ⟨2453239863391513852916803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3270986484522018470555737 2453239863391513852916803)
                ·
                  refine ⟨3679859795087270779375205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2453239863391513852916803 3679859795087270779375205)
                  ·
                    refine ⟨689973711578863271132851, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3679859795087270779375205 689973711578863271132851)
                    ·
                      rfl

theorem cell23_4031157_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 3, 2, 2, 1, 4].length) (baseStart_4031157 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4031157 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4031157 prefixEnd_4031157 := by exact prefixLift 4031157
  have htrace : WordTrace (prefixWord ++ tailWord_4031157) baseStart_4031157 baseEnd_4031157 := by
    simpa [prefixWord, tailWord_4031157, baseEnd_4031157] using wordTrace_append hprefix tailTrace_4031157
  have hstable : (prefixWord ++ tailWord_4031157).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4031157).length < 2 ^ (prefixWord ++ tailWord_4031157).sum := by decide
  have hdescent : baseEnd_4031157 < baseStart_4031157 := by decide
  rcases family_descends (prefixWord ++ tailWord_4031157) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4031179 : List Nat := [1, 1, 1, 1, 3, 2, 1, 1, 8, 4]
def baseStart_4031179 : Nat := 118140960795 + 4031179 * 2 ^ 59
def prefixEnd_4031179 : Nat := 4983230072969 + 3 ^ 40 * 4031179 * 2
def baseEnd_4031179 : Nat := 689977477103662909107817

theorem tailTrace_4031179 : CollatzResearch.WordTrace tailWord_4031179 prefixEnd_4031179 689977477103662909107817 := by
  unfold tailWord_4031179
  simp only [CollatzResearch.WordTrace]
  refine ⟨147029177062734428406368591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98019451375156285604245727 147029177062734428406368591)
  ·
    refine ⟨220543765594101642609552887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147029177062734428406368591 220543765594101642609552887)
    ·
      refine ⟨330815648391152463914329331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 220543765594101642609552887 330815648391152463914329331)
      ·
        refine ⟨496223472586728695871493997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 330815648391152463914329331 496223472586728695871493997)
        ·
          refine ⟨186083802220023260951810249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 496223472586728695871493997 186083802220023260951810249)
          ·
            refine ⟨139562851665017445713857687, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 186083802220023260951810249 139562851665017445713857687)
            ·
              refine ⟨209344277497526168570786531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 139562851665017445713857687 209344277497526168570786531)
              ·
                refine ⟨314016416246289252856179797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 209344277497526168570786531 314016416246289252856179797)
                ·
                  refine ⟨3679879877886202181908357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 314016416246289252856179797 3679879877886202181908357)
                  ·
                    refine ⟨689977477103662909107817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3679879877886202181908357 689977477103662909107817)
                    ·
                      rfl

theorem cell23_4031179_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 1, 1, 8, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 1, 1, 8, 4].length) (baseStart_4031179 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4031179 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4031179 prefixEnd_4031179 := by exact prefixLift 4031179
  have htrace : WordTrace (prefixWord ++ tailWord_4031179) baseStart_4031179 baseEnd_4031179 := by
    simpa [prefixWord, tailWord_4031179, baseEnd_4031179] using wordTrace_append hprefix tailTrace_4031179
  have hstable : (prefixWord ++ tailWord_4031179).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4031179).length < 2 ^ (prefixWord ++ tailWord_4031179).sum := by decide
  have hdescent : baseEnd_4031179 < baseStart_4031179 := by decide
  rcases family_descends (prefixWord ++ tailWord_4031179) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4031203 : List Nat := [1, 1, 1, 7, 1, 2, 1, 3, 1, 1, 4]
def baseStart_4031203 : Nat := 118140960795 + 4031203 * 2 ^ 59
def prefixEnd_4031203 : Nat := 4983230072969 + 3 ^ 40 * 4031203 * 2
def baseEnd_4031203 : Nat := 2069944754846696633423341

theorem tailTrace_4031203 : CollatzResearch.WordTrace tailWord_4031203 prefixEnd_4031203 2069944754846696633423341 := by
  unfold tailWord_4031203
  simp only [CollatzResearch.WordTrace]
  refine ⟨147030052414647480505242263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98020034943098320336828175 147030052414647480505242263)
  ·
    refine ⟨220545078621971220757863395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147030052414647480505242263 220545078621971220757863395)
    ·
      refine ⟨330817617932956831136795093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 220545078621971220757863395 330817617932956831136795093)
      ·
        refine ⟨7753537920303675729768635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 330817617932956831136795093 7753537920303675729768635)
        ·
          refine ⟨11630306880455513594652953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7753537920303675729768635 11630306880455513594652953)
          ·
            refine ⟨8722730160341635195989715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11630306880455513594652953 8722730160341635195989715)
            ·
              refine ⟨13084095240512452793984573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8722730160341635195989715 13084095240512452793984573)
              ·
                refine ⟨4906535715192169797744215, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13084095240512452793984573 4906535715192169797744215)
                ·
                  refine ⟨7359803572788254696616323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4906535715192169797744215 7359803572788254696616323)
                  ·
                    refine ⟨11039705359182382044924485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7359803572788254696616323 11039705359182382044924485)
                    ·
                      refine ⟨2069944754846696633423341, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11039705359182382044924485 2069944754846696633423341)
                      ·
                        rfl

theorem cell23_4031203_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 2, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 2, 1, 3, 1, 1, 4].length) (baseStart_4031203 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4031203 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4031203 prefixEnd_4031203 := by exact prefixLift 4031203
  have htrace : WordTrace (prefixWord ++ tailWord_4031203) baseStart_4031203 baseEnd_4031203 := by
    simpa [prefixWord, tailWord_4031203, baseEnd_4031203] using wordTrace_append hprefix tailTrace_4031203
  have hstable : (prefixWord ++ tailWord_4031203).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4031203).length < 2 ^ (prefixWord ++ tailWord_4031203).sum := by decide
  have hdescent : baseEnd_4031203 < baseStart_4031203 := by decide
  rcases family_descends (prefixWord ++ tailWord_4031203) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4031249 : List Nat := [1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 5]
def baseStart_4031249 : Nat := 118140960795 + 4031249 * 2 ^ 59
def prefixEnd_4031249 : Nat := 4983230072969 + 3 ^ 40 * 4031249 * 2
def baseEnd_4031249 : Nat := 2069968374956803453448129

theorem tailTrace_4031249 : CollatzResearch.WordTrace tailWord_4031249 prefixEnd_4031249 2069968374956803453448129 := by
  unfold tailWord_4031249
  simp only [CollatzResearch.WordTrace]
  refine ⟨147031730172480830361416801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98021153448320553574277867 147031730172480830361416801)
  ·
    refine ⟨110273797629360622771062601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 147031730172480830361416801 110273797629360622771062601)
    ·
      refine ⟨82705348222020467078296951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 110273797629360622771062601 82705348222020467078296951)
      ·
        refine ⟨124058022333030700617445427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82705348222020467078296951 124058022333030700617445427)
        ·
          refine ⟨186087033499546050926168141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 124058022333030700617445427 186087033499546050926168141)
          ·
            refine ⟨69782637562329769097313053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 186087033499546050926168141 69782637562329769097313053)
            ·
              refine ⟨26168489085873663411492395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 69782637562329769097313053 26168489085873663411492395)
              ·
                refine ⟨39252733628810495117238593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26168489085873663411492395 39252733628810495117238593)
                ·
                  refine ⟨29439550221607871337928945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 39252733628810495117238593 29439550221607871337928945)
                  ·
                    refine ⟨22079662666205903503446709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 29439550221607871337928945 22079662666205903503446709)
                    ·
                      refine ⟨2069968374956803453448129, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 22079662666205903503446709 2069968374956803453448129)
                      ·
                        rfl

theorem cell23_4031249_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 5].length) (baseStart_4031249 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4031249 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4031249 prefixEnd_4031249 := by exact prefixLift 4031249
  have htrace : WordTrace (prefixWord ++ tailWord_4031249) baseStart_4031249 baseEnd_4031249 := by
    simpa [prefixWord, tailWord_4031249, baseEnd_4031249] using wordTrace_append hprefix tailTrace_4031249
  have hstable : (prefixWord ++ tailWord_4031249).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4031249).length < 2 ^ (prefixWord ++ tailWord_4031249).sum := by decide
  have hdescent : baseEnd_4031249 < baseStart_4031249 := by decide
  rcases family_descends (prefixWord ++ tailWord_4031249) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4031279 : List Nat := [1, 1, 2, 1, 2, 1, 2, 1, 6, 1, 5]
def baseStart_4031279 : Nat := 118140960795 + 4031279 * 2 ^ 59
def prefixEnd_4031279 : Nat := 4983230072969 + 3 ^ 40 * 4031279 * 2
def baseEnd_4031279 : Nat := 2069983779376438336072991

theorem tailTrace_4031279 : CollatzResearch.WordTrace tailWord_4031279 prefixEnd_4031279 2069983779376438336072991 := by
  unfold tailWord_4031279
  simp only [CollatzResearch.WordTrace]
  refine ⟨147032824362372145485008891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98021882908248096990005927 147032824362372145485008891)
  ·
    refine ⟨220549236543558218227513337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147032824362372145485008891 220549236543558218227513337)
    ·
      refine ⟨165411927407668663670635003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 220549236543558218227513337 165411927407668663670635003)
      ·
        refine ⟨248117891111502995505952505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 165411927407668663670635003 248117891111502995505952505)
        ·
          refine ⟨186088418333627246629464379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 248117891111502995505952505 186088418333627246629464379)
          ·
            refine ⟨279132627500440869944196569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 186088418333627246629464379 279132627500440869944196569)
            ·
              refine ⟨209349470625330652458147427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 279132627500440869944196569 209349470625330652458147427)
              ·
                refine ⟨314024205937995978687221141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 209349470625330652458147427 314024205937995978687221141)
                ·
                  refine ⟨14719884653343561500963491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 314024205937995978687221141 14719884653343561500963491)
                  ·
                    refine ⟨22079826980015342251445237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14719884653343561500963491 22079826980015342251445237)
                    ·
                      refine ⟨2069983779376438336072991, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 22079826980015342251445237 2069983779376438336072991)
                      ·
                        rfl

theorem cell23_4031279_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 2, 1, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 2, 1, 6, 1, 5].length) (baseStart_4031279 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4031279 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4031279 prefixEnd_4031279 := by exact prefixLift 4031279
  have htrace : WordTrace (prefixWord ++ tailWord_4031279) baseStart_4031279 baseEnd_4031279 := by
    simpa [prefixWord, tailWord_4031279, baseEnd_4031279] using wordTrace_append hprefix tailTrace_4031279
  have hstable : (prefixWord ++ tailWord_4031279).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4031279).length < 2 ^ (prefixWord ++ tailWord_4031279).sum := by decide
  have hdescent : baseEnd_4031279 < baseStart_4031279 := by decide
  rcases family_descends (prefixWord ++ tailWord_4031279) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4031297 : List Nat := [1, 2, 5, 3, 1, 1, 1, 1, 3, 3, 2]
def baseStart_4031297 : Nat := 118140960795 + 4031297 * 2 ^ 59
def prefixEnd_4031297 : Nat := 4983230072969 + 3 ^ 40 * 4031297 * 2
def baseEnd_4031297 : Nat := 2069993022028219265647909

theorem tailTrace_4031297 : CollatzResearch.WordTrace tailWord_4031297 prefixEnd_4031297 2069993022028219265647909 := by
  unfold tailWord_4031297
  simp only [CollatzResearch.WordTrace]
  refine ⟨147033480876306934559164145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98022320584204623039442763 147033480876306934559164145)
  ·
    refine ⟨110275110657230200919373109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 147033480876306934559164145 110275110657230200919373109)
    ·
      refine ⟨10338291624115331336191229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 110275110657230200919373109 10338291624115331336191229)
      ·
        refine ⟨3876859359043249251071711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10338291624115331336191229 3876859359043249251071711)
        ·
          refine ⟨5815289038564873876607567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3876859359043249251071711 5815289038564873876607567)
          ·
            refine ⟨8722933557847310814911351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5815289038564873876607567 8722933557847310814911351)
            ·
              refine ⟨13084400336770966222367027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8722933557847310814911351 13084400336770966222367027)
              ·
                refine ⟨19626600505156449333550541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13084400336770966222367027 19626600505156449333550541)
                ·
                  refine ⟨7359975189433668500081453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19626600505156449333550541 7359975189433668500081453)
                  ·
                    refine ⟨2759990696037625687530545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7359975189433668500081453 2759990696037625687530545)
                    ·
                      refine ⟨2069993022028219265647909, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2759990696037625687530545 2069993022028219265647909)
                      ·
                        rfl

theorem cell23_4031297_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 3, 1, 1, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 3, 1, 1, 1, 1, 3, 3, 2].length) (baseStart_4031297 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4031297 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4031297 prefixEnd_4031297 := by exact prefixLift 4031297
  have htrace : WordTrace (prefixWord ++ tailWord_4031297) baseStart_4031297 baseEnd_4031297 := by
    simpa [prefixWord, tailWord_4031297, baseEnd_4031297] using wordTrace_append hprefix tailTrace_4031297
  have hstable : (prefixWord ++ tailWord_4031297).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4031297).length < 2 ^ (prefixWord ++ tailWord_4031297).sum := by decide
  have hdescent : baseEnd_4031297 < baseStart_4031297 := by decide
  rcases family_descends (prefixWord ++ tailWord_4031297) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4031299 : List Nat := [1, 1, 1, 3, 1, 4, 2, 1, 9]
def baseStart_4031299 : Nat := 118140960795 + 4031299 * 2 ^ 59
def prefixEnd_4031299 : Nat := 4983230072969 + 3 ^ 40 * 4031299 * 2
def baseEnd_4031299 : Nat := 229999338776614250869211

theorem tailTrace_4031299 : CollatzResearch.WordTrace tailWord_4031299 prefixEnd_4031299 229999338776614250869211 := by
  unfold tailWord_4031299
  simp only [CollatzResearch.WordTrace]
  refine ⟨147033553822299688900736951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98022369214866459267157967 147033553822299688900736951)
  ·
    refine ⟨220550330733449533351105427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147033553822299688900736951 220550330733449533351105427)
    ·
      refine ⟨330825496100174300026658141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 220550330733449533351105427 330825496100174300026658141)
      ·
        refine ⟨124059561037565362509996803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 330825496100174300026658141 124059561037565362509996803)
        ·
          refine ⟨186089341556348043764995205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 124059561037565362509996803 186089341556348043764995205)
          ·
            refine ⟨34891751541815258205936601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 186089341556348043764995205 34891751541815258205936601)
            ·
              refine ⟨26168813656361443654452451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34891751541815258205936601 26168813656361443654452451)
              ·
                refine ⟨39253220484542165481678677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26168813656361443654452451 39253220484542165481678677)
                ·
                  refine ⟨229999338776614250869211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 39253220484542165481678677 229999338776614250869211)
                  ·
                    rfl

theorem cell23_4031299_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 2, 1, 9].length) (baseStart_4031299 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4031299 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4031299 prefixEnd_4031299 := by exact prefixLift 4031299
  have htrace : WordTrace (prefixWord ++ tailWord_4031299) baseStart_4031299 baseEnd_4031299 := by
    simpa [prefixWord, tailWord_4031299, baseEnd_4031299] using wordTrace_append hprefix tailTrace_4031299
  have hstable : (prefixWord ++ tailWord_4031299).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4031299).length < 2 ^ (prefixWord ++ tailWord_4031299).sum := by decide
  have hdescent : baseEnd_4031299 < baseStart_4031299 := by decide
  rcases family_descends (prefixWord ++ tailWord_4031299) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4031346 : List Nat := [3, 2, 1, 2, 1, 1, 2, 2, 4, 5]
def baseStart_4031346 : Nat := 118140960795 + 4031346 * 2 ^ 59
def prefixEnd_4031346 : Nat := 4983230072969 + 3 ^ 40 * 4031346 * 2
def baseEnd_4031346 : Nat := 690006060860096524645061

theorem tailTrace_4031346 : CollatzResearch.WordTrace tailWord_4031346 prefixEnd_4031346 690006060860096524645061 := by
  unfold tailWord_4031346
  simp only [CollatzResearch.WordTrace]
  refine ⟨36758817013282353981924473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 98023512035419610618465261 36758817013282353981924473)
  ·
    refine ⟨27569112759961765486443355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36758817013282353981924473 27569112759961765486443355)
    ·
      refine ⟨41353669139942648229665033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27569112759961765486443355 41353669139942648229665033)
      ·
        refine ⟨31015251854956986172248775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41353669139942648229665033 31015251854956986172248775)
        ·
          refine ⟨46522877782435479258373163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31015251854956986172248775 46522877782435479258373163)
          ·
            refine ⟨69784316673653218887559745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46522877782435479258373163 69784316673653218887559745)
            ·
              refine ⟨52338237505239914165669809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 69784316673653218887559745 52338237505239914165669809)
              ·
                refine ⟨39253678128929935624252357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 52338237505239914165669809 39253678128929935624252357)
                ·
                  refine ⟨7360064649174362929547317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 39253678128929935624252357 7360064649174362929547317)
                  ·
                    refine ⟨690006060860096524645061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7360064649174362929547317 690006060860096524645061)
                    ·
                      rfl

theorem cell23_4031346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 2, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 2, 2, 4, 5].length) (baseStart_4031346 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4031346 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4031346 prefixEnd_4031346 := by exact prefixLift 4031346
  have htrace : WordTrace (prefixWord ++ tailWord_4031346) baseStart_4031346 baseEnd_4031346 := by
    simpa [prefixWord, tailWord_4031346, baseEnd_4031346] using wordTrace_append hprefix tailTrace_4031346
  have hstable : (prefixWord ++ tailWord_4031346).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4031346).length < 2 ^ (prefixWord ++ tailWord_4031346).sum := by decide
  have hdescent : baseEnd_4031346 < baseStart_4031346 := by decide
  rcases family_descends (prefixWord ++ tailWord_4031346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4031383 : List Nat := [1, 1, 3, 3, 1, 2, 1, 1, 4, 4, 2]
def baseStart_4031383 : Nat := 118140960795 + 4031383 * 2 ^ 59
def prefixEnd_4031383 : Nat := 4983230072969 + 3 ^ 40 * 4031383 * 2
def baseEnd_4031383 : Nat := 2070037181364505929172513

theorem tailTrace_4031383 : CollatzResearch.WordTrace tailWord_4031383 prefixEnd_4031383 2070037181364505929172513 := by
  unfold tailWord_4031383
  simp only [CollatzResearch.WordTrace]
  refine ⟨147036617553995371246794803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98024411702663580831196535 147036617553995371246794803)
  ·
    refine ⟨220554926330993056870192205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147036617553995371246794803 220554926330993056870192205)
    ·
      refine ⟨82708097374122396326322077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 220554926330993056870192205 82708097374122396326322077)
      ·
        refine ⟨31015536515295898622370779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 82708097374122396326322077 31015536515295898622370779)
        ·
          refine ⟨46523304772943847933556169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31015536515295898622370779 46523304772943847933556169)
          ·
            refine ⟨34892478579707885950167127, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46523304772943847933556169 34892478579707885950167127)
            ·
              refine ⟨52338717869561828925250691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34892478579707885950167127 52338717869561828925250691)
              ·
                refine ⟨78508076804342743387876037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52338717869561828925250691 78508076804342743387876037)
                ·
                  refine ⟨14720264400814264385226757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 78508076804342743387876037 14720264400814264385226757)
                  ·
                    refine ⟨2760049575152674572230017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 14720264400814264385226757 2760049575152674572230017)
                    ·
                      refine ⟨2070037181364505929172513, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2760049575152674572230017 2070037181364505929172513)
                      ·
                        rfl

theorem cell23_4031383_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 1, 1, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 1, 1, 4, 4, 2].length) (baseStart_4031383 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4031383 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4031383 prefixEnd_4031383 := by exact prefixLift 4031383
  have htrace : WordTrace (prefixWord ++ tailWord_4031383) baseStart_4031383 baseEnd_4031383 := by
    simpa [prefixWord, tailWord_4031383, baseEnd_4031383] using wordTrace_append hprefix tailTrace_4031383
  have hstable : (prefixWord ++ tailWord_4031383).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4031383).length < 2 ^ (prefixWord ++ tailWord_4031383).sum := by decide
  have hdescent : baseEnd_4031383 < baseStart_4031383 := by decide
  rcases family_descends (prefixWord ++ tailWord_4031383) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4031396 : List Nat := [2, 3, 1, 2, 1, 2, 1, 2, 2, 1, 6]
def baseStart_4031396 : Nat := 118140960795 + 4031396 * 2 ^ 59
def prefixEnd_4031396 : Nat := 4983230072969 + 3 ^ 40 * 4031396 * 2
def baseEnd_4031396 : Nat := 2070043856613014378309953

theorem tailTrace_4031396 : CollatzResearch.WordTrace tailWord_4031396 prefixEnd_4031396 2070043856613014378309953 := by
  unfold tailWord_4031396
  simp only [CollatzResearch.WordTrace]
  refine ⟨73518545851474137233509021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98024727801965516311345361 73518545851474137233509021)
  ·
    refine ⟨27569454694302801462565883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 73518545851474137233509021 27569454694302801462565883)
    ·
      refine ⟨41354182041454202193848825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27569454694302801462565883 41354182041454202193848825)
      ·
        refine ⟨31015636531090651645386619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41354182041454202193848825 31015636531090651645386619)
        ·
          refine ⟨46523454796635977468079929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31015636531090651645386619 46523454796635977468079929)
          ·
            refine ⟨34892591097476983101059947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46523454796635977468079929 34892591097476983101059947)
            ·
              refine ⟨52338886646215474651589921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34892591097476983101059947 52338886646215474651589921)
              ·
                refine ⟨39254164984661605988692441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 52338886646215474651589921 39254164984661605988692441)
                ·
                  refine ⟨29440623738496204491519331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 39254164984661605988692441 29440623738496204491519331)
                  ·
                    refine ⟨44160935607744306737278997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 29440623738496204491519331 44160935607744306737278997)
                    ·
                      refine ⟨2070043856613014378309953, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 44160935607744306737278997 2070043856613014378309953)
                      ·
                        rfl

theorem cell23_4031396_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 1, 2, 2, 1, 6].length) (baseStart_4031396 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4031396 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4031396 prefixEnd_4031396 := by exact prefixLift 4031396
  have htrace : WordTrace (prefixWord ++ tailWord_4031396) baseStart_4031396 baseEnd_4031396 := by
    simpa [prefixWord, tailWord_4031396, baseEnd_4031396] using wordTrace_append hprefix tailTrace_4031396
  have hstable : (prefixWord ++ tailWord_4031396).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4031396).length < 2 ^ (prefixWord ++ tailWord_4031396).sum := by decide
  have hdescent : baseEnd_4031396 < baseStart_4031396 := by decide
  rcases family_descends (prefixWord ++ tailWord_4031396) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4031444 : List Nat := [2, 4, 1, 2, 1, 3, 3, 2, 1, 4]
def baseStart_4031444 : Nat := 118140960795 + 4031444 * 2 ^ 59
def prefixEnd_4031444 : Nat := 4983230072969 + 3 ^ 40 * 4031444 * 2
def baseEnd_4031444 : Nat := 690022834561476730169911

theorem tailTrace_4031444 : CollatzResearch.WordTrace tailWord_4031444 prefixEnd_4031444 690022834561476730169911 := by
  unfold tailWord_4031444
  simp only [CollatzResearch.WordTrace]
  refine ⟨73519421203387189332382693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98025894937849585776510257 73519421203387189332382693)
  ·
    refine ⟨13784891475635097999821755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 73519421203387189332382693 13784891475635097999821755)
    ·
      refine ⟨20677337213452646999732633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13784891475635097999821755 20677337213452646999732633)
      ·
        refine ⟨15508002910089485249799475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20677337213452646999732633 15508002910089485249799475)
        ·
          refine ⟨23262004365134227874699213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15508002910089485249799475 23262004365134227874699213)
          ·
            refine ⟨8723251636925335453012205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23262004365134227874699213 8723251636925335453012205)
            ·
              refine ⟨3271219363847000794879577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8723251636925335453012205 3271219363847000794879577)
              ·
                refine ⟨2453414522885250596159683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3271219363847000794879577 2453414522885250596159683)
                ·
                  refine ⟨3680121784327875894239525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2453414522885250596159683 3680121784327875894239525)
                  ·
                    refine ⟨690022834561476730169911, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3680121784327875894239525 690022834561476730169911)
                    ·
                      rfl

theorem cell23_4031444_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 3, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 3, 3, 2, 1, 4].length) (baseStart_4031444 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4031444 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4031444 prefixEnd_4031444 := by exact prefixLift 4031444
  have htrace : WordTrace (prefixWord ++ tailWord_4031444) baseStart_4031444 baseEnd_4031444 := by
    simpa [prefixWord, tailWord_4031444, baseEnd_4031444] using wordTrace_append hprefix tailTrace_4031444
  have hstable : (prefixWord ++ tailWord_4031444).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4031444).length < 2 ^ (prefixWord ++ tailWord_4031444).sum := by decide
  have hdescent : baseEnd_4031444 < baseStart_4031444 := by decide
  rcases family_descends (prefixWord ++ tailWord_4031444) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4031456 : List Nat := [2, 1, 1, 3, 1, 1, 1, 1, 1, 7, 4]
def baseStart_4031456 : Nat := 118140960795 + 4031456 * 2 ^ 59
def prefixEnd_4031456 : Nat := 4983230072969 + 3 ^ 40 * 4031456 * 2
def baseEnd_4031456 : Nat := 2070074665452284143559677

theorem tailTrace_4031456 : CollatzResearch.WordTrace tailWord_4031456 prefixEnd_4031456 2070074665452284143559677 := by
  unfold tailWord_4031456
  simp only [CollatzResearch.WordTrace]
  refine ⟨73519640041365452357101111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98026186721820603142801481 73519640041365452357101111)
  ·
    refine ⟨110279460062048178535651667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73519640041365452357101111 110279460062048178535651667)
    ·
      refine ⟨165419190093072267803477501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110279460062048178535651667 165419190093072267803477501)
      ·
        refine ⟨62032196284902100426304063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 165419190093072267803477501 62032196284902100426304063)
        ·
          refine ⟨93048294427353150639456095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62032196284902100426304063 93048294427353150639456095)
          ·
            refine ⟨139572441641029725959184143, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 93048294427353150639456095 139572441641029725959184143)
            ·
              refine ⟨209358662461544588938776215, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 139572441641029725959184143 209358662461544588938776215)
              ·
                refine ⟨314037993692316883408164323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 209358662461544588938776215 314037993692316883408164323)
                ·
                  refine ⟨471056990538475325112246485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 314037993692316883408164323 471056990538475325112246485)
                  ·
                    refine ⟨11040398215745515432318277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 471056990538475325112246485 11040398215745515432318277)
                    ·
                      refine ⟨2070074665452284143559677, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11040398215745515432318277 2070074665452284143559677)
                      ·
                        rfl

theorem cell23_4031456_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 1, 1, 1, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 1, 1, 1, 7, 4].length) (baseStart_4031456 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4031456 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4031456 prefixEnd_4031456 := by exact prefixLift 4031456
  have htrace : WordTrace (prefixWord ++ tailWord_4031456) baseStart_4031456 baseEnd_4031456 := by
    simpa [prefixWord, tailWord_4031456, baseEnd_4031456] using wordTrace_append hprefix tailTrace_4031456
  have hstable : (prefixWord ++ tailWord_4031456).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4031456).length < 2 ^ (prefixWord ++ tailWord_4031456).sum := by decide
  have hdescent : baseEnd_4031456 < baseStart_4031456 := by decide
  rcases family_descends (prefixWord ++ tailWord_4031456) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4031470 : List Nat := [4, 1, 2, 1, 4, 1, 1, 1, 3, 5]
def baseStart_4031470 : Nat := 118140960795 + 4031470 * 2 ^ 59
def prefixEnd_4031470 : Nat := 4983230072969 + 3 ^ 40 * 4031470 * 2
def baseEnd_4031470 : Nat := 690027284727149029594871

theorem tailTrace_4031470 : CollatzResearch.WordTrace tailWord_4031470 prefixEnd_4031470 690027284727149029594871 := by
  unfold tailWord_4031470
  simp only [CollatzResearch.WordTrace]
  refine ⟨18379973838085023138151483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 98026527136453456736807909 18379973838085023138151483)
  ·
    refine ⟨27569960757127534707227225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18379973838085023138151483 27569960757127534707227225)
    ·
      refine ⟨20677470567845651030420419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27569960757127534707227225 20677470567845651030420419)
      ·
        refine ⟨31016205851768476545630629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20677470567845651030420419 31016205851768476545630629)
        ·
          refine ⟨5815538597206589352305743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 31016205851768476545630629 5815538597206589352305743)
          ·
            refine ⟨8723307895809884028458615, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5815538597206589352305743 8723307895809884028458615)
            ·
              refine ⟨13084961843714826042687923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8723307895809884028458615 13084961843714826042687923)
              ·
                refine ⟨19627442765572239064031885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13084961843714826042687923 19627442765572239064031885)
                ·
                  refine ⟨7360291037089589649011957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19627442765572239064031885 7360291037089589649011957)
                  ·
                    refine ⟨690027284727149029594871, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7360291037089589649011957 690027284727149029594871)
                    ·
                      rfl

theorem cell23_4031470_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 4, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 4, 1, 1, 1, 3, 5].length) (baseStart_4031470 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4031470 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4031470 prefixEnd_4031470 := by exact prefixLift 4031470
  have htrace : WordTrace (prefixWord ++ tailWord_4031470) baseStart_4031470 baseEnd_4031470 := by
    simpa [prefixWord, tailWord_4031470, baseEnd_4031470] using wordTrace_append hprefix tailTrace_4031470
  have hstable : (prefixWord ++ tailWord_4031470).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4031470).length < 2 ^ (prefixWord ++ tailWord_4031470).sum := by decide
  have hdescent : baseEnd_4031470 < baseStart_4031470 := by decide
  rcases family_descends (prefixWord ++ tailWord_4031470) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4031496 : List Nat := [2, 1, 3, 2, 1, 14]
def baseStart_4031496 : Nat := 118140960795 + 4031496 * 2 ^ 59
def prefixEnd_4031496 : Nat := 4983230072969 + 3 ^ 40 * 4031496 * 2
def baseEnd_4031496 : Nat := 8518910307318781839751

theorem tailTrace_4031496 : CollatzResearch.WordTrace tailWord_4031496 prefixEnd_4031496 8518910307318781839751 := by
  unfold tailWord_4031496
  simp only [CollatzResearch.WordTrace]
  refine ⟨73520369501292995772829171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98027159335057327697105561 73520369501292995772829171)
  ·
    refine ⟨110280554251939493659243757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73520369501292995772829171 110280554251939493659243757)
    ·
      refine ⟨41355207844477310122216409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 110280554251939493659243757 41355207844477310122216409)
      ·
        refine ⟨31016405883357982591662307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41355207844477310122216409 31016405883357982591662307)
        ·
          refine ⟨46524608825036973887493461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31016405883357982591662307 46524608825036973887493461)
          ·
            refine ⟨8518910307318781839751, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 14 46524608825036973887493461 8518910307318781839751)
            ·
              rfl

theorem cell23_4031496_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 14].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 14].length) (baseStart_4031496 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4031496 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4031496 prefixEnd_4031496 := by exact prefixLift 4031496
  have htrace : WordTrace (prefixWord ++ tailWord_4031496) baseStart_4031496 baseEnd_4031496 := by
    simpa [prefixWord, tailWord_4031496, baseEnd_4031496] using wordTrace_append hprefix tailTrace_4031496
  have hstable : (prefixWord ++ tailWord_4031496).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4031496).length < 2 ^ (prefixWord ++ tailWord_4031496).sum := by decide
  have hdescent : baseEnd_4031496 < baseStart_4031496 := by decide
  rcases family_descends (prefixWord ++ tailWord_4031496) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4031500 : List Nat := [2, 2, 1, 2, 3, 2, 1, 4, 2, 4]
def baseStart_4031500 : Nat := 118140960795 + 4031500 * 2 ^ 59
def prefixEnd_4031500 : Nat := 4983230072969 + 3 ^ 40 * 4031500 * 2
def baseEnd_4031500 : Nat := 690032419533693990469825

theorem tailTrace_4031500 : CollatzResearch.WordTrace tailWord_4031500 prefixEnd_4031500 690032419533693990469825 := by
  unfold tailWord_4031500
  simp only [CollatzResearch.WordTrace]
  refine ⟨73520442447285750114401977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98027256596381000152535969 73520442447285750114401977)
  ·
    refine ⟨55140331835464312585801483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73520442447285750114401977 55140331835464312585801483)
    ·
      refine ⟨82710497753196468878702225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55140331835464312585801483 82710497753196468878702225)
      ·
        refine ⟨62032873314897351659026669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 82710497753196468878702225 62032873314897351659026669)
        ·
          refine ⟨23262327493086506872135001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 62032873314897351659026669 23262327493086506872135001)
          ·
            refine ⟨17446745619814880154101251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23262327493086506872135001 17446745619814880154101251)
            ·
              refine ⟨26170118429722320231151877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17446745619814880154101251 26170118429722320231151877)
              ·
                refine ⟨4906897205572935043340977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 26170118429722320231151877 4906897205572935043340977)
                ·
                  refine ⟨3680172904179701282505733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4906897205572935043340977 3680172904179701282505733)
                  ·
                    refine ⟨690032419533693990469825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3680172904179701282505733 690032419533693990469825)
                    ·
                      rfl

theorem cell23_4031500_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 2, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 2, 1, 4, 2, 4].length) (baseStart_4031500 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4031500 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4031500 prefixEnd_4031500 := by exact prefixLift 4031500
  have htrace : WordTrace (prefixWord ++ tailWord_4031500) baseStart_4031500 baseEnd_4031500 := by
    simpa [prefixWord, tailWord_4031500, baseEnd_4031500] using wordTrace_append hprefix tailTrace_4031500
  have hstable : (prefixWord ++ tailWord_4031500).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4031500).length < 2 ^ (prefixWord ++ tailWord_4031500).sum := by decide
  have hdescent : baseEnd_4031500 < baseStart_4031500 := by decide
  rcases family_descends (prefixWord ++ tailWord_4031500) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4031524 : List Nat := [2, 3, 1, 4, 1, 2, 1, 2, 3, 2, 2]
def baseStart_4031524 : Nat := 118140960795 + 4031524 * 2 ^ 59
def prefixEnd_4031524 : Nat := 4983230072969 + 3 ^ 40 * 4031524 * 2
def baseEnd_4031524 : Nat := 2070109582136789877509365

theorem tailTrace_4031524 : CollatzResearch.WordTrace tailWord_4031524 prefixEnd_4031524 2070109582136789877509365 := by
  unfold tailWord_4031524
  simp only [CollatzResearch.WordTrace]
  refine ⟨73520880123242276163838813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98027840164323034885118417 73520880123242276163838813)
  ·
    refine ⟨27570330046215853561439555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 73520880123242276163838813 27570330046215853561439555)
    ·
      refine ⟨41355495069323780342159333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27570330046215853561439555 41355495069323780342159333)
      ·
        refine ⟨7754155325498208814154875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 41355495069323780342159333 7754155325498208814154875)
        ·
          refine ⟨11631232988247313221232313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7754155325498208814154875 11631232988247313221232313)
          ·
            refine ⟨8723424741185484915924235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11631232988247313221232313 8723424741185484915924235)
            ·
              refine ⟨13085137111778227373886353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8723424741185484915924235 13085137111778227373886353)
              ·
                refine ⟨9813852833833670530414765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13085137111778227373886353 9813852833833670530414765)
                ·
                  refine ⟨3680194812687626448905537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9813852833833670530414765 3680194812687626448905537)
                  ·
                    refine ⟨2760146109515719836679153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3680194812687626448905537 2760146109515719836679153)
                    ·
                      refine ⟨2070109582136789877509365, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2760146109515719836679153 2070109582136789877509365)
                      ·
                        rfl

theorem cell23_4031524_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 2, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 2, 1, 2, 3, 2, 2].length) (baseStart_4031524 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4031524 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4031524 prefixEnd_4031524 := by exact prefixLift 4031524
  have htrace : WordTrace (prefixWord ++ tailWord_4031524) baseStart_4031524 baseEnd_4031524 := by
    simpa [prefixWord, tailWord_4031524, baseEnd_4031524] using wordTrace_append hprefix tailTrace_4031524
  have hstable : (prefixWord ++ tailWord_4031524).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4031524).length < 2 ^ (prefixWord ++ tailWord_4031524).sum := by decide
  have hdescent : baseEnd_4031524 < baseStart_4031524 := by decide
  rcases family_descends (prefixWord ++ tailWord_4031524) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4031527 : List Nat := [1, 1, 7, 1, 1, 1, 2, 1, 3, 2, 3]
def baseStart_4031527 : Nat := 118140960795 + 4031527 * 2 ^ 59
def prefixEnd_4031527 : Nat := 4983230072969 + 3 ^ 40 * 4031527 * 2
def baseEnd_4031527 : Nat := 2070111122578753365771851

theorem tailTrace_4031527 : CollatzResearch.WordTrace tailWord_4031527 prefixEnd_4031527 2070111122578753365771851 := by
  unfold tailWord_4031527
  simp only [CollatzResearch.WordTrace]
  refine ⟨147041869665473683840036835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98027913110315789226691223 147041869665473683840036835)
  ·
    refine ⟨220562804498210525760055253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147041869665473683840036835 220562804498210525760055253)
    ·
      refine ⟨5169440730426809197501295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 220562804498210525760055253 5169440730426809197501295)
      ·
        refine ⟨7754161095640213796251943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5169440730426809197501295 7754161095640213796251943)
        ·
          refine ⟨11631241643460320694377915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7754161095640213796251943 11631241643460320694377915)
          ·
            refine ⟨17446862465190481041566873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11631241643460320694377915 17446862465190481041566873)
            ·
              refine ⟨13085146848892860781175155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17446862465190481041566873 13085146848892860781175155)
              ·
                refine ⟨19627720273339291171762733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13085146848892860781175155 19627720273339291171762733)
                ·
                  refine ⟨7360395102502234189411025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19627720273339291171762733 7360395102502234189411025)
                  ·
                    refine ⟨5520296326876675642058269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7360395102502234189411025 5520296326876675642058269)
                    ·
                      refine ⟨2070111122578753365771851, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5520296326876675642058269 2070111122578753365771851)
                      ·
                        rfl

theorem cell23_4031527_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 1, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 1, 2, 1, 3, 2, 3].length) (baseStart_4031527 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4031527 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4031527 prefixEnd_4031527 := by exact prefixLift 4031527
  have htrace : WordTrace (prefixWord ++ tailWord_4031527) baseStart_4031527 baseEnd_4031527 := by
    simpa [prefixWord, tailWord_4031527, baseEnd_4031527] using wordTrace_append hprefix tailTrace_4031527
  have hstable : (prefixWord ++ tailWord_4031527).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4031527).length < 2 ^ (prefixWord ++ tailWord_4031527).sum := by decide
  have hdescent : baseEnd_4031527 < baseStart_4031527 := by decide
  rcases family_descends (prefixWord ++ tailWord_4031527) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4031544 : List Nat := [2, 1, 2, 1, 5, 3, 2, 1, 1, 2, 3]
def baseStart_4031544 : Nat := 118140960795 + 4031544 * 2 ^ 59
def prefixEnd_4031544 : Nat := 4983230072969 + 3 ^ 40 * 4031544 * 2
def baseEnd_4031544 : Nat := 2070119851749879799259273

theorem tailTrace_4031544 : CollatzResearch.WordTrace tailWord_4031544 prefixEnd_4031544 2070119851749879799259273 := by
  unfold tailWord_4031544
  simp only [CollatzResearch.WordTrace]
  refine ⟨73521244853206047871702843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98028326470941397162270457 73521244853206047871702843)
  ·
    refine ⟨110281867279809071807554265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73521244853206047871702843 110281867279809071807554265)
    ·
      refine ⟨82711400459856803855665699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 110281867279809071807554265 82711400459856803855665699)
      ·
        refine ⟨124067100689785205783498549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82711400459856803855665699 124067100689785205783498549)
        ·
          refine ⟨11631290689667363042202989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 124067100689785205783498549 11631290689667363042202989)
          ·
            refine ⟨4361734008625261140826121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11631290689667363042202989 4361734008625261140826121)
            ·
              refine ⟨3271300506468945855619591, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4361734008625261140826121 3271300506468945855619591)
              ·
                refine ⟨4906950759703418783429387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3271300506468945855619591 4906950759703418783429387)
                ·
                  refine ⟨7360426139555128175144081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4906950759703418783429387 7360426139555128175144081)
                  ·
                    refine ⟨5520319604666346131358061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7360426139555128175144081 5520319604666346131358061)
                    ·
                      refine ⟨2070119851749879799259273, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5520319604666346131358061 2070119851749879799259273)
                      ·
                        rfl

theorem cell23_4031544_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 3, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 3, 2, 1, 1, 2, 3].length) (baseStart_4031544 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4031544 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4031544 prefixEnd_4031544 := by exact prefixLift 4031544
  have htrace : WordTrace (prefixWord ++ tailWord_4031544) baseStart_4031544 baseEnd_4031544 := by
    simpa [prefixWord, tailWord_4031544, baseEnd_4031544] using wordTrace_append hprefix tailTrace_4031544
  have hstable : (prefixWord ++ tailWord_4031544).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4031544).length < 2 ^ (prefixWord ++ tailWord_4031544).sum := by decide
  have hdescent : baseEnd_4031544 < baseStart_4031544 := by decide
  rcases family_descends (prefixWord ++ tailWord_4031544) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4031557 : List Nat := [1, 3, 1, 1, 1, 3, 5, 2, 2, 1, 3]
def baseStart_4031557 : Nat := 118140960795 + 4031557 * 2 ^ 59
def prefixEnd_4031557 : Nat := 4983230072969 + 3 ^ 40 * 4031557 * 2
def baseEnd_4031557 : Nat := 2070126526998388248396713

theorem tailTrace_4031557 : CollatzResearch.WordTrace tailWord_4031557 prefixEnd_4031557 2070126526998388248396713 := by
  unfold tailWord_4031557
  simp only [CollatzResearch.WordTrace]
  refine ⟨147042963855364998963628925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98028642570243332642419283 147042963855364998963628925)
  ·
    refine ⟨55141111445761874611360847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 147042963855364998963628925 55141111445761874611360847)
    ·
      refine ⟨82711667168642811917041271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55141111445761874611360847 82711667168642811917041271)
      ·
        refine ⟨124067500752964217875561907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82711667168642811917041271 124067500752964217875561907)
        ·
          refine ⟨186101251129446326813342861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 124067500752964217875561907 186101251129446326813342861)
          ·
            refine ⟨69787969173542372555003573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 186101251129446326813342861 69787969173542372555003573)
            ·
              refine ⟨6542622110019597427031585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 69787969173542372555003573 6542622110019597427031585)
              ·
                refine ⟨4906966582514698070273689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6542622110019597427031585 4906966582514698070273689)
                ·
                  refine ⟨3680224936886023552705267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4906966582514698070273689 3680224936886023552705267)
                  ·
                    refine ⟨5520337405329035329057901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3680224936886023552705267 5520337405329035329057901)
                    ·
                      refine ⟨2070126526998388248396713, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5520337405329035329057901 2070126526998388248396713)
                      ·
                        rfl

theorem cell23_4031557_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 5, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 5, 2, 2, 1, 3].length) (baseStart_4031557 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4031557 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4031557 prefixEnd_4031557 := by exact prefixLift 4031557
  have htrace : WordTrace (prefixWord ++ tailWord_4031557) baseStart_4031557 baseEnd_4031557 := by
    simpa [prefixWord, tailWord_4031557, baseEnd_4031557] using wordTrace_append hprefix tailTrace_4031557
  have hstable : (prefixWord ++ tailWord_4031557).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4031557).length < 2 ^ (prefixWord ++ tailWord_4031557).sum := by decide
  have hdescent : baseEnd_4031557 < baseStart_4031557 := by decide
  rcases family_descends (prefixWord ++ tailWord_4031557) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4031558 : List Nat := [6, 1, 1, 1, 1, 2, 2, 4, 1, 2, 2]
def baseStart_4031558 : Nat := 118140960795 + 4031558 * 2 ^ 59
def prefixEnd_4031558 : Nat := 4983230072969 + 3 ^ 40 * 4031558 * 2
def baseEnd_4031558 : Nat := 2070127040479042744484209

theorem tailTrace_4031558 : CollatzResearch.WordTrace tailWord_4031558 prefixEnd_4031558 2070127040479042744484209 := by
  unfold tailWord_4031558
  simp only [CollatzResearch.WordTrace]
  refine ⟨4595093760261293004200479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 98028666885574250756276885 4595093760261293004200479)
  ·
    refine ⟨6892640640391939506300719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4595093760261293004200479 6892640640391939506300719)
    ·
      refine ⟨10338960960587909259451079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6892640640391939506300719 10338960960587909259451079)
      ·
        refine ⟨15508441440881863889176619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10338960960587909259451079 15508441440881863889176619)
        ·
          refine ⟨23262662161322795833764929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15508441440881863889176619 23262662161322795833764929)
          ·
            refine ⟨17446996620992096875323697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23262662161322795833764929 17446996620992096875323697)
            ·
              refine ⟨13085247465744072656492773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17446996620992096875323697 13085247465744072656492773)
              ·
                refine ⟨2453483899827013623092395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13085247465744072656492773 2453483899827013623092395)
                ·
                  refine ⟨3680225849740520434638593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2453483899827013623092395 3680225849740520434638593)
                  ·
                    refine ⟨2760169387305390325978945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3680225849740520434638593 2760169387305390325978945)
                    ·
                      refine ⟨2070127040479042744484209, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2760169387305390325978945 2070127040479042744484209)
                      ·
                        rfl

theorem cell23_4031558_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 2, 2, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 2, 2, 4, 1, 2, 2].length) (baseStart_4031558 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4031558 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4031558 prefixEnd_4031558 := by exact prefixLift 4031558
  have htrace : WordTrace (prefixWord ++ tailWord_4031558) baseStart_4031558 baseEnd_4031558 := by
    simpa [prefixWord, tailWord_4031558, baseEnd_4031558] using wordTrace_append hprefix tailTrace_4031558
  have hstable : (prefixWord ++ tailWord_4031558).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4031558).length < 2 ^ (prefixWord ++ tailWord_4031558).sum := by decide
  have hdescent : baseEnd_4031558 < baseStart_4031558 := by decide
  rcases family_descends (prefixWord ++ tailWord_4031558) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4031573 : List Nat := [1, 3, 2, 2, 1, 2, 1, 3, 2, 6]
def baseStart_4031573 : Nat := 118140960795 + 4031573 * 2 ^ 59
def prefixEnd_4031573 : Nat := 4983230072969 + 3 ^ 40 * 4031573 * 2
def baseEnd_4031573 : Nat := 690044914229620061932213

theorem tailTrace_4031573 : CollatzResearch.WordTrace tailWord_4031573 prefixEnd_4031573 690044914229620061932213 := by
  unfold tailWord_4031573
  simp only [CollatzResearch.WordTrace]
  refine ⟨147043547423307033696211373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98029031615538022464140915 147043547423307033696211373)
  ·
    refine ⟨55141330283740137636079265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 147043547423307033696211373 55141330283740137636079265)
    ·
      refine ⟨41355997712805103227059449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55141330283740137636079265 41355997712805103227059449)
      ·
        refine ⟨31016998284603827420294587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41355997712805103227059449 31016998284603827420294587)
        ·
          refine ⟨46525497426905741130441881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31016998284603827420294587 46525497426905741130441881)
          ·
            refine ⟨34894123070179305847831411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46525497426905741130441881 34894123070179305847831411)
            ·
              refine ⟨52341184605268958771747117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34894123070179305847831411 52341184605268958771747117)
              ·
                refine ⟨19627944226975859539405169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 52341184605268958771747117 19627944226975859539405169)
                ·
                  refine ⟨14720958170231894654553877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19627944226975859539405169 14720958170231894654553877)
                  ·
                    refine ⟨690044914229620061932213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 14720958170231894654553877 690044914229620061932213)
                    ·
                      rfl

theorem cell23_4031573_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 1, 3, 2, 6].length) (baseStart_4031573 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4031573 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4031573 prefixEnd_4031573 := by exact prefixLift 4031573
  have htrace : WordTrace (prefixWord ++ tailWord_4031573) baseStart_4031573 baseEnd_4031573 := by
    simpa [prefixWord, tailWord_4031573, baseEnd_4031573] using wordTrace_append hprefix tailTrace_4031573
  have hstable : (prefixWord ++ tailWord_4031573).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4031573).length < 2 ^ (prefixWord ++ tailWord_4031573).sum := by decide
  have hdescent : baseEnd_4031573 < baseStart_4031573 := by decide
  rcases family_descends (prefixWord ++ tailWord_4031573) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4031583 : List Nat := [1, 1, 2, 3, 1, 1, 4, 2, 2, 1, 5]
def baseStart_4031583 : Nat := 118140960795 + 4031583 * 2 ^ 59
def prefixEnd_4031583 : Nat := 4983230072969 + 3 ^ 40 * 4031583 * 2
def baseEnd_4031583 : Nat := 2070139877495405146671593

theorem tailTrace_4031583 : CollatzResearch.WordTrace tailWord_4031583 prefixEnd_4031583 2070139877495405146671593 := by
  unfold tailWord_4031583
  simp only [CollatzResearch.WordTrace]
  refine ⟨147043912153270805404075403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98029274768847203602716935 147043912153270805404075403)
  ·
    refine ⟨220565868229906208106113105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147043912153270805404075403 220565868229906208106113105)
    ·
      refine ⟨165424401172429656079584829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 220565868229906208106113105 165424401172429656079584829)
      ·
        refine ⟨62034150439661121029844311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 165424401172429656079584829 62034150439661121029844311)
        ·
          refine ⟨93051225659491681544766467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62034150439661121029844311 93051225659491681544766467)
          ·
            refine ⟨139576838489237522317149701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 93051225659491681544766467 139576838489237522317149701)
            ·
              refine ⟨26170657216732035434465569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 139576838489237522317149701 26170657216732035434465569)
              ·
                refine ⟨19627992912549026575849177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26170657216732035434465569 19627992912549026575849177)
                ·
                  refine ⟨14720994684411769931886883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19627992912549026575849177 14720994684411769931886883)
                  ·
                    refine ⟨22081492026617654897830325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14720994684411769931886883 22081492026617654897830325)
                    ·
                      refine ⟨2070139877495405146671593, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 22081492026617654897830325 2070139877495405146671593)
                      ·
                        rfl

theorem cell23_4031583_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 4, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 4, 2, 2, 1, 5].length) (baseStart_4031583 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4031583 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4031583 prefixEnd_4031583 := by exact prefixLift 4031583
  have htrace : WordTrace (prefixWord ++ tailWord_4031583) baseStart_4031583 baseEnd_4031583 := by
    simpa [prefixWord, tailWord_4031583, baseEnd_4031583] using wordTrace_append hprefix tailTrace_4031583
  have hstable : (prefixWord ++ tailWord_4031583).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4031583).length < 2 ^ (prefixWord ++ tailWord_4031583).sum := by decide
  have hdescent : baseEnd_4031583 < baseStart_4031583 := by decide
  rcases family_descends (prefixWord ++ tailWord_4031583) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4031613 : List Nat := [1, 4, 1, 1, 3, 1, 1, 1, 1, 2, 7]
def baseStart_4031613 : Nat := 118140960795 + 4031613 * 2 ^ 59
def prefixEnd_4031613 : Nat := 4983230072969 + 3 ^ 40 * 4031613 * 2
def baseEnd_4031613 : Nat := 2070155281915040029296455

theorem tailTrace_4031613 : CollatzResearch.WordTrace tailWord_4031613 prefixEnd_4031613 2070155281915040029296455 := by
  unfold tailWord_4031613
  simp only [CollatzResearch.WordTrace]
  refine ⟨147045006343162120527667493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98030004228774747018444995 147045006343162120527667493)
  ·
    refine ⟨27570938689342897598937655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 147045006343162120527667493 27570938689342897598937655)
    ·
      refine ⟨41356408034014346398406483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27570938689342897598937655 41356408034014346398406483)
      ·
        refine ⟨62034612051021519597609725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41356408034014346398406483 62034612051021519597609725)
        ·
          refine ⟨23262979519133069849103647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 62034612051021519597609725 23262979519133069849103647)
          ·
            refine ⟨34894469278699604773655471, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23262979519133069849103647 34894469278699604773655471)
            ·
              refine ⟨52341703918049407160483207, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34894469278699604773655471 52341703918049407160483207)
              ·
                refine ⟨78512555877074110740724811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52341703918049407160483207 78512555877074110740724811)
                ·
                  refine ⟨117768833815611166111087217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 78512555877074110740724811 117768833815611166111087217)
                  ·
                    refine ⟨88326625361708374583315413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 117768833815611166111087217 88326625361708374583315413)
                    ·
                      refine ⟨2070155281915040029296455, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 88326625361708374583315413 2070155281915040029296455)
                      ·
                        rfl

theorem cell23_4031613_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 1, 1, 1, 2, 7].length) (baseStart_4031613 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4031613 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4031613 prefixEnd_4031613 := by exact prefixLift 4031613
  have htrace : WordTrace (prefixWord ++ tailWord_4031613) baseStart_4031613 baseEnd_4031613 := by
    simpa [prefixWord, tailWord_4031613, baseEnd_4031613] using wordTrace_append hprefix tailTrace_4031613
  have hstable : (prefixWord ++ tailWord_4031613).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4031613).length < 2 ^ (prefixWord ++ tailWord_4031613).sum := by decide
  have hdescent : baseEnd_4031613 < baseStart_4031613 := by decide
  rcases family_descends (prefixWord ++ tailWord_4031613) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4031620 : List Nat := [2, 3, 2, 1, 2, 2, 3, 1, 7]
def baseStart_4031620 : Nat := 118140960795 + 4031620 * 2 ^ 59
def prefixEnd_4031620 : Nat := 4983230072969 + 3 ^ 40 * 4031620 * 2
def baseEnd_4031620 : Nat := 230017652919957944656547

theorem tailTrace_4031620 : CollatzResearch.WordTrace tailWord_4031620 prefixEnd_4031620 230017652919957944656547 := by
  unfold tailWord_4031620
  simp only [CollatzResearch.WordTrace]
  refine ⟨73522630827068380361586157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98030174436091173815448209 73522630827068380361586157)
  ·
    refine ⟨27570986560150642635594809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 73522630827068380361586157 27570986560150642635594809)
    ·
      refine ⟨20678239920112981976696107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27570986560150642635594809 20678239920112981976696107)
      ·
        refine ⟨31017359880169472965044161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20678239920112981976696107 31017359880169472965044161)
        ·
          refine ⟨23263019910127104723783121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31017359880169472965044161 23263019910127104723783121)
          ·
            refine ⟨17447264932595328542837341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23263019910127104723783121 17447264932595328542837341)
            ·
              refine ⟨6542724349723248203564003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17447264932595328542837341 6542724349723248203564003)
              ·
                refine ⟨9814086524584872305346005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6542724349723248203564003 9814086524584872305346005)
                ·
                  refine ⟨230017652919957944656547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 9814086524584872305346005 230017652919957944656547)
                  ·
                    rfl

theorem cell23_4031620_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 2, 3, 1, 7].length) (baseStart_4031620 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4031620 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4031620 prefixEnd_4031620 := by exact prefixLift 4031620
  have htrace : WordTrace (prefixWord ++ tailWord_4031620) baseStart_4031620 baseEnd_4031620 := by
    simpa [prefixWord, tailWord_4031620, baseEnd_4031620] using wordTrace_append hprefix tailTrace_4031620
  have hstable : (prefixWord ++ tailWord_4031620).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4031620).length < 2 ^ (prefixWord ++ tailWord_4031620).sum := by decide
  have hdescent : baseEnd_4031620 < baseStart_4031620 := by decide
  rcases family_descends (prefixWord ++ tailWord_4031620) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4031683 : List Nat := [1, 1, 1, 3, 1, 1, 1, 3, 4, 1, 6]
def baseStart_4031683 : Nat := 118140960795 + 4031683 * 2 ^ 59
def prefixEnd_4031683 : Nat := 4983230072969 + 3 ^ 40 * 4031683 * 2
def baseEnd_4031683 : Nat := 2070191225560854755421133

theorem tailTrace_4031683 : CollatzResearch.WordTrace tailWord_4031683 prefixEnd_4031683 2070191225560854755421133 := by
  unfold tailWord_4031683
  simp only [CollatzResearch.WordTrace]
  refine ⟨147047559452908522482715703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98031706301939014988477135 147047559452908522482715703)
  ·
    refine ⟨220571339179362783724073555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147047559452908522482715703 220571339179362783724073555)
    ·
      refine ⟨330857008769044175586110333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 220571339179362783724073555 330857008769044175586110333)
      ·
        refine ⟨124071378288391565844791375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 330857008769044175586110333 124071378288391565844791375)
        ·
          refine ⟨186107067432587348767187063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 124071378288391565844791375 186107067432587348767187063)
          ·
            refine ⟨279160601148881023150780595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 186107067432587348767187063 279160601148881023150780595)
            ·
              refine ⟨418740901723321534726170893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 279160601148881023150780595 418740901723321534726170893)
              ·
                refine ⟨157027838146245575522314085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 418740901723321534726170893 157027838146245575522314085)
                ·
                  refine ⟨29442719652421045410433891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 157027838146245575522314085 29442719652421045410433891)
                  ·
                    refine ⟨44164079478631568115650837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 29442719652421045410433891 44164079478631568115650837)
                    ·
                      refine ⟨2070191225560854755421133, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 44164079478631568115650837 2070191225560854755421133)
                      ·
                        rfl

theorem cell23_4031683_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 3, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 3, 4, 1, 6].length) (baseStart_4031683 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4031683 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4031683 prefixEnd_4031683 := by exact prefixLift 4031683
  have htrace : WordTrace (prefixWord ++ tailWord_4031683) baseStart_4031683 baseEnd_4031683 := by
    simpa [prefixWord, tailWord_4031683, baseEnd_4031683] using wordTrace_append hprefix tailTrace_4031683
  have hstable : (prefixWord ++ tailWord_4031683).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4031683).length < 2 ^ (prefixWord ++ tailWord_4031683).sum := by decide
  have hdescent : baseEnd_4031683 < baseStart_4031683 := by decide
  rcases family_descends (prefixWord ++ tailWord_4031683) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4031704 : List Nat := [2, 1, 2, 2, 5, 2, 1, 1, 2, 1, 4]
def baseStart_4031704 : Nat := 118140960795 + 4031704 * 2 ^ 59
def prefixEnd_4031704 : Nat := 4983230072969 + 3 ^ 40 * 4031704 * 2
def baseEnd_4031704 : Nat := 2070202008654599173258537

theorem tailTrace_4031704 : CollatzResearch.WordTrace tailWord_4031704 prefixEnd_4031704 2070202008654599173258537 := by
  unfold tailWord_4031704
  simp only [CollatzResearch.WordTrace]
  refine ⟨73524162692916221534615083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98032216923888295379486777 73524162692916221534615083)
  ·
    refine ⟨110286244039374332301922625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73524162692916221534615083 110286244039374332301922625)
    ·
      refine ⟨82714683029530749226441969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 110286244039374332301922625 82714683029530749226441969)
      ·
        refine ⟨62036012272148061919831477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 82714683029530749226441969 62036012272148061919831477)
        ·
          refine ⟨5815876150513880804984201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 62036012272148061919831477 5815876150513880804984201)
          ·
            refine ⟨4361907112885410603738151, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5815876150513880804984201 4361907112885410603738151)
            ·
              refine ⟨6542860669328115905607227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4361907112885410603738151 6542860669328115905607227)
              ·
                refine ⟨9814291003992173858410841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6542860669328115905607227 9814291003992173858410841)
                ·
                  refine ⟨7360718252994130393808131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9814291003992173858410841 7360718252994130393808131)
                  ·
                    refine ⟨11041077379491195590712197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7360718252994130393808131 11041077379491195590712197)
                    ·
                      refine ⟨2070202008654599173258537, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11041077379491195590712197 2070202008654599173258537)
                      ·
                        rfl

theorem cell23_4031704_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 5, 2, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 5, 2, 1, 1, 2, 1, 4].length) (baseStart_4031704 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4031704 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4031704 prefixEnd_4031704 := by exact prefixLift 4031704
  have htrace : WordTrace (prefixWord ++ tailWord_4031704) baseStart_4031704 baseEnd_4031704 := by
    simpa [prefixWord, tailWord_4031704, baseEnd_4031704] using wordTrace_append hprefix tailTrace_4031704
  have hstable : (prefixWord ++ tailWord_4031704).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4031704).length < 2 ^ (prefixWord ++ tailWord_4031704).sum := by decide
  have hdescent : baseEnd_4031704 < baseStart_4031704 := by decide
  rcases family_descends (prefixWord ++ tailWord_4031704) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4031747 : List Nat := [1, 1, 1, 3, 2, 4, 1, 2, 1, 5, 2]
def baseStart_4031747 : Nat := 118140960795 + 4031747 * 2 ^ 59
def prefixEnd_4031747 : Nat := 4983230072969 + 3 ^ 40 * 4031747 * 2
def baseEnd_4031747 : Nat := 2070224088322742505020839

theorem tailTrace_4031747 : CollatzResearch.WordTrace tailWord_4031747 prefixEnd_4031747 2070224088322742505020839 := by
  unfold tailWord_4031747
  simp only [CollatzResearch.WordTrace]
  refine ⟨147049893724676661413045495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98033262483117774275363663 147049893724676661413045495)
  ·
    refine ⟨220574840587014992119568243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147049893724676661413045495 220574840587014992119568243)
    ·
      refine ⟨330862260880522488179352365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 220574840587014992119568243 330862260880522488179352365)
      ·
        refine ⟨124073347830195933067257137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 330862260880522488179352365 124073347830195933067257137)
        ·
          refine ⟨93055010872646949800442853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 124073347830195933067257137 93055010872646949800442853)
          ·
            refine ⟨17447814538621303087583035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 93055010872646949800442853 17447814538621303087583035)
            ·
              refine ⟨26171721807931954631374553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17447814538621303087583035 26171721807931954631374553)
              ·
                refine ⟨19628791355948965973530915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26171721807931954631374553 19628791355948965973530915)
                ·
                  refine ⟨29443187033923448960296373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19628791355948965973530915 29443187033923448960296373)
                  ·
                    refine ⟨2760298784430323340027785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 29443187033923448960296373 2760298784430323340027785)
                    ·
                      refine ⟨2070224088322742505020839, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2760298784430323340027785 2070224088322742505020839)
                      ·
                        rfl

theorem cell23_4031747_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 4, 1, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 4, 1, 2, 1, 5, 2].length) (baseStart_4031747 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4031747 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4031747 prefixEnd_4031747 := by exact prefixLift 4031747
  have htrace : WordTrace (prefixWord ++ tailWord_4031747) baseStart_4031747 baseEnd_4031747 := by
    simpa [prefixWord, tailWord_4031747, baseEnd_4031747] using wordTrace_append hprefix tailTrace_4031747
  have hstable : (prefixWord ++ tailWord_4031747).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4031747).length < 2 ^ (prefixWord ++ tailWord_4031747).sum := by decide
  have hdescent : baseEnd_4031747 < baseStart_4031747 := by decide
  rcases family_descends (prefixWord ++ tailWord_4031747) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4031760 : List Nat := [2, 1, 1, 1, 1, 1, 1, 1, 9, 1, 4]
def baseStart_4031760 : Nat := 118140960795 + 4031760 * 2 ^ 59
def prefixEnd_4031760 : Nat := 4983230072969 + 3 ^ 40 * 4031760 * 2
def baseEnd_4031760 : Nat := 2070230763571250954158279

theorem tailTrace_4031760 : CollatzResearch.WordTrace tailWord_4031760 prefixEnd_4031760 2070230763571250954158279 := by
  unfold tailWord_4031760
  simp only [CollatzResearch.WordTrace]
  refine ⟨73525183936814782316634367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98033578582419709755512489 73525183936814782316634367)
  ·
    refine ⟨110287775905222173474951551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73525183936814782316634367 110287775905222173474951551)
    ·
      refine ⟨165431663857833260212427327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110287775905222173474951551 165431663857833260212427327)
      ·
        refine ⟨248147495786749890318640991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 165431663857833260212427327 248147495786749890318640991)
        ·
          refine ⟨372221243680124835477961487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 248147495786749890318640991 372221243680124835477961487)
          ·
            refine ⟨558331865520187253216942231, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 372221243680124835477961487 558331865520187253216942231)
            ·
              refine ⟨837497798280280879825413347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 558331865520187253216942231 837497798280280879825413347)
              ·
                refine ⟨1256246697420421319738120021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 837497798280280879825413347 1256246697420421319738120021)
                ·
                  refine ⟨7360820492697781170340547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 1256246697420421319738120021 7360820492697781170340547)
                  ·
                    refine ⟨11041230739046671755510821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7360820492697781170340547 11041230739046671755510821)
                    ·
                      refine ⟨2070230763571250954158279, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11041230739046671755510821 2070230763571250954158279)
                      ·
                        rfl

theorem cell23_4031760_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 9, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 9, 1, 4].length) (baseStart_4031760 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4031760 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4031760 prefixEnd_4031760 := by exact prefixLift 4031760
  have htrace : WordTrace (prefixWord ++ tailWord_4031760) baseStart_4031760 baseEnd_4031760 := by
    simpa [prefixWord, tailWord_4031760, baseEnd_4031760] using wordTrace_append hprefix tailTrace_4031760
  have hstable : (prefixWord ++ tailWord_4031760).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4031760).length < 2 ^ (prefixWord ++ tailWord_4031760).sum := by decide
  have hdescent : baseEnd_4031760 < baseStart_4031760 := by decide
  rcases family_descends (prefixWord ++ tailWord_4031760) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4031797 : List Nat := [1, 3, 3, 1, 2, 2, 2, 2, 1, 1, 5]
def baseStart_4031797 : Nat := 118140960795 + 4031797 * 2 ^ 59
def prefixEnd_4031797 : Nat := 4983230072969 + 3 ^ 40 * 4031797 * 2
def baseEnd_4031797 : Nat := 2070249762355467309395609

theorem tailTrace_4031797 : CollatzResearch.WordTrace tailWord_4031797 prefixEnd_4031797 2070249762355467309395609 := by
  unfold tailWord_4031797
  simp only [CollatzResearch.WordTrace]
  refine ⟨147051717374495519952365645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98034478249663679968243763 147051717374495519952365645)
  ·
    refine ⟨55144394015435819982137117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 147051717374495519952365645 55144394015435819982137117)
    ·
      refine ⟨20679147755788432493301419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 55144394015435819982137117 20679147755788432493301419)
      ·
        refine ⟨31018721633682648739952129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20679147755788432493301419 31018721633682648739952129)
        ·
          refine ⟨23264041225261986554964097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31018721633682648739952129 23264041225261986554964097)
          ·
            refine ⟨17448030918946489916223073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23264041225261986554964097 17448030918946489916223073)
            ·
              refine ⟨13086023189209867437167305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17448030918946489916223073 13086023189209867437167305)
              ·
                refine ⟨9814517391907400577875479, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13086023189209867437167305 9814517391907400577875479)
                ·
                  refine ⟨14721776087861100866813219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9814517391907400577875479 14721776087861100866813219)
                  ·
                    refine ⟨22082664131791651300219829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14721776087861100866813219 22082664131791651300219829)
                    ·
                      refine ⟨2070249762355467309395609, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 22082664131791651300219829 2070249762355467309395609)
                      ·
                        rfl

theorem cell23_4031797_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 2, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 2, 2, 2, 1, 1, 5].length) (baseStart_4031797 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4031797 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4031797 prefixEnd_4031797 := by exact prefixLift 4031797
  have htrace : WordTrace (prefixWord ++ tailWord_4031797) baseStart_4031797 baseEnd_4031797 := by
    simpa [prefixWord, tailWord_4031797, baseEnd_4031797] using wordTrace_append hprefix tailTrace_4031797
  have hstable : (prefixWord ++ tailWord_4031797).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4031797).length < 2 ^ (prefixWord ++ tailWord_4031797).sum := by decide
  have hdescent : baseEnd_4031797 < baseStart_4031797 := by decide
  rcases family_descends (prefixWord ++ tailWord_4031797) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4031804 : List Nat := [2, 2, 2, 2, 1, 4, 1, 3, 2, 4]
def baseStart_4031804 : Nat := 118140960795 + 4031804 * 2 ^ 59
def prefixEnd_4031804 : Nat := 4983230072969 + 3 ^ 40 * 4031804 * 2
def baseEnd_4031804 : Nat := 690084452240016260669359

theorem tailTrace_4031804 : CollatzResearch.WordTrace tailWord_4031804 prefixEnd_4031804 690084452240016260669359 := by
  unfold tailWord_4031804
  simp only [CollatzResearch.WordTrace]
  refine ⟨73525986342735080073935233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98034648456980106765246977 73525986342735080073935233)
  ·
    refine ⟨55144489757051310055451425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73525986342735080073935233 55144489757051310055451425)
    ·
      refine ⟨41358367317788482541588569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55144489757051310055451425 41358367317788482541588569)
      ·
        refine ⟨31018775488341361906191427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41358367317788482541588569 31018775488341361906191427)
        ·
          refine ⟨46528163232512042859287141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31018775488341361906191427 46528163232512042859287141)
          ·
            refine ⟨8724030606096008036116339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 46528163232512042859287141 8724030606096008036116339)
            ·
              refine ⟨13086045909144012054174509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8724030606096008036116339 13086045909144012054174509)
              ·
                refine ⟨4907267215929004520315441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13086045909144012054174509 4907267215929004520315441)
                ·
                  refine ⟨3680450411946753390236581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4907267215929004520315441 3680450411946753390236581)
                  ·
                    refine ⟨690084452240016260669359, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3680450411946753390236581 690084452240016260669359)
                    ·
                      rfl

theorem cell23_4031804_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 4, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 4, 1, 3, 2, 4].length) (baseStart_4031804 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4031804 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4031804 prefixEnd_4031804 := by exact prefixLift 4031804
  have htrace : WordTrace (prefixWord ++ tailWord_4031804) baseStart_4031804 baseEnd_4031804 := by
    simpa [prefixWord, tailWord_4031804, baseEnd_4031804] using wordTrace_append hprefix tailTrace_4031804
  have hstable : (prefixWord ++ tailWord_4031804).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4031804).length < 2 ^ (prefixWord ++ tailWord_4031804).sum := by decide
  have hdescent : baseEnd_4031804 < baseStart_4031804 := by decide
  rcases family_descends (prefixWord ++ tailWord_4031804) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4031821 : List Nat := [1, 6, 1, 3, 1, 1, 1, 2, 1, 6]
def baseStart_4031821 : Nat := 118140960795 + 4031821 * 2 ^ 59
def prefixEnd_4031821 : Nat := 4983230072969 + 3 ^ 40 * 4031821 * 2
def baseEnd_4031821 : Nat := 690087361963725071831833

theorem tailTrace_4031821 : CollatzResearch.WordTrace tailWord_4031821 prefixEnd_4031821 690087361963725071831833 := by
  unfold tailWord_4031821
  simp only [CollatzResearch.WordTrace]
  refine ⟨147052592726408572051239317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98035061817605714700826211 147052592726408572051239317)
  ·
    refine ⟨6893090284050401814901843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 147052592726408572051239317 6893090284050401814901843)
    ·
      refine ⟨10339635426075602722352765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6893090284050401814901843 10339635426075602722352765)
      ·
        refine ⟨3877363284778351020882287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10339635426075602722352765 3877363284778351020882287)
        ·
          refine ⟨5816044927167526531323431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3877363284778351020882287 5816044927167526531323431)
          ·
            refine ⟨8724067390751289796985147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5816044927167526531323431 8724067390751289796985147)
            ·
              refine ⟨13086101086126934695477721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8724067390751289796985147 13086101086126934695477721)
              ·
                refine ⟨9814575814595201021608291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13086101086126934695477721 9814575814595201021608291)
                ·
                  refine ⟨14721863721892801532412437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9814575814595201021608291 14721863721892801532412437)
                  ·
                    refine ⟨690087361963725071831833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 14721863721892801532412437 690087361963725071831833)
                    ·
                      rfl

theorem cell23_4031821_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 3, 1, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 3, 1, 1, 1, 2, 1, 6].length) (baseStart_4031821 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4031821 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4031821 prefixEnd_4031821 := by exact prefixLift 4031821
  have htrace : WordTrace (prefixWord ++ tailWord_4031821) baseStart_4031821 baseEnd_4031821 := by
    simpa [prefixWord, tailWord_4031821, baseEnd_4031821] using wordTrace_append hprefix tailTrace_4031821
  have hstable : (prefixWord ++ tailWord_4031821).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4031821).length < 2 ^ (prefixWord ++ tailWord_4031821).sum := by decide
  have hdescent : baseEnd_4031821 < baseStart_4031821 := by decide
  rcases family_descends (prefixWord ++ tailWord_4031821) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4031827 : List Nat := [1, 1, 1, 2, 1, 1, 7, 2, 1, 3, 3]
def baseStart_4031827 : Nat := 118140960795 + 4031827 * 2 ^ 59
def prefixEnd_4031827 : Nat := 4983230072969 + 3 ^ 40 * 4031827 * 2
def baseEnd_4031827 : Nat := 2070265166775102192020471

theorem tailTrace_4031827 : CollatzResearch.WordTrace tailWord_4031827 prefixEnd_4031827 2070265166775102192020471 := by
  unfold tailWord_4031827
  simp only [CollatzResearch.WordTrace]
  refine ⟨147052811564386835075957735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98035207709591223383971823 147052811564386835075957735)
  ·
    refine ⟨220579217346580252613936603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147052811564386835075957735 220579217346580252613936603)
    ·
      refine ⟨330868826019870378920904905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 220579217346580252613936603 330868826019870378920904905)
      ·
        refine ⟨248151619514902784190678679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 330868826019870378920904905 248151619514902784190678679)
        ·
          refine ⟨372227429272354176286018019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 248151619514902784190678679 372227429272354176286018019)
          ·
            refine ⟨558341143908531264429027029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 372227429272354176286018019 558341143908531264429027029)
            ·
              refine ⟨13086120560356201510055321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 558341143908531264429027029 13086120560356201510055321)
              ·
                refine ⟨9814590420267151132541491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13086120560356201510055321 9814590420267151132541491)
                ·
                  refine ⟨14721885630400726698812237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9814590420267151132541491 14721885630400726698812237)
                  ·
                    refine ⟨5520707111400272512054589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14721885630400726698812237 5520707111400272512054589)
                    ·
                      refine ⟨2070265166775102192020471, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5520707111400272512054589 2070265166775102192020471)
                      ·
                        rfl

theorem cell23_4031827_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 7, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 7, 2, 1, 3, 3].length) (baseStart_4031827 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4031827 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4031827 prefixEnd_4031827 := by exact prefixLift 4031827
  have htrace : WordTrace (prefixWord ++ tailWord_4031827) baseStart_4031827 baseEnd_4031827 := by
    simpa [prefixWord, tailWord_4031827, baseEnd_4031827] using wordTrace_append hprefix tailTrace_4031827
  have hstable : (prefixWord ++ tailWord_4031827).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4031827).length < 2 ^ (prefixWord ++ tailWord_4031827).sum := by decide
  have hdescent : baseEnd_4031827 < baseStart_4031827 := by decide
  rcases family_descends (prefixWord ++ tailWord_4031827) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4031828 : List Nat := [2, 4, 1, 1, 2, 1, 2, 5, 1, 2, 2]
def baseStart_4031828 : Nat := 118140960795 + 4031828 * 2 ^ 59
def prefixEnd_4031828 : Nat := 4983230072969 + 3 ^ 40 * 4031828 * 2
def baseEnd_4031828 : Nat := 2070265680255756688107967

theorem tailTrace_4031828 : CollatzResearch.WordTrace tailWord_4031828 prefixEnd_4031828 2070265680255756688107967 := by
  unfold tailWord_4031828
  simp only [CollatzResearch.WordTrace]
  refine ⟨73526424018691606123372069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98035232024922141497829425 73526424018691606123372069)
  ·
    refine ⟨13786204503504676148132263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 73526424018691606123372069 13786204503504676148132263)
    ·
      refine ⟨20679306755257014222198395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13786204503504676148132263 20679306755257014222198395)
      ·
        refine ⟨31018960132885521333297593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20679306755257014222198395 31018960132885521333297593)
        ·
          refine ⟨23264220099664140999973195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31018960132885521333297593 23264220099664140999973195)
          ·
            refine ⟨34896330149496211499959793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23264220099664140999973195 34896330149496211499959793)
            ·
              refine ⟨26172247612122158624969845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34896330149496211499959793 26172247612122158624969845)
              ·
                refine ⟨2453648213636452371090923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 26172247612122158624969845 2453648213636452371090923)
                ·
                  refine ⟨3680472320454678556636385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2453648213636452371090923 3680472320454678556636385)
                  ·
                    refine ⟨2760354240341008917477289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3680472320454678556636385 2760354240341008917477289)
                    ·
                      refine ⟨2070265680255756688107967, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2760354240341008917477289 2070265680255756688107967)
                      ·
                        rfl

theorem cell23_4031828_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 2, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 2, 5, 1, 2, 2].length) (baseStart_4031828 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4031828 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4031828 prefixEnd_4031828 := by exact prefixLift 4031828
  have htrace : WordTrace (prefixWord ++ tailWord_4031828) baseStart_4031828 baseEnd_4031828 := by
    simpa [prefixWord, tailWord_4031828, baseEnd_4031828] using wordTrace_append hprefix tailTrace_4031828
  have hstable : (prefixWord ++ tailWord_4031828).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4031828).length < 2 ^ (prefixWord ++ tailWord_4031828).sum := by decide
  have hdescent : baseEnd_4031828 < baseStart_4031828 := by decide
  rcases family_descends (prefixWord ++ tailWord_4031828) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4031831 : List Nat := [1, 1, 3, 2, 3, 3, 3, 1, 1, 2, 3]
def baseStart_4031831 : Nat := 118140960795 + 4031831 * 2 ^ 59
def prefixEnd_4031831 : Nat := 4983230072969 + 3 ^ 40 * 4031831 * 2
def baseEnd_4031831 : Nat := 2070267220697720176370453

theorem tailTrace_4031831 : CollatzResearch.WordTrace tailWord_4031831 prefixEnd_4031831 2070267220697720176370453 := by
  unfold tailWord_4031831
  simp only [CollatzResearch.WordTrace]
  refine ⟨147052957456372343759103347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98035304970914895839402231 147052957456372343759103347)
  ·
    refine ⟨220579436184558515638655021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147052957456372343759103347 220579436184558515638655021)
    ·
      refine ⟨82717288569209443364495633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 220579436184558515638655021 82717288569209443364495633)
      ·
        refine ⟨62037966426907082523371725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 82717288569209443364495633 62037966426907082523371725)
        ·
          refine ⟨23264237410090155946264397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 62037966426907082523371725 23264237410090155946264397)
          ·
            refine ⟨8724089028783808479849149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23264237410090155946264397 8724089028783808479849149)
            ·
              refine ⟨3271533385793928179943431, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8724089028783808479849149 3271533385793928179943431)
              ·
                refine ⟨4907300078690892269915147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3271533385793928179943431 4907300078690892269915147)
                ·
                  refine ⟨7360950118036338404872721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4907300078690892269915147 7360950118036338404872721)
                  ·
                    refine ⟨5520712588527253803654541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7360950118036338404872721 5520712588527253803654541)
                    ·
                      refine ⟨2070267220697720176370453, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5520712588527253803654541 2070267220697720176370453)
                      ·
                        rfl

theorem cell23_4031831_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 3, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 3, 3, 1, 1, 2, 3].length) (baseStart_4031831 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4031831 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4031831 prefixEnd_4031831 := by exact prefixLift 4031831
  have htrace : WordTrace (prefixWord ++ tailWord_4031831) baseStart_4031831 baseEnd_4031831 := by
    simpa [prefixWord, tailWord_4031831, baseEnd_4031831] using wordTrace_append hprefix tailTrace_4031831
  have hstable : (prefixWord ++ tailWord_4031831).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4031831).length < 2 ^ (prefixWord ++ tailWord_4031831).sum := by decide
  have hdescent : baseEnd_4031831 < baseStart_4031831 := by decide
  rcases family_descends (prefixWord ++ tailWord_4031831) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4031861 : List Nat := [1, 3, 4, 1, 3, 1, 2, 1, 1, 3, 3]
def baseStart_4031861 : Nat := 118140960795 + 4031861 * 2 ^ 59
def prefixEnd_4031861 : Nat := 4983230072969 + 3 ^ 40 * 4031861 * 2
def baseEnd_4031861 : Nat := 2070282625117355058995315

theorem tailTrace_4031861 : CollatzResearch.WordTrace tailWord_4031861 prefixEnd_4031861 2070282625117355058995315 := by
  unfold tailWord_4031861
  simp only [CollatzResearch.WordTrace]
  refine ⟨147054051646263658882695437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98036034430842439255130291 147054051646263658882695437)
  ·
    refine ⟨55145269367348872081010789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 147054051646263658882695437 55145269367348872081010789)
    ·
      refine ⟨10339738006377913515189523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 55145269367348872081010789 10339738006377913515189523)
      ·
        refine ⟨15509607009566870272784285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10339738006377913515189523 15509607009566870272784285)
        ·
          refine ⟨5816102628587576352294107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15509607009566870272784285 5816102628587576352294107)
          ·
            refine ⟨8724153942881364528441161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5816102628587576352294107 8724153942881364528441161)
            ·
              refine ⟨6543115457161023396330871, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8724153942881364528441161 6543115457161023396330871)
              ·
                refine ⟨9814673185741535094496307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6543115457161023396330871 9814673185741535094496307)
                ·
                  refine ⟨14722009778612302641744461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9814673185741535094496307 14722009778612302641744461)
                  ·
                    refine ⟨5520753666979613490654173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14722009778612302641744461 5520753666979613490654173)
                    ·
                      refine ⟨2070282625117355058995315, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5520753666979613490654173 2070282625117355058995315)
                      ·
                        rfl

theorem cell23_4031861_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 3, 1, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 3, 1, 2, 1, 1, 3, 3].length) (baseStart_4031861 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4031861 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4031861 prefixEnd_4031861 := by exact prefixLift 4031861
  have htrace : WordTrace (prefixWord ++ tailWord_4031861) baseStart_4031861 baseEnd_4031861 := by
    simpa [prefixWord, tailWord_4031861, baseEnd_4031861] using wordTrace_append hprefix tailTrace_4031861
  have hstable : (prefixWord ++ tailWord_4031861).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4031861).length < 2 ^ (prefixWord ++ tailWord_4031861).sum := by decide
  have hdescent : baseEnd_4031861 < baseStart_4031861 := by decide
  rcases family_descends (prefixWord ++ tailWord_4031861) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4031884 : List Nat := [2, 2, 1, 2, 1, 3, 1, 4, 1, 4, 2]
def baseStart_4031884 : Nat := 118140960795 + 4031884 * 2 ^ 59
def prefixEnd_4031884 : Nat := 4983230072969 + 3 ^ 40 * 4031884 * 2
def baseEnd_4031884 : Nat := 2070294435172408469007709

theorem tailTrace_4031884 : CollatzResearch.WordTrace tailWord_4031884 prefixEnd_4031884 2070294435172408469007709 := by
  unfold tailWord_4031884
  simp only [CollatzResearch.WordTrace]
  refine ⟨73527445262590166905391353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98036593683453555873855137 73527445262590166905391353)
  ·
    refine ⟨55145583946942625179043515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73527445262590166905391353 55145583946942625179043515)
    ·
      refine ⟨82718375920413937768565273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55145583946942625179043515 82718375920413937768565273)
      ·
        refine ⟨62038781940310453326423955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 82718375920413937768565273 62038781940310453326423955)
        ·
          refine ⟨93058172910465679989635933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62038781940310453326423955 93058172910465679989635933)
          ·
            refine ⟨34896814841424629996113475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 93058172910465679989635933 34896814841424629996113475)
            ·
              refine ⟨52345222262136944994170213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34896814841424629996113475 52345222262136944994170213)
              ·
                refine ⟨9814729174150677186406915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 52345222262136944994170213 9814729174150677186406915)
                ·
                  refine ⟨14722093761226015779610373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9814729174150677186406915 14722093761226015779610373)
                  ·
                    refine ⟨2760392580229877958676945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 14722093761226015779610373 2760392580229877958676945)
                    ·
                      refine ⟨2070294435172408469007709, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2760392580229877958676945 2070294435172408469007709)
                      ·
                        rfl

theorem cell23_4031884_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 1, 4, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 1, 4, 1, 4, 2].length) (baseStart_4031884 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4031884 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4031884 prefixEnd_4031884 := by exact prefixLift 4031884
  have htrace : WordTrace (prefixWord ++ tailWord_4031884) baseStart_4031884 baseEnd_4031884 := by
    simpa [prefixWord, tailWord_4031884, baseEnd_4031884] using wordTrace_append hprefix tailTrace_4031884
  have hstable : (prefixWord ++ tailWord_4031884).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4031884).length < 2 ^ (prefixWord ++ tailWord_4031884).sum := by decide
  have hdescent : baseEnd_4031884 < baseStart_4031884 := by decide
  rcases family_descends (prefixWord ++ tailWord_4031884) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4031897 : List Nat := [1, 2, 1, 2, 1, 5, 1, 2, 2, 2, 4]
def baseStart_4031897 : Nat := 118140960795 + 4031897 * 2 ^ 59
def prefixEnd_4031897 : Nat := 4983230072969 + 3 ^ 40 * 4031897 * 2
def baseEnd_4031897 : Nat := 2070301110420916918145149

theorem tailTrace_4031897 : CollatzResearch.WordTrace tailWord_4031897 prefixEnd_4031897 2070301110420916918145149 := by
  unfold tailWord_4031897
  simp only [CollatzResearch.WordTrace]
  refine ⟨147055364674133237031005945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98036909782755491354003963 147055364674133237031005945)
  ·
    refine ⟨110291523505599927773254459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 147055364674133237031005945 110291523505599927773254459)
    ·
      refine ⟨165437285258399891659881689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110291523505599927773254459 165437285258399891659881689)
      ·
        refine ⟨124077963943799918744911267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 165437285258399891659881689 124077963943799918744911267)
        ·
          refine ⟨186116945915699878117366901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 124077963943799918744911267 186116945915699878117366901)
          ·
            refine ⟨17448463679596863573503147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 186116945915699878117366901 17448463679596863573503147)
            ·
              refine ⟨26172695519395295360254721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17448463679596863573503147 26172695519395295360254721)
              ·
                refine ⟨19629521639546471520191041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26172695519395295360254721 19629521639546471520191041)
                ·
                  refine ⟨14722141229659853640143281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19629521639546471520191041 14722141229659853640143281)
                  ·
                    refine ⟨11041605922244890230107461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14722141229659853640143281 11041605922244890230107461)
                    ·
                      refine ⟨2070301110420916918145149, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11041605922244890230107461 2070301110420916918145149)
                      ·
                        rfl

theorem cell23_4031897_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 5, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 5, 1, 2, 2, 2, 4].length) (baseStart_4031897 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4031897 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4031897 prefixEnd_4031897 := by exact prefixLift 4031897
  have htrace : WordTrace (prefixWord ++ tailWord_4031897) baseStart_4031897 baseEnd_4031897 := by
    simpa [prefixWord, tailWord_4031897, baseEnd_4031897] using wordTrace_append hprefix tailTrace_4031897
  have hstable : (prefixWord ++ tailWord_4031897).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4031897).length < 2 ^ (prefixWord ++ tailWord_4031897).sum := by decide
  have hdescent : baseEnd_4031897 < baseStart_4031897 := by decide
  rcases family_descends (prefixWord ++ tailWord_4031897) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4031907 : List Nat := [1, 1, 1, 4, 1, 3, 4, 1, 7]
def baseStart_4031907 : Nat := 118140960795 + 4031907 * 2 ^ 59
def prefixEnd_4031907 : Nat := 4983230072969 + 3 ^ 40 * 4031907 * 2
def baseEnd_4031907 : Nat := 230034027247495764335567

theorem tailTrace_4031907 : CollatzResearch.WordTrace tailWord_4031907 prefixEnd_4031907 230034027247495764335567 := by
  unfold tailWord_4031907
  simp only [CollatzResearch.WordTrace]
  refine ⟨147055729404097008738869975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98037152936064672492579983 147055729404097008738869975)
  ·
    refine ⟨220583594106145513108304963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147055729404097008738869975 220583594106145513108304963)
    ·
      refine ⟨330875391159218269662457445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 220583594106145513108304963 330875391159218269662457445)
      ·
        refine ⟨62039135842353425561710771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 330875391159218269662457445 62039135842353425561710771)
        ·
          refine ⟨93058703763530138342566157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62039135842353425561710771 93058703763530138342566157)
          ·
            refine ⟨34897013911323801878462309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 93058703763530138342566157 34897013911323801878462309)
            ·
              refine ⟨6543190108373212852211683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 34897013911323801878462309 6543190108373212852211683)
              ·
                refine ⟨9814785162559819278317525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6543190108373212852211683 9814785162559819278317525)
                ·
                  refine ⟨230034027247495764335567, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 9814785162559819278317525 230034027247495764335567)
                  ·
                    rfl

theorem cell23_4031907_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 4, 1, 7].length) (baseStart_4031907 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4031907 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4031907 prefixEnd_4031907 := by exact prefixLift 4031907
  have htrace : WordTrace (prefixWord ++ tailWord_4031907) baseStart_4031907 baseEnd_4031907 := by
    simpa [prefixWord, tailWord_4031907, baseEnd_4031907] using wordTrace_append hprefix tailTrace_4031907
  have hstable : (prefixWord ++ tailWord_4031907).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4031907).length < 2 ^ (prefixWord ++ tailWord_4031907).sum := by decide
  have hdescent : baseEnd_4031907 < baseStart_4031907 := by decide
  rcases family_descends (prefixWord ++ tailWord_4031907) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4032017 : List Nat := [1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 6]
def baseStart_4032017 : Nat := 118140960795 + 4032017 * 2 ^ 59
def prefixEnd_4032017 : Nat := 4983230072969 + 3 ^ 40 * 4032017 * 2
def baseEnd_4032017 : Nat := 2070362728099456448644597

theorem tailTrace_4032017 : CollatzResearch.WordTrace tailWord_4032017 prefixEnd_4032017 2070362728099456448644597 := by
  unfold tailWord_4032017
  simp only [CollatzResearch.WordTrace]
  refine ⟨147059741433698497525374305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98039827622465665016916203 147059741433698497525374305)
  ·
    refine ⟨110294806075273873144030729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 147059741433698497525374305 110294806075273873144030729)
    ·
      refine ⟨82721104556455404858023047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 110294806075273873144030729 82721104556455404858023047)
      ·
        refine ⟨124081656834683107287034571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82721104556455404858023047 124081656834683107287034571)
        ·
          refine ⟨186122485252024660930551857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 124081656834683107287034571 186122485252024660930551857)
          ·
            refine ⟨139591863939018495697913893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 186122485252024660930551857 139591863939018495697913893)
            ·
              refine ⟨26173474488565967943358855, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 139591863939018495697913893 26173474488565967943358855)
              ·
                refine ⟨39260211732848951915038283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26173474488565967943358855 39260211732848951915038283)
                ·
                  refine ⟨58890317599273427872557425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39260211732848951915038283 58890317599273427872557425)
                  ·
                    refine ⟨44167738199455070904418069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 58890317599273427872557425 44167738199455070904418069)
                    ·
                      refine ⟨2070362728099456448644597, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 44167738199455070904418069 2070362728099456448644597)
                      ·
                        rfl

theorem cell23_4032017_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 6].length) (baseStart_4032017 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4032017 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4032017 prefixEnd_4032017 := by exact prefixLift 4032017
  have htrace : WordTrace (prefixWord ++ tailWord_4032017) baseStart_4032017 baseEnd_4032017 := by
    simpa [prefixWord, tailWord_4032017, baseEnd_4032017] using wordTrace_append hprefix tailTrace_4032017
  have hstable : (prefixWord ++ tailWord_4032017).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4032017).length < 2 ^ (prefixWord ++ tailWord_4032017).sum := by decide
  have hdescent : baseEnd_4032017 < baseStart_4032017 := by decide
  rcases family_descends (prefixWord ++ tailWord_4032017) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4032037 : List Nat := [1, 3, 1, 2, 2, 1, 1, 1, 1, 3, 7]
def baseStart_4032037 : Nat := 118140960795 + 4032037 * 2 ^ 59
def prefixEnd_4032037 : Nat := 4983230072969 + 3 ^ 40 * 4032037 * 2
def baseEnd_4032037 : Nat := 2070372997712546370394505

theorem tailTrace_4032037 : CollatzResearch.WordTrace tailWord_4032037 prefixEnd_4032037 2070372997712546370394505 := by
  unfold tailWord_4032037
  simp only [CollatzResearch.WordTrace]
  refine ⟨147060470893626040941102365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98040313929084027294068243 147060470893626040941102365)
  ·
    refine ⟨55147676585109765352913387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 147060470893626040941102365 55147676585109765352913387)
    ·
      refine ⟨82721514877664648029370081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55147676585109765352913387 82721514877664648029370081)
      ·
        refine ⟨62041136158248486022027561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 82721514877664648029370081 62041136158248486022027561)
        ·
          refine ⟨46530852118686364516520671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62041136158248486022027561 46530852118686364516520671)
          ·
            refine ⟨69796278178029546774781007, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46530852118686364516520671 69796278178029546774781007)
            ·
              refine ⟨104694417267044320162171511, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 69796278178029546774781007 104694417267044320162171511)
              ·
                refine ⟨157041625900566480243257267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 104694417267044320162171511 157041625900566480243257267)
                ·
                  refine ⟨235562438850849720364885901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 157041625900566480243257267 235562438850849720364885901)
                  ·
                    refine ⟨88335914569068645136832213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 235562438850849720364885901 88335914569068645136832213)
                    ·
                      refine ⟨2070372997712546370394505, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 88335914569068645136832213 2070372997712546370394505)
                      ·
                        rfl

theorem cell23_4032037_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 1, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 1, 1, 1, 3, 7].length) (baseStart_4032037 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4032037 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4032037 prefixEnd_4032037 := by exact prefixLift 4032037
  have htrace : WordTrace (prefixWord ++ tailWord_4032037) baseStart_4032037 baseEnd_4032037 := by
    simpa [prefixWord, tailWord_4032037, baseEnd_4032037] using wordTrace_append hprefix tailTrace_4032037
  have hstable : (prefixWord ++ tailWord_4032037).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4032037).length < 2 ^ (prefixWord ++ tailWord_4032037).sum := by decide
  have hdescent : baseEnd_4032037 < baseStart_4032037 := by decide
  rcases family_descends (prefixWord ++ tailWord_4032037) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4032051 : List Nat := [1, 1, 1, 2, 4, 4, 1, 1, 1, 5, 2]
def baseStart_4032051 : Nat := 118140960795 + 4032051 * 2 ^ 59
def prefixEnd_4032051 : Nat := 4983230072969 + 3 ^ 40 * 4032051 * 2
def baseEnd_4032051 : Nat := 2070380186441709315619441

theorem tailTrace_4032051 : CollatzResearch.WordTrace tailWord_4032051 prefixEnd_4032051 2070380186441709315619441 := by
  unfold tailWord_4032051
  simp only [CollatzResearch.WordTrace]
  refine ⟨147060981515575321332112007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98040654343716880888074671 147060981515575321332112007)
  ·
    refine ⟨220591472273362981998168011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147060981515575321332112007 220591472273362981998168011)
    ·
      refine ⟨330887208410044472997252017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 220591472273362981998168011 330887208410044472997252017)
      ·
        refine ⟨248165406307533354747939013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 330887208410044472997252017 248165406307533354747939013)
        ·
          refine ⟨46531013682662504015238565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 248165406307533354747939013 46531013682662504015238565)
          ·
            refine ⟨8724565065499219502857231, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 46531013682662504015238565 8724565065499219502857231)
            ·
              refine ⟨13086847598248829254285847, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8724565065499219502857231 13086847598248829254285847)
              ·
                refine ⟨19630271397373243881428771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13086847598248829254285847 19630271397373243881428771)
                ·
                  refine ⟨29445407096059865822143157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19630271397373243881428771 29445407096059865822143157)
                  ·
                    refine ⟨2760506915255612420825921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 29445407096059865822143157 2760506915255612420825921)
                    ·
                      refine ⟨2070380186441709315619441, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2760506915255612420825921 2070380186441709315619441)
                      ·
                        rfl

theorem cell23_4032051_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 4, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 4, 1, 1, 1, 5, 2].length) (baseStart_4032051 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4032051 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4032051 prefixEnd_4032051 := by exact prefixLift 4032051
  have htrace : WordTrace (prefixWord ++ tailWord_4032051) baseStart_4032051 baseEnd_4032051 := by
    simpa [prefixWord, tailWord_4032051, baseEnd_4032051] using wordTrace_append hprefix tailTrace_4032051
  have hstable : (prefixWord ++ tailWord_4032051).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4032051).length < 2 ^ (prefixWord ++ tailWord_4032051).sum := by decide
  have hdescent : baseEnd_4032051 < baseStart_4032051 := by decide
  rcases family_descends (prefixWord ++ tailWord_4032051) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4032109 : List Nat := [1, 5, 1, 1, 5, 1, 1, 3, 1, 1, 3]
def baseStart_4032109 : Nat := 118140960795 + 4032109 * 2 ^ 59
def prefixEnd_4032109 : Nat := 4983230072969 + 3 ^ 40 * 4032109 * 2
def baseEnd_4032109 : Nat := 2070409968319670088694175

theorem tailTrace_4032109 : CollatzResearch.WordTrace tailWord_4032109 prefixEnd_4032109 2070409968319670088694175 := by
  unfold tailWord_4032109
  simp only [CollatzResearch.WordTrace]
  refine ⟨147063096949365197237723381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98042064632910131491815587 147063096949365197237723381)
  ·
    refine ⟨13787165339002987241036567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 147063096949365197237723381 13787165339002987241036567)
    ·
      refine ⟨20680748008504480861554851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13787165339002987241036567 20680748008504480861554851)
      ·
        refine ⟨31021122012756721292332277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20680748008504480861554851 31021122012756721292332277)
        ·
          refine ⟨2908230188695942621156151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 31021122012756721292332277 2908230188695942621156151)
          ·
            refine ⟨4362345283043913931734227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2908230188695942621156151 4362345283043913931734227)
            ·
              refine ⟨6543517924565870897601341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4362345283043913931734227 6543517924565870897601341)
              ·
                refine ⟨2453819221712201586600503, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6543517924565870897601341 2453819221712201586600503)
                ·
                  refine ⟨3680728832568302379900755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2453819221712201586600503 3680728832568302379900755)
                  ·
                    refine ⟨5521093248852453569851133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3680728832568302379900755 5521093248852453569851133)
                    ·
                      refine ⟨2070409968319670088694175, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5521093248852453569851133 2070409968319670088694175)
                      ·
                        rfl

theorem cell23_4032109_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 5, 1, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 5, 1, 1, 3, 1, 1, 3].length) (baseStart_4032109 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4032109 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4032109 prefixEnd_4032109 := by exact prefixLift 4032109
  have htrace : WordTrace (prefixWord ++ tailWord_4032109) baseStart_4032109 baseEnd_4032109 := by
    simpa [prefixWord, tailWord_4032109, baseEnd_4032109] using wordTrace_append hprefix tailTrace_4032109
  have hstable : (prefixWord ++ tailWord_4032109).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4032109).length < 2 ^ (prefixWord ++ tailWord_4032109).sum := by decide
  have hdescent : baseEnd_4032109 < baseStart_4032109 := by decide
  rcases family_descends (prefixWord ++ tailWord_4032109) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4032118 : List Nat := [5, 1, 1, 2, 2, 2, 2, 1, 1, 1, 5]
def baseStart_4032118 : Nat := 118140960795 + 4032118 * 2 ^ 59
def prefixEnd_4032118 : Nat := 4983230072969 + 3 ^ 40 * 4032118 * 2
def baseEnd_4032118 : Nat := 2070414589645560553481633

theorem tailTrace_4032118 : CollatzResearch.WordTrace tailWord_4032118 prefixEnd_4032118 2070414589645560553481633 := by
  unfold tailWord_4032118
  simp only [CollatzResearch.WordTrace]
  refine ⟨9191464075395786985925063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 98042283470888394516534005 9191464075395786985925063)
  ·
    refine ⟨13787196113093680478887595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9191464075395786985925063 13787196113093680478887595)
    ·
      refine ⟨20680794169640520718331393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13787196113093680478887595 20680794169640520718331393)
      ·
        refine ⟨15510595627230390538748545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20680794169640520718331393 15510595627230390538748545)
        ·
          refine ⟨11632946720422792904061409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15510595627230390538748545 11632946720422792904061409)
          ·
            refine ⟨8724710040317094678046057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11632946720422792904061409 8724710040317094678046057)
            ·
              refine ⟨6543532530237821008534543, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8724710040317094678046057 6543532530237821008534543)
              ·
                refine ⟨9815298795356731512801815, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6543532530237821008534543 9815298795356731512801815)
                ·
                  refine ⟨14722948193035097269202723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9815298795356731512801815 14722948193035097269202723)
                  ·
                    refine ⟨22084422289552645903804085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14722948193035097269202723 22084422289552645903804085)
                    ·
                      refine ⟨2070414589645560553481633, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 22084422289552645903804085 2070414589645560553481633)
                      ·
                        rfl

theorem cell23_4032118_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 2, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 2, 2, 1, 1, 1, 5].length) (baseStart_4032118 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4032118 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4032118 prefixEnd_4032118 := by exact prefixLift 4032118
  have htrace : WordTrace (prefixWord ++ tailWord_4032118) baseStart_4032118 baseEnd_4032118 := by
    simpa [prefixWord, tailWord_4032118, baseEnd_4032118] using wordTrace_append hprefix tailTrace_4032118
  have hstable : (prefixWord ++ tailWord_4032118).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4032118).length < 2 ^ (prefixWord ++ tailWord_4032118).sum := by decide
  have hdescent : baseEnd_4032118 < baseStart_4032118 := by decide
  rcases family_descends (prefixWord ++ tailWord_4032118) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4032132 : List Nat := [2, 3, 2, 1, 4, 2, 1, 1, 3, 2, 2]
def baseStart_4032132 : Nat := 118140960795 + 4032132 * 2 ^ 59
def prefixEnd_4032132 : Nat := 4983230072969 + 3 ^ 40 * 4032132 * 2
def baseEnd_4032132 : Nat := 2070421778374723498706569

theorem tailTrace_4032132 : CollatzResearch.WordTrace tailWord_4032132 prefixEnd_4032132 2070421778374723498706569 := by
  unfold tailWord_4032132
  simp only [CollatzResearch.WordTrace]
  refine ⟨73531967914140936082905325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98042623885521248110540433 73531967914140936082905325)
  ·
    refine ⟨27574487967802851031089497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 73531967914140936082905325 27574487967802851031089497)
    ·
      refine ⟨20680865975852138273317123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27574487967802851031089497 20680865975852138273317123)
      ·
        refine ⟨31021298963778207409975685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20680865975852138273317123 31021298963778207409975685)
        ·
          refine ⟨5816493555708413889370441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 31021298963778207409975685 5816493555708413889370441)
          ·
            refine ⟨4362370166781310417027831, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5816493555708413889370441 4362370166781310417027831)
            ·
              refine ⟨6543555250171965625541747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4362370166781310417027831 6543555250171965625541747)
              ·
                refine ⟨9815332875257948438312621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6543555250171965625541747 9815332875257948438312621)
                ·
                  refine ⟨3680749828221730664367233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9815332875257948438312621 3680749828221730664367233)
                  ·
                    refine ⟨2760562371166297998275425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3680749828221730664367233 2760562371166297998275425)
                    ·
                      refine ⟨2070421778374723498706569, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2760562371166297998275425 2070421778374723498706569)
                      ·
                        rfl

theorem cell23_4032132_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 4, 2, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 4, 2, 1, 1, 3, 2, 2].length) (baseStart_4032132 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4032132 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4032132 prefixEnd_4032132 := by exact prefixLift 4032132
  have htrace : WordTrace (prefixWord ++ tailWord_4032132) baseStart_4032132 baseEnd_4032132 := by
    simpa [prefixWord, tailWord_4032132, baseEnd_4032132] using wordTrace_append hprefix tailTrace_4032132
  have hstable : (prefixWord ++ tailWord_4032132).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4032132).length < 2 ^ (prefixWord ++ tailWord_4032132).sum := by decide
  have hdescent : baseEnd_4032132 < baseStart_4032132 := by decide
  rcases family_descends (prefixWord ++ tailWord_4032132) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4032175 : List Nat := [1, 1, 2, 1, 2, 4, 5, 1, 1, 3, 2]
def baseStart_4032175 : Nat := 118140960795 + 4032175 * 2 ^ 59
def prefixEnd_4032175 : Nat := 4983230072969 + 3 ^ 40 * 4032175 * 2
def baseEnd_4032175 : Nat := 2070443858042866830468871

theorem tailTrace_4032175 : CollatzResearch.WordTrace tailWord_4032175 prefixEnd_4032175 2070443858042866830468871 := by
  unfold tailWord_4032175
  simp only [CollatzResearch.WordTrace]
  refine ⟨147065504167126090509625979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98043669444750727006417319 147065504167126090509625979)
  ·
    refine ⟨220598256250689135764438969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147065504167126090509625979 220598256250689135764438969)
    ·
      refine ⟨165448692188016851823329227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 220598256250689135764438969 165448692188016851823329227)
      ·
        refine ⟨248173038282025277734993841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 165448692188016851823329227 248173038282025277734993841)
        ·
          refine ⟨186129778711518958301245381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 248173038282025277734993841 186129778711518958301245381)
          ·
            refine ⟨34899333508409804681483509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 186129778711518958301245381 34899333508409804681483509)
            ·
              refine ⟨3271812516413419188889079, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 34899333508409804681483509 3271812516413419188889079)
              ·
                refine ⟨4907718774620128783333619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3271812516413419188889079 4907718774620128783333619)
                ·
                  refine ⟨7361578161930193175000429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4907718774620128783333619 7361578161930193175000429)
                  ·
                    refine ⟨2760591810723822440625161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7361578161930193175000429 2760591810723822440625161)
                    ·
                      refine ⟨2070443858042866830468871, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2760591810723822440625161 2070443858042866830468871)
                      ·
                        rfl

theorem cell23_4032175_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 5, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 5, 1, 1, 3, 2].length) (baseStart_4032175 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4032175 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4032175 prefixEnd_4032175 := by exact prefixLift 4032175
  have htrace : WordTrace (prefixWord ++ tailWord_4032175) baseStart_4032175 baseEnd_4032175 := by
    simpa [prefixWord, tailWord_4032175, baseEnd_4032175] using wordTrace_append hprefix tailTrace_4032175
  have hstable : (prefixWord ++ tailWord_4032175).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4032175).length < 2 ^ (prefixWord ++ tailWord_4032175).sum := by decide
  have hdescent : baseEnd_4032175 < baseStart_4032175 := by decide
  rcases family_descends (prefixWord ++ tailWord_4032175) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4032182 : List Nat := [5, 1, 3, 1, 1, 1, 1, 4, 2, 1, 3]
def baseStart_4032182 : Nat := 118140960795 + 4032182 * 2 ^ 59
def prefixEnd_4032182 : Nat := 4983230072969 + 3 ^ 40 * 4032182 * 2
def baseEnd_4032182 : Nat := 2070447452407448303081339

theorem tailTrace_4032182 : CollatzResearch.WordTrace tailWord_4032182 prefixEnd_4032182 2070447452407448303081339 := by
  unfold tailWord_4032182
  simp only [CollatzResearch.WordTrace]
  refine ⟨9191609967381295669070675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 98043839652067153803420533 9191609967381295669070675)
  ·
    refine ⟨13787414951071943503606013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9191609967381295669070675 13787414951071943503606013)
    ·
      refine ⟨5170280606651978813852255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13787414951071943503606013 5170280606651978813852255)
      ·
        refine ⟨7755420909977968220778383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5170280606651978813852255 7755420909977968220778383)
        ·
          refine ⟨11633131364966952331167575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7755420909977968220778383 11633131364966952331167575)
          ·
            refine ⟨17449697047450428496751363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11633131364966952331167575 17449697047450428496751363)
            ·
              refine ⟨26174545571175642745127045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17449697047450428496751363 26174545571175642745127045)
              ·
                refine ⟨4907727294595433014711321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 26174545571175642745127045 4907727294595433014711321)
                ·
                  refine ⟨3680795470946574761033491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4907727294595433014711321 3680795470946574761033491)
                  ·
                    refine ⟨5521193206419862141550237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3680795470946574761033491 5521193206419862141550237)
                    ·
                      refine ⟨2070447452407448303081339, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5521193206419862141550237 2070447452407448303081339)
                      ·
                        rfl

theorem cell23_4032182_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 1, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 1, 1, 4, 2, 1, 3].length) (baseStart_4032182 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4032182 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4032182 prefixEnd_4032182 := by exact prefixLift 4032182
  have htrace : WordTrace (prefixWord ++ tailWord_4032182) baseStart_4032182 baseEnd_4032182 := by
    simpa [prefixWord, tailWord_4032182, baseEnd_4032182] using wordTrace_append hprefix tailTrace_4032182
  have hstable : (prefixWord ++ tailWord_4032182).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4032182).length < 2 ^ (prefixWord ++ tailWord_4032182).sum := by decide
  have hdescent : baseEnd_4032182 < baseStart_4032182 := by decide
  rcases family_descends (prefixWord ++ tailWord_4032182) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4032184 : List Nat := [2, 1, 2, 1, 2, 1, 1, 2, 3, 4, 4]
def baseStart_4032184 : Nat := 118140960795 + 4032184 * 2 ^ 59
def prefixEnd_4032184 : Nat := 4983230072969 + 3 ^ 40 * 4032184 * 2
def baseEnd_4032184 : Nat := 2070448479368757295256329

theorem tailTrace_4032184 : CollatzResearch.WordTrace tailWord_4032184 prefixEnd_4032184 2070448479368757295256329 := by
  unfold tailWord_4032184
  simp only [CollatzResearch.WordTrace]
  refine ⟨73532916212046742523351803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98043888282728990031135737 73532916212046742523351803)
  ·
    refine ⟨110299374318070113785027705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73532916212046742523351803 110299374318070113785027705)
    ·
      refine ⟨82724530738552585338770779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 110299374318070113785027705 82724530738552585338770779)
      ·
        refine ⟨124086796107828878008156169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82724530738552585338770779 124086796107828878008156169)
        ·
          refine ⟨93065097080871658506117127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 124086796107828878008156169 93065097080871658506117127)
          ·
            refine ⟨139597645621307487759175691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 93065097080871658506117127 139597645621307487759175691)
            ·
              refine ⟨209396468431961231638763537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 139597645621307487759175691 209396468431961231638763537)
              ·
                refine ⟨157047351323970923729072653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 209396468431961231638763537 157047351323970923729072653)
                ·
                  refine ⟨58892756746489096398402245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 157047351323970923729072653 58892756746489096398402245)
                  ·
                    refine ⟨11042391889966705574700421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 58892756746489096398402245 11042391889966705574700421)
                    ·
                      refine ⟨2070448479368757295256329, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11042391889966705574700421 2070448479368757295256329)
                      ·
                        rfl

theorem cell23_4032184_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 1, 2, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 1, 2, 3, 4, 4].length) (baseStart_4032184 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4032184 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4032184 prefixEnd_4032184 := by exact prefixLift 4032184
  have htrace : WordTrace (prefixWord ++ tailWord_4032184) baseStart_4032184 baseEnd_4032184 := by
    simpa [prefixWord, tailWord_4032184, baseEnd_4032184] using wordTrace_append hprefix tailTrace_4032184
  have hstable : (prefixWord ++ tailWord_4032184).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4032184).length < 2 ^ (prefixWord ++ tailWord_4032184).sum := by decide
  have hdescent : baseEnd_4032184 < baseStart_4032184 := by decide
  rcases family_descends (prefixWord ++ tailWord_4032184) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4032228 : List Nat := [2, 3, 1, 1, 1, 3, 4, 3, 5]
def baseStart_4032228 : Nat := 118140960795 + 4032228 * 2 ^ 59
def prefixEnd_4032228 : Nat := 4983230072969 + 3 ^ 40 * 4032228 * 2
def baseEnd_4032228 : Nat := 230052341390839458122903

theorem tailTrace_4032228 : CollatzResearch.WordTrace tailWord_4032228 prefixEnd_4032228 230052341390839458122903 := by
  unfold tailWord_4032228
  simp only [CollatzResearch.WordTrace]
  refine ⟨73533718617967040280652669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98044958157289387040870225 73533718617967040280652669)
  ·
    refine ⟨27575144481737640105244751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 73533718617967040280652669 27575144481737640105244751)
    ·
      refine ⟨41362716722606460157867127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27575144481737640105244751 41362716722606460157867127)
      ·
        refine ⟨62044075083909690236800691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41362716722606460157867127 62044075083909690236800691)
        ·
          refine ⟨93066112625864535355201037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62044075083909690236800691 93066112625864535355201037)
          ·
            refine ⟨34899792234699200758200389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 93066112625864535355201037 34899792234699200758200389)
            ·
              refine ⟨6543711044006100142162573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 34899792234699200758200389 6543711044006100142162573)
              ·
                refine ⟨2453891641502287553310965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6543711044006100142162573 2453891641502287553310965)
                ·
                  refine ⟨230052341390839458122903, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2453891641502287553310965 230052341390839458122903)
                  ·
                    rfl

theorem cell23_4032228_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 4, 3, 5].length) (baseStart_4032228 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4032228 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4032228 prefixEnd_4032228 := by exact prefixLift 4032228
  have htrace : WordTrace (prefixWord ++ tailWord_4032228) baseStart_4032228 baseEnd_4032228 := by
    simpa [prefixWord, tailWord_4032228, baseEnd_4032228] using wordTrace_append hprefix tailTrace_4032228
  have hstable : (prefixWord ++ tailWord_4032228).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4032228).length < 2 ^ (prefixWord ++ tailWord_4032228).sum := by decide
  have hdescent : baseEnd_4032228 < baseStart_4032228 := by decide
  rcases family_descends (prefixWord ++ tailWord_4032228) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4032271 : List Nat := [1, 1, 2, 1, 1, 1, 4, 3, 5, 4]
def baseStart_4032271 : Nat := 118140960795 + 4032271 * 2 ^ 59
def prefixEnd_4032271 : Nat := 4983230072969 + 3 ^ 40 * 4032271 * 2
def baseEnd_4032271 : Nat := 690164384061899484956143

theorem tailTrace_4032271 : CollatzResearch.WordTrace tailWord_4032271 prefixEnd_4032271 690164384061899484956143 := by
  unfold tailWord_4032271
  simp only [CollatzResearch.WordTrace]
  refine ⟨147069005574778298905120667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98046003716518865936747111 147069005574778298905120667)
  ·
    refine ⟨220603508362167448357681001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147069005574778298905120667 220603508362167448357681001)
    ·
      refine ⟨165452631271625586268260751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 220603508362167448357681001 165452631271625586268260751)
      ·
        refine ⟨248178946907438379402391127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 165452631271625586268260751 248178946907438379402391127)
        ·
          refine ⟨372268420361157569103586691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 248178946907438379402391127 372268420361157569103586691)
          ·
            refine ⟨558402630541736353655380037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 372268420361157569103586691 558402630541736353655380037)
            ·
              refine ⟨104700493226575566310383757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 558402630541736353655380037 104700493226575566310383757)
              ·
                refine ⟨39262684959965837366393909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 104700493226575566310383757 39262684959965837366393909)
                ·
                  refine ⟨3680876714996797253099429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 39262684959965837366393909 3680876714996797253099429)
                  ·
                    refine ⟨690164384061899484956143, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3680876714996797253099429 690164384061899484956143)
                    ·
                      rfl

theorem cell23_4032271_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 4, 3, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 4, 3, 5, 4].length) (baseStart_4032271 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4032271 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4032271 prefixEnd_4032271 := by exact prefixLift 4032271
  have htrace : WordTrace (prefixWord ++ tailWord_4032271) baseStart_4032271 baseEnd_4032271 := by
    simpa [prefixWord, tailWord_4032271, baseEnd_4032271] using wordTrace_append hprefix tailTrace_4032271
  have hstable : (prefixWord ++ tailWord_4032271).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4032271).length < 2 ^ (prefixWord ++ tailWord_4032271).sum := by decide
  have hdescent : baseEnd_4032271 < baseStart_4032271 := by decide
  rcases family_descends (prefixWord ++ tailWord_4032271) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4032305 : List Nat := [1, 2, 2, 3, 2, 4, 1, 1, 3, 4]
def baseStart_4032305 : Nat := 118140960795 + 4032305 * 2 ^ 59
def prefixEnd_4032305 : Nat := 4983230072969 + 3 ^ 40 * 4032305 * 2
def baseEnd_4032305 : Nat := 690170203509317107281091

theorem tailTrace_4032305 : CollatzResearch.WordTrace tailWord_4032305 prefixEnd_4032305 690170203509317107281091 := by
  unfold tailWord_4032305
  simp only [CollatzResearch.WordTrace]
  refine ⟨147070245656655122711858369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98046830437770081807905579 147070245656655122711858369)
  ·
    refine ⟨110302684242491342033893777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 147070245656655122711858369 110302684242491342033893777)
    ·
      refine ⟨82727013181868506525420333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 110302684242491342033893777 82727013181868506525420333)
      ·
        refine ⟨31022629943200689947032625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 82727013181868506525420333 31022629943200689947032625)
        ·
          refine ⟨23266972457400517460274469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31022629943200689947032625 23266972457400517460274469)
          ·
            refine ⟨4362557335762597023801463, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 23266972457400517460274469 4362557335762597023801463)
            ·
              refine ⟨6543836003643895535702195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4362557335762597023801463 6543836003643895535702195)
              ·
                refine ⟨9815754005465843303553293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6543836003643895535702195 9815754005465843303553293)
                ·
                  refine ⟨3680907752049691238832485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9815754005465843303553293 3680907752049691238832485)
                  ·
                    refine ⟨690170203509317107281091, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3680907752049691238832485 690170203509317107281091)
                    ·
                      rfl

theorem cell23_4032305_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 4, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 4, 1, 1, 3, 4].length) (baseStart_4032305 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4032305 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4032305 prefixEnd_4032305 := by exact prefixLift 4032305
  have htrace : WordTrace (prefixWord ++ tailWord_4032305) baseStart_4032305 baseEnd_4032305 := by
    simpa [prefixWord, tailWord_4032305, baseEnd_4032305] using wordTrace_append hprefix tailTrace_4032305
  have hstable : (prefixWord ++ tailWord_4032305).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4032305).length < 2 ^ (prefixWord ++ tailWord_4032305).sum := by decide
  have hdescent : baseEnd_4032305 < baseStart_4032305 := by decide
  rcases family_descends (prefixWord ++ tailWord_4032305) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4032311 : List Nat := [1, 1, 3, 1, 2, 1, 2, 2, 2, 5, 3]
def baseStart_4032311 : Nat := 118140960795 + 4032311 * 2 ^ 59
def prefixEnd_4032311 : Nat := 4983230072969 + 3 ^ 40 * 4032311 * 2
def baseEnd_4032311 : Nat := 2070513691411878298368245

theorem tailTrace_4032311 : CollatzResearch.WordTrace tailWord_4032311 prefixEnd_4032311 2070513691411878298368245 := by
  unfold tailWord_4032311
  simp only [CollatzResearch.WordTrace]
  refine ⟨147070464494633385736576787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98046976329755590491051191 147070464494633385736576787)
  ·
    refine ⟨220605696741950078604865181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147070464494633385736576787 220605696741950078604865181)
    ·
      refine ⟨82727136278231279476824443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 220605696741950078604865181 82727136278231279476824443)
      ·
        refine ⟨124090704417346919215236665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82727136278231279476824443 124090704417346919215236665)
        ·
          refine ⟨93068028313010189411427499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 124090704417346919215236665 93068028313010189411427499)
          ·
            refine ⟨139602042469515284117141249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 93068028313010189411427499 139602042469515284117141249)
            ·
              refine ⟨104701531852136463087855937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 139602042469515284117141249 104701531852136463087855937)
              ·
                refine ⟨78526148889102347315891953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 104701531852136463087855937 78526148889102347315891953)
                ·
                  refine ⟨58894611666826760486918965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 78526148889102347315891953 58894611666826760486918965)
                  ·
                    refine ⟨5521369843765008795648653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 58894611666826760486918965 5521369843765008795648653)
                    ·
                      refine ⟨2070513691411878298368245, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5521369843765008795648653 2070513691411878298368245)
                      ·
                        rfl

theorem cell23_4032311_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 2, 2, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 2, 2, 2, 5, 3].length) (baseStart_4032311 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4032311 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4032311 prefixEnd_4032311 := by exact prefixLift 4032311
  have htrace : WordTrace (prefixWord ++ tailWord_4032311) baseStart_4032311 baseEnd_4032311 := by
    simpa [prefixWord, tailWord_4032311, baseEnd_4032311] using wordTrace_append hprefix tailTrace_4032311
  have hstable : (prefixWord ++ tailWord_4032311).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4032311).length < 2 ^ (prefixWord ++ tailWord_4032311).sum := by decide
  have hdescent : baseEnd_4032311 < baseStart_4032311 := by decide
  rcases family_descends (prefixWord ++ tailWord_4032311) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4032356 : List Nat := [2, 3, 1, 1, 6, 1, 2, 2, 1, 4]
def baseStart_4032356 : Nat := 118140960795 + 4032356 * 2 ^ 59
def prefixEnd_4032356 : Nat := 4983230072969 + 3 ^ 40 * 4032356 * 2
def baseEnd_4032356 : Nat := 690178932680443540768513

theorem tailTrace_4032356 : CollatzResearch.WordTrace tailWord_4032356 prefixEnd_4032356 690178932680443540768513 := by
  unfold tailWord_4032356
  simp only [CollatzResearch.WordTrace]
  refine ⟨73536052889735179210982461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98048070519646905614643281 73536052889735179210982461)
  ·
    refine ⟨27576019833650692204118423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 73536052889735179210982461 27576019833650692204118423)
    ·
      refine ⟨41364029750476038306177635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27576019833650692204118423 41364029750476038306177635)
      ·
        refine ⟨62046044625714057459266453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41364029750476038306177635 62046044625714057459266453)
        ·
          refine ⟨2908408341830346443403115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 62046044625714057459266453 2908408341830346443403115)
          ·
            refine ⟨4362612512745519665104673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2908408341830346443403115 4362612512745519665104673)
            ·
              refine ⟨3271959384559139748828505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4362612512745519665104673 3271959384559139748828505)
              ·
                refine ⟨2453969538419354811621379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3271959384559139748828505 2453969538419354811621379)
                ·
                  refine ⟨3680954307629032217432069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2453969538419354811621379 3680954307629032217432069)
                  ·
                    refine ⟨690178932680443540768513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3680954307629032217432069 690178932680443540768513)
                    ·
                      rfl

theorem cell23_4032356_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 6, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 6, 1, 2, 2, 1, 4].length) (baseStart_4032356 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4032356 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4032356 prefixEnd_4032356 := by exact prefixLift 4032356
  have htrace : WordTrace (prefixWord ++ tailWord_4032356) baseStart_4032356 baseEnd_4032356 := by
    simpa [prefixWord, tailWord_4032356, baseEnd_4032356] using wordTrace_append hprefix tailTrace_4032356
  have hstable : (prefixWord ++ tailWord_4032356).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4032356).length < 2 ^ (prefixWord ++ tailWord_4032356).sum := by decide
  have hdescent : baseEnd_4032356 < baseStart_4032356 := by decide
  rcases family_descends (prefixWord ++ tailWord_4032356) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4032368 : List Nat := [2, 1, 1, 1, 4, 1, 1, 2, 2, 6, 2]
def baseStart_4032368 : Nat := 118140960795 + 4032368 * 2 ^ 59
def prefixEnd_4032368 : Nat := 4983230072969 + 3 ^ 40 * 4032368 * 2
def baseEnd_4032368 : Nat := 2070542959809184575355483

theorem tailTrace_4032368 : CollatzResearch.WordTrace tailWord_4032368 prefixEnd_4032368 2070542959809184575355483 := by
  unfold tailWord_4032368
  simp only [CollatzResearch.WordTrace]
  refine ⟨73536271727713442235700879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98048362303617922980934505 73536271727713442235700879)
  ·
    refine ⟨110304407591570163353551319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73536271727713442235700879 110304407591570163353551319)
    ·
      refine ⟨165456611387355245030326979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110304407591570163353551319 165456611387355245030326979)
      ·
        refine ⟨248184917081032867545490469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 165456611387355245030326979 248184917081032867545490469)
        ·
          refine ⟨46534671952693662664779463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 248184917081032867545490469 46534671952693662664779463)
          ·
            refine ⟨69802007929040493997169195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46534671952693662664779463 69802007929040493997169195)
            ·
              refine ⟨104703011893560740995753793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 69802007929040493997169195 104703011893560740995753793)
              ·
                refine ⟨78527258920170555746815345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 104703011893560740995753793 78527258920170555746815345)
                ·
                  refine ⟨58895444190127916810111509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 78527258920170555746815345 58895444190127916810111509)
                  ·
                    refine ⟨2760723946412246100473977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 58895444190127916810111509 2760723946412246100473977)
                    ·
                      refine ⟨2070542959809184575355483, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2760723946412246100473977 2070542959809184575355483)
                      ·
                        rfl

theorem cell23_4032368_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 1, 2, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 1, 2, 2, 6, 2].length) (baseStart_4032368 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4032368 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4032368 prefixEnd_4032368 := by exact prefixLift 4032368
  have htrace : WordTrace (prefixWord ++ tailWord_4032368) baseStart_4032368 baseEnd_4032368 := by
    simpa [prefixWord, tailWord_4032368, baseEnd_4032368] using wordTrace_append hprefix tailTrace_4032368
  have hstable : (prefixWord ++ tailWord_4032368).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4032368).length < 2 ^ (prefixWord ++ tailWord_4032368).sum := by decide
  have hdescent : baseEnd_4032368 < baseStart_4032368 := by decide
  rcases family_descends (prefixWord ++ tailWord_4032368) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4032371 : List Nat := [1, 1, 1, 2, 2, 1, 3, 3, 3, 1, 5]
def baseStart_4032371 : Nat := 118140960795 + 4032371 * 2 ^ 59
def prefixEnd_4032371 : Nat := 4983230072969 + 3 ^ 40 * 4032371 * 2
def baseEnd_4032371 : Nat := 2070544500251148063617969

theorem tailTrace_4032371 : CollatzResearch.WordTrace tailWord_4032371 prefixEnd_4032371 2070544500251148063617969 := by
  unfold tailWord_4032371
  simp only [CollatzResearch.WordTrace]
  refine ⟨147072652874416015983760967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98048435249610677322507311 147072652874416015983760967)
  ·
    refine ⟨220608979311624023975641451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147072652874416015983760967 220608979311624023975641451)
    ·
      refine ⟨330913468967436035963462177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 220608979311624023975641451 330913468967436035963462177)
      ·
        refine ⟨248185101725577026972596633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 330913468967436035963462177 248185101725577026972596633)
        ·
          refine ⟨186138826294182770229447475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 248185101725577026972596633 186138826294182770229447475)
          ·
            refine ⟨279208239441274155344171213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 186138826294182770229447475 279208239441274155344171213)
            ·
              refine ⟨104703089790477808254064205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 279208239441274155344171213 104703089790477808254064205)
              ·
                refine ⟨39263658671429178095274077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 104703089790477808254064205 39263658671429178095274077)
                ·
                  refine ⟨14723872001785941785727779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 39263658671429178095274077 14723872001785941785727779)
                  ·
                    refine ⟨22085808002678912678591669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14723872001785941785727779 22085808002678912678591669)
                    ·
                      refine ⟨2070544500251148063617969, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 22085808002678912678591669 2070544500251148063617969)
                      ·
                        rfl

theorem cell23_4032371_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 3, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 3, 3, 3, 1, 5].length) (baseStart_4032371 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4032371 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4032371 prefixEnd_4032371 := by exact prefixLift 4032371
  have htrace : WordTrace (prefixWord ++ tailWord_4032371) baseStart_4032371 baseEnd_4032371 := by
    simpa [prefixWord, tailWord_4032371, baseEnd_4032371] using wordTrace_append hprefix tailTrace_4032371
  have hstable : (prefixWord ++ tailWord_4032371).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4032371).length < 2 ^ (prefixWord ++ tailWord_4032371).sum := by decide
  have hdescent : baseEnd_4032371 < baseStart_4032371 := by decide
  rcases family_descends (prefixWord ++ tailWord_4032371) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4032402 : List Nat := [3, 2, 3, 2, 1, 2, 1, 3, 1, 1, 4]
def baseStart_4032402 : Nat := 118140960795 + 4032402 * 2 ^ 59
def prefixEnd_4032402 : Nat := 4983230072969 + 3 ^ 40 * 4032402 * 2
def baseEnd_4032402 : Nat := 2070560418151437442330327

theorem tailTrace_4032402 : CollatzResearch.WordTrace tailWord_4032402 prefixEnd_4032402 2070560418151437442330327 := by
  unfold tailWord_4032402
  simp only [CollatzResearch.WordTrace]
  refine ⟨36768445884325927069534865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 98049189024869138852092973 36768445884325927069534865)
  ·
    refine ⟨27576334413244445302151149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36768445884325927069534865 27576334413244445302151149)
    ·
      refine ⟨10341125404966666988306681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27576334413244445302151149 10341125404966666988306681)
      ·
        refine ⟨7755844053725000241230011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10341125404966666988306681 7755844053725000241230011)
        ·
          refine ⟨11633766080587500361845017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7755844053725000241230011 11633766080587500361845017)
          ·
            refine ⟨8725324560440625271383763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11633766080587500361845017 8725324560440625271383763)
            ·
              refine ⟨13087986840660937907075645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8725324560440625271383763 13087986840660937907075645)
              ·
                refine ⟨4907995065247851715153367, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13087986840660937907075645 4907995065247851715153367)
                ·
                  refine ⟨7361992597871777572730051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4907995065247851715153367 7361992597871777572730051)
                  ·
                    refine ⟨11042988896807666359095077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7361992597871777572730051 11042988896807666359095077)
                    ·
                      refine ⟨2070560418151437442330327, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11042988896807666359095077 2070560418151437442330327)
                      ·
                        rfl

theorem cell23_4032402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 2, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 2, 1, 3, 1, 1, 4].length) (baseStart_4032402 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4032402 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4032402 prefixEnd_4032402 := by exact prefixLift 4032402
  have htrace : WordTrace (prefixWord ++ tailWord_4032402) baseStart_4032402 baseEnd_4032402 := by
    simpa [prefixWord, tailWord_4032402, baseEnd_4032402] using wordTrace_append hprefix tailTrace_4032402
  have hstable : (prefixWord ++ tailWord_4032402).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4032402).length < 2 ^ (prefixWord ++ tailWord_4032402).sum := by decide
  have hdescent : baseEnd_4032402 < baseStart_4032402 := by decide
  rcases family_descends (prefixWord ++ tailWord_4032402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4032405 : List Nat := [1, 3, 2, 1, 1, 3, 3, 3, 1, 2, 3]
def baseStart_4032405 : Nat := 118140960795 + 4032405 * 2 ^ 59
def prefixEnd_4032405 : Nat := 4983230072969 + 3 ^ 40 * 4032405 * 2
def baseEnd_4032405 : Nat := 2070561958593400930592813

theorem tailTrace_4032405 : CollatzResearch.WordTrace tailWord_4032405 prefixEnd_4032405 2070561958593400930592813 := by
  unfold tailWord_4032405
  simp only [CollatzResearch.WordTrace]
  refine ⟨147073892956292839790498669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98049261970861893193665779 147073892956292839790498669)
  ·
    refine ⟨55152709858609814921437001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 147073892956292839790498669 55152709858609814921437001)
    ·
      refine ⟨41364532393957361191077751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55152709858609814921437001 41364532393957361191077751)
      ·
        refine ⟨62046798590936041786616627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41364532393957361191077751 62046798590936041786616627)
        ·
          refine ⟨93070197886404062679924941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62046798590936041786616627 93070197886404062679924941)
          ·
            refine ⟨34901324207401523504971853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 93070197886404062679924941 34901324207401523504971853)
            ·
              refine ⟨13087996577775571314364445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34901324207401523504971853 13087996577775571314364445)
              ·
                refine ⟨4907998716665839242886667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13087996577775571314364445 4907998716665839242886667)
                ·
                  refine ⟨7361998074998758864330001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4907998716665839242886667 7361998074998758864330001)
                  ·
                    refine ⟨5521498556249069148247501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7361998074998758864330001 5521498556249069148247501)
                    ·
                      refine ⟨2070561958593400930592813, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5521498556249069148247501 2070561958593400930592813)
                      ·
                        rfl

theorem cell23_4032405_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 3, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 3, 3, 1, 2, 3].length) (baseStart_4032405 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4032405 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4032405 prefixEnd_4032405 := by exact prefixLift 4032405
  have htrace : WordTrace (prefixWord ++ tailWord_4032405) baseStart_4032405 baseEnd_4032405 := by
    simpa [prefixWord, tailWord_4032405, baseEnd_4032405] using wordTrace_append hprefix tailTrace_4032405
  have hstable : (prefixWord ++ tailWord_4032405).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4032405).length < 2 ^ (prefixWord ++ tailWord_4032405).sum := by decide
  have hdescent : baseEnd_4032405 < baseStart_4032405 := by decide
  rcases family_descends (prefixWord ++ tailWord_4032405) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4032412 : List Nat := [2, 2, 3, 3, 1, 1, 3, 2, 2, 4]
def baseStart_4032412 : Nat := 118140960795 + 4032412 * 2 ^ 59
def prefixEnd_4032412 : Nat := 4983230072969 + 3 ^ 40 * 4032412 * 2
def baseEnd_4032412 : Nat := 690188517652660801068427

theorem tailTrace_4032412 : CollatzResearch.WordTrace tailWord_4032412 prefixEnd_4032412 690188517652660801068427 := by
  unfold tailWord_4032412
  simp only [CollatzResearch.WordTrace]
  refine ⟨73537074133633739993001745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98049432178178319990668993 73537074133633739993001745)
  ·
    refine ⟨55152805600225304994751309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73537074133633739993001745 55152805600225304994751309)
    ·
      refine ⟨20682302100084489373031741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 55152805600225304994751309 20682302100084489373031741)
      ·
        refine ⟨7755863287531683514886903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20682302100084489373031741 7755863287531683514886903)
        ·
          refine ⟨11633794931297525272330355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7755863287531683514886903 11633794931297525272330355)
          ·
            refine ⟨17450692396946287908495533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11633794931297525272330355 17450692396946287908495533)
            ·
              refine ⟨6544009648854857965685825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17450692396946287908495533 6544009648854857965685825)
              ·
                refine ⟨4908007236641143474264369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6544009648854857965685825 4908007236641143474264369)
                ·
                  refine ⟨3681005427480857605698277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4908007236641143474264369 3681005427480857605698277)
                  ·
                    refine ⟨690188517652660801068427, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3681005427480857605698277 690188517652660801068427)
                    ·
                      rfl

theorem cell23_4032412_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 1, 3, 2, 2, 4].length) (baseStart_4032412 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4032412 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4032412 prefixEnd_4032412 := by exact prefixLift 4032412
  have htrace : WordTrace (prefixWord ++ tailWord_4032412) baseStart_4032412 baseEnd_4032412 := by
    simpa [prefixWord, tailWord_4032412, baseEnd_4032412] using wordTrace_append hprefix tailTrace_4032412
  have hstable : (prefixWord ++ tailWord_4032412).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4032412).length < 2 ^ (prefixWord ++ tailWord_4032412).sum := by decide
  have hdescent : baseEnd_4032412 < baseStart_4032412 := by decide
  rcases family_descends (prefixWord ++ tailWord_4032412) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4032421 : List Nat := [1, 3, 1, 2, 1, 1, 1, 3, 1, 9]
def baseStart_4032421 : Nat := 118140960795 + 4032421 * 2 ^ 59
def prefixEnd_4032421 : Nat := 4983230072969 + 3 ^ 40 * 4032421 * 2
def baseEnd_4032421 : Nat := 690190058094624289330913

theorem tailTrace_4032421 : CollatzResearch.WordTrace tailWord_4032421 prefixEnd_4032421 690190058094624289330913 := by
  unfold tailWord_4032421
  simp only [CollatzResearch.WordTrace]
  refine ⟨147074476524234874523081117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98049651016156583015387411 147074476524234874523081117)
  ·
    refine ⟨55152928696588077946155419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 147074476524234874523081117 55152928696588077946155419)
    ·
      refine ⟨82729393044882116919233129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55152928696588077946155419 82729393044882116919233129)
      ·
        refine ⟨62047044783661587689424847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 82729393044882116919233129 62047044783661587689424847)
        ·
          refine ⟨93070567175492381534137271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62047044783661587689424847 93070567175492381534137271)
          ·
            refine ⟨139605850763238572301205907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 93070567175492381534137271 139605850763238572301205907)
            ·
              refine ⟨209408776144857858451808861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 139605850763238572301205907 209408776144857858451808861)
              ·
                refine ⟨78528291054321696919428323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 209408776144857858451808861 78528291054321696919428323)
                ·
                  refine ⟨117792436581482545379142485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 78528291054321696919428323 117792436581482545379142485)
                  ·
                    refine ⟨690190058094624289330913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 117792436581482545379142485 690190058094624289330913)
                    ·
                      rfl

theorem cell23_4032421_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 1, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 1, 3, 1, 9].length) (baseStart_4032421 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4032421 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4032421 prefixEnd_4032421 := by exact prefixLift 4032421
  have htrace : WordTrace (prefixWord ++ tailWord_4032421) baseStart_4032421 baseEnd_4032421 := by
    simpa [prefixWord, tailWord_4032421, baseEnd_4032421] using wordTrace_append hprefix tailTrace_4032421
  have hstable : (prefixWord ++ tailWord_4032421).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4032421).length < 2 ^ (prefixWord ++ tailWord_4032421).sum := by decide
  have hdescent : baseEnd_4032421 < baseStart_4032421 := by decide
  rcases family_descends (prefixWord ++ tailWord_4032421) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4032462 : List Nat := [4, 1, 1, 1, 2, 2, 1, 5, 1, 3, 2]
def baseStart_4032462 : Nat := 118140960795 + 4032462 * 2 ^ 59
def prefixEnd_4032462 : Nat := 4983230072969 + 3 ^ 40 * 4032462 * 2
def baseEnd_4032462 : Nat := 2070591226990707207580051

theorem tailTrace_4032462 : CollatzResearch.WordTrace tailWord_4032462 prefixEnd_4032462 2070591226990707207580051 := by
  unfold tailWord_4032462
  simp only [CollatzResearch.WordTrace]
  refine ⟨18384496489635792315665455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 98050647944724225683549093 18384496489635792315665455)
  ·
    refine ⟨27576744734453688473498183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18384496489635792315665455 27576744734453688473498183)
    ·
      refine ⟨41365117101680532710247275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27576744734453688473498183 41365117101680532710247275)
      ·
        refine ⟨62047675652520799065370913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41365117101680532710247275 62047675652520799065370913)
        ·
          refine ⟨46535756739390599299028185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62047675652520799065370913 46535756739390599299028185)
          ·
            refine ⟨34901817554542949474271139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46535756739390599299028185 34901817554542949474271139)
            ·
              refine ⟨52352726331814424211406709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34901817554542949474271139 52352726331814424211406709)
              ·
                refine ⟨4908068093607602269819379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 52352726331814424211406709 4908068093607602269819379)
                ·
                  refine ⟨7362102140411403404729069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4908068093607602269819379 7362102140411403404729069)
                  ·
                    refine ⟨2760788302654276276773401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7362102140411403404729069 2760788302654276276773401)
                    ·
                      refine ⟨2070591226990707207580051, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2760788302654276276773401 2070591226990707207580051)
                      ·
                        rfl

theorem cell23_4032462_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 1, 5, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 1, 5, 1, 3, 2].length) (baseStart_4032462 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4032462 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4032462 prefixEnd_4032462 := by exact prefixLift 4032462
  have htrace : WordTrace (prefixWord ++ tailWord_4032462) baseStart_4032462 baseEnd_4032462 := by
    simpa [prefixWord, tailWord_4032462, baseEnd_4032462] using wordTrace_append hprefix tailTrace_4032462
  have hstable : (prefixWord ++ tailWord_4032462).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4032462).length < 2 ^ (prefixWord ++ tailWord_4032462).sum := by decide
  have hdescent : baseEnd_4032462 < baseStart_4032462 := by decide
  rcases family_descends (prefixWord ++ tailWord_4032462) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4032470 : List Nat := [5, 2, 1, 1, 3, 1, 3, 2, 1, 2, 2]
def baseStart_4032470 : Nat := 118140960795 + 4032470 * 2 ^ 59
def prefixEnd_4032470 : Nat := 4983230072969 + 3 ^ 40 * 4032470 * 2
def baseEnd_4032470 : Nat := 2070595334835943176280015

theorem tailTrace_4032470 : CollatzResearch.WordTrace tailWord_4032470 prefixEnd_4032470 2070595334835943176280015 := by
  unfold tailWord_4032470
  simp only [CollatzResearch.WordTrace]
  refine ⟨9192266481316084743225929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 98050842467371570594409909 9192266481316084743225929)
  ·
    refine ⟨6894199860987063557419447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9192266481316084743225929 6894199860987063557419447)
    ·
      refine ⟨10341299791480595336129171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6894199860987063557419447 10341299791480595336129171)
      ·
        refine ⟨15511949687220893004193757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10341299791480595336129171 15511949687220893004193757)
        ·
          refine ⟨5816981132707834876572659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15511949687220893004193757 5816981132707834876572659)
          ·
            refine ⟨8725471699061752314858989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5816981132707834876572659 8725471699061752314858989)
            ·
              refine ⟨3272051887148157118072121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8725471699061752314858989 3272051887148157118072121)
              ·
                refine ⟨2454038915361117838554091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3272051887148157118072121 2454038915361117838554091)
                ·
                  refine ⟨3681058373041676757831137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2454038915361117838554091 3681058373041676757831137)
                  ·
                    refine ⟨2760793779781257568373353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3681058373041676757831137 2760793779781257568373353)
                    ·
                      refine ⟨2070595334835943176280015, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2760793779781257568373353 2070595334835943176280015)
                      ·
                        rfl

theorem cell23_4032470_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 3, 1, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 3, 1, 3, 2, 1, 2, 2].length) (baseStart_4032470 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4032470 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4032470 prefixEnd_4032470 := by exact prefixLift 4032470
  have htrace : WordTrace (prefixWord ++ tailWord_4032470) baseStart_4032470 baseEnd_4032470 := by
    simpa [prefixWord, tailWord_4032470, baseEnd_4032470] using wordTrace_append hprefix tailTrace_4032470
  have hstable : (prefixWord ++ tailWord_4032470).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4032470).length < 2 ^ (prefixWord ++ tailWord_4032470).sum := by decide
  have hdescent : baseEnd_4032470 < baseStart_4032470 := by decide
  rcases family_descends (prefixWord ++ tailWord_4032470) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4032488 : List Nat := [2, 1, 4, 1, 1, 1, 1, 3, 1, 4, 4]
def baseStart_4032488 : Nat := 118140960795 + 4032488 * 2 ^ 59
def prefixEnd_4032488 : Nat := 4983230072969 + 3 ^ 40 * 4032488 * 2
def baseEnd_4032488 : Nat := 2070604577487724105854931

theorem tailTrace_4032488 : CollatzResearch.WordTrace tailWord_4032488 prefixEnd_4032488 2070604577487724105854931 := by
  unfold tailWord_4032488
  simp only [CollatzResearch.WordTrace]
  refine ⟨73538460107496072482885059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98051280143328096643846745 73538460107496072482885059)
  ·
    refine ⟨110307690161244108724327589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73538460107496072482885059 110307690161244108724327589)
    ·
      refine ⟨20682691905233270385811423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 110307690161244108724327589 20682691905233270385811423)
      ·
        refine ⟨31024037857849905578717135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20682691905233270385811423 31024037857849905578717135)
        ·
          refine ⟨46536056786774858368075703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31024037857849905578717135 46536056786774858368075703)
          ·
            refine ⟨69804085180162287552113555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46536056786774858368075703 69804085180162287552113555)
            ·
              refine ⟨104706127770243431328170333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 69804085180162287552113555 104706127770243431328170333)
              ·
                refine ⟨39264797913841286748063875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 104706127770243431328170333 39264797913841286748063875)
                ·
                  refine ⟨58897196870761930122095813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39264797913841286748063875 58897196870761930122095813)
                  ·
                    refine ⟨11043224413267861897892965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 58897196870761930122095813 11043224413267861897892965)
                    ·
                      refine ⟨2070604577487724105854931, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11043224413267861897892965 2070604577487724105854931)
                      ·
                        rfl

theorem cell23_4032488_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 1, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 1, 3, 1, 4, 4].length) (baseStart_4032488 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4032488 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4032488 prefixEnd_4032488 := by exact prefixLift 4032488
  have htrace : WordTrace (prefixWord ++ tailWord_4032488) baseStart_4032488 baseEnd_4032488 := by
    simpa [prefixWord, tailWord_4032488, baseEnd_4032488] using wordTrace_append hprefix tailTrace_4032488
  have hstable : (prefixWord ++ tailWord_4032488).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4032488).length < 2 ^ (prefixWord ++ tailWord_4032488).sum := by decide
  have hdescent : baseEnd_4032488 < baseStart_4032488 := by decide
  rcases family_descends (prefixWord ++ tailWord_4032488) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4032562 : List Nat := [3, 2, 1, 1, 2, 5, 1, 1, 2, 5]
def baseStart_4032562 : Nat := 118140960795 + 4032562 * 2 ^ 59
def prefixEnd_4032562 : Nat := 4983230072969 + 3 ^ 40 * 4032562 * 2
def baseEnd_4032562 : Nat := 690214191685385605443197

theorem tailTrace_4032562 : CollatzResearch.WordTrace tailWord_4032562 prefixEnd_4032562 690214191685385605443197 := by
  unfold tailWord_4032562
  simp only [CollatzResearch.WordTrace]
  refine ⟨36769904804181013900990985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 98053079477816037069309293 36769904804181013900990985)
  ·
    refine ⟨27577428603135760425743239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36769904804181013900990985 27577428603135760425743239)
    ·
      refine ⟨41366142904703640638614859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27577428603135760425743239 41366142904703640638614859)
      ·
        refine ⟨62049214357055460957922289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41366142904703640638614859 62049214357055460957922289)
        ·
          refine ⟨46536910767791595718441717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62049214357055460957922289 46536910767791595718441717)
          ·
            refine ⟨4362835384480462098603911, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 46536910767791595718441717 4362835384480462098603911)
            ·
              refine ⟨6544253076720693147905867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4362835384480462098603911 6544253076720693147905867)
              ·
                refine ⟨9816379615081039721858801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6544253076720693147905867 9816379615081039721858801)
                ·
                  refine ⟨7362284711310779791394101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9816379615081039721858801 7362284711310779791394101)
                  ·
                    refine ⟨690214191685385605443197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7362284711310779791394101 690214191685385605443197)
                    ·
                      rfl

theorem cell23_4032562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 5, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 5, 1, 1, 2, 5].length) (baseStart_4032562 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4032562 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4032562 prefixEnd_4032562 := by exact prefixLift 4032562
  have htrace : WordTrace (prefixWord ++ tailWord_4032562) baseStart_4032562 baseEnd_4032562 := by
    simpa [prefixWord, tailWord_4032562, baseEnd_4032562] using wordTrace_append hprefix tailTrace_4032562
  have hstable : (prefixWord ++ tailWord_4032562).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4032562).length < 2 ^ (prefixWord ++ tailWord_4032562).sum := by decide
  have hdescent : baseEnd_4032562 < baseStart_4032562 := by decide
  rcases family_descends (prefixWord ++ tailWord_4032562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4032585 : List Nat := [1, 2, 1, 1, 2, 2, 4, 1, 4, 2, 3]
def baseStart_4032585 : Nat := 118140960795 + 4032585 * 2 ^ 59
def prefixEnd_4032585 : Nat := 4983230072969 + 3 ^ 40 * 4032585 * 2
def baseEnd_4032585 : Nat := 2070654385111210226341985

theorem tailTrace_4032585 : CollatzResearch.WordTrace tailWord_4032585 prefixEnd_4032585 2070654385111210226341985 := by
  unfold tailWord_4032585
  simp only [CollatzResearch.WordTrace]
  refine ⟨147080458095640730532051209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98053638730427153688034139 147080458095640730532051209)
  ·
    refine ⟨110310343571730547899038407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 147080458095640730532051209 110310343571730547899038407)
    ·
      refine ⟨165465515357595821848557611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110310343571730547899038407 165465515357595821848557611)
      ·
        refine ⟨248198273036393732772836417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 165465515357595821848557611 248198273036393732772836417)
        ·
          refine ⟨186148704777295299579627313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 248198273036393732772836417 186148704777295299579627313)
          ·
            refine ⟨139611528582971474684720485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 186148704777295299579627313 139611528582971474684720485)
            ·
              refine ⟨26177161609307151503385091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 139611528582971474684720485 26177161609307151503385091)
              ·
                refine ⟨39265742413960727255077637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26177161609307151503385091 39265742413960727255077637)
                ·
                  refine ⟨7362326702617636360327057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 39265742413960727255077637 7362326702617636360327057)
                  ·
                    refine ⟨5521745026963227270245293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7362326702617636360327057 5521745026963227270245293)
                    ·
                      refine ⟨2070654385111210226341985, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5521745026963227270245293 2070654385111210226341985)
                      ·
                        rfl

theorem cell23_4032585_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 4, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 4, 1, 4, 2, 3].length) (baseStart_4032585 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4032585 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4032585 prefixEnd_4032585 := by exact prefixLift 4032585
  have htrace : WordTrace (prefixWord ++ tailWord_4032585) baseStart_4032585 baseEnd_4032585 := by
    simpa [prefixWord, tailWord_4032585, baseEnd_4032585] using wordTrace_append hprefix tailTrace_4032585
  have hstable : (prefixWord ++ tailWord_4032585).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4032585).length < 2 ^ (prefixWord ++ tailWord_4032585).sum := by decide
  have hdescent : baseEnd_4032585 < baseStart_4032585 := by decide
  rcases family_descends (prefixWord ++ tailWord_4032585) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4032615 : List Nat := [1, 1, 5, 1, 1, 2, 1, 1, 2, 5, 3]
def baseStart_4032615 : Nat := 118140960795 + 4032615 * 2 ^ 59
def prefixEnd_4032615 : Nat := 4983230072969 + 3 ^ 40 * 4032615 * 2
def baseEnd_4032615 : Nat := 2070669789530845108966847

theorem tailTrace_4032615 : CollatzResearch.WordTrace tailWord_4032615 prefixEnd_4032615 2070669789530845108966847 := by
  unfold tailWord_4032615
  simp only [CollatzResearch.WordTrace]
  refine ⟨147081552285532045655643299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98054368190354697103762199 147081552285532045655643299)
  ·
    refine ⟨220622328428298068483464949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147081552285532045655643299 220622328428298068483464949)
    ·
      refine ⟨20683343290152943920324839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 220622328428298068483464949 20683343290152943920324839)
      ·
        refine ⟨31025014935229415880487259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20683343290152943920324839 31025014935229415880487259)
        ·
          refine ⟨46537522402844123820730889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31025014935229415880487259 46537522402844123820730889)
          ·
            refine ⟨34903141802133092865548167, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46537522402844123820730889 34903141802133092865548167)
            ·
              refine ⟨52354712703199639298322251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34903141802133092865548167 52354712703199639298322251)
              ·
                refine ⟨78532069054799458947483377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52354712703199639298322251 78532069054799458947483377)
                ·
                  refine ⟨58899051791099594210612533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 78532069054799458947483377 58899051791099594210612533)
                  ·
                    refine ⟨5521786105415586957244925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 58899051791099594210612533 5521786105415586957244925)
                    ·
                      refine ⟨2070669789530845108966847, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5521786105415586957244925 2070669789530845108966847)
                      ·
                        rfl

theorem cell23_4032615_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 1, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 1, 1, 2, 5, 3].length) (baseStart_4032615 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4032615 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4032615 prefixEnd_4032615 := by exact prefixLift 4032615
  have htrace : WordTrace (prefixWord ++ tailWord_4032615) baseStart_4032615 baseEnd_4032615 := by
    simpa [prefixWord, tailWord_4032615, baseEnd_4032615] using wordTrace_append hprefix tailTrace_4032615
  have hstable : (prefixWord ++ tailWord_4032615).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4032615).length < 2 ^ (prefixWord ++ tailWord_4032615).sum := by decide
  have hdescent : baseEnd_4032615 < baseStart_4032615 := by decide
  rcases family_descends (prefixWord ++ tailWord_4032615) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4032626 : List Nat := [3, 2, 1, 2, 2, 4, 1, 3, 1, 4]
def baseStart_4032626 : Nat := 118140960795 + 4032626 * 2 ^ 59
def prefixEnd_4032626 : Nat := 4983230072969 + 3 ^ 40 * 4032626 * 2
def baseEnd_4032626 : Nat := 690225145939348188643099

theorem tailTrace_4032626 : CollatzResearch.WordTrace tailWord_4032626 prefixEnd_4032626 690225145939348188643099 := by
  unfold tailWord_4032626
  simp only [CollatzResearch.WordTrace]
  refine ⟨36770488372123048633573433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 98054635658994796356195821 36770488372123048633573433)
  ·
    refine ⟨27577866279092286475180075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36770488372123048633573433 27577866279092286475180075)
    ·
      refine ⟨41366799418638429712770113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27577866279092286475180075 41366799418638429712770113)
      ·
        refine ⟨31025099563978822284577585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41366799418638429712770113 31025099563978822284577585)
        ·
          refine ⟨23268824672984116713433189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31025099563978822284577585 23268824672984116713433189)
          ·
            refine ⟨4362904626184521883768723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 23268824672984116713433189 4362904626184521883768723)
            ·
              refine ⟨6544356939276782825653085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4362904626184521883768723 6544356939276782825653085)
              ·
                refine ⟨2454133852228793559619907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6544356939276782825653085 2454133852228793559619907)
                ·
                  refine ⟨3681200778343190339429861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2454133852228793559619907 3681200778343190339429861)
                  ·
                    refine ⟨690225145939348188643099, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3681200778343190339429861 690225145939348188643099)
                    ·
                      rfl

theorem cell23_4032626_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 4, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 4, 1, 3, 1, 4].length) (baseStart_4032626 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4032626 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4032626 prefixEnd_4032626 := by exact prefixLift 4032626
  have htrace : WordTrace (prefixWord ++ tailWord_4032626) baseStart_4032626 baseEnd_4032626 := by
    simpa [prefixWord, tailWord_4032626, baseEnd_4032626] using wordTrace_append hprefix tailTrace_4032626
  have hstable : (prefixWord ++ tailWord_4032626).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4032626).length < 2 ^ (prefixWord ++ tailWord_4032626).sum := by decide
  have hdescent : baseEnd_4032626 < baseStart_4032626 := by decide
  rcases family_descends (prefixWord ++ tailWord_4032626) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4032669 : List Nat := [1, 4, 2, 1, 1, 5, 1, 2, 1, 5]
def baseStart_4032669 : Nat := 118140960795 + 4032669 * 2 ^ 59
def prefixEnd_4032669 : Nat := 4983230072969 + 3 ^ 40 * 4032669 * 2
def baseEnd_4032669 : Nat := 690232505828729299230533

theorem tailTrace_4032669 : CollatzResearch.WordTrace tailWord_4032669 prefixEnd_4032669 690232505828729299230533 := by
  unfold tailWord_4032669
  simp only [CollatzResearch.WordTrace]
  refine ⟨147083521827336412878109061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98055681218224275252072707 147083521827336412878109061)
  ·
    refine ⟨27578160342625577414645449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 147083521827336412878109061 27578160342625577414645449)
    ·
      refine ⟨20683620256969183060984087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27578160342625577414645449 20683620256969183060984087)
      ·
        refine ⟨31025430385453774591476131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20683620256969183060984087 31025430385453774591476131)
        ·
          refine ⟨46538145578180661887214197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31025430385453774591476131 46538145578180661887214197)
          ·
            refine ⟨4362951147954437051926331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 46538145578180661887214197 4362951147954437051926331)
            ·
              refine ⟨6544426721931655577889497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4362951147954437051926331 6544426721931655577889497)
              ·
                refine ⟨4908320041448741683417123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6544426721931655577889497 4908320041448741683417123)
                ·
                  refine ⟨7362480062173112525125685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4908320041448741683417123 7362480062173112525125685)
                  ·
                    refine ⟨690232505828729299230533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7362480062173112525125685 690232505828729299230533)
                    ·
                      rfl

theorem cell23_4032669_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 5, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 5, 1, 2, 1, 5].length) (baseStart_4032669 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4032669 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4032669 prefixEnd_4032669 := by exact prefixLift 4032669
  have htrace : WordTrace (prefixWord ++ tailWord_4032669) baseStart_4032669 baseEnd_4032669 := by
    simpa [prefixWord, tailWord_4032669, baseEnd_4032669] using wordTrace_append hprefix tailTrace_4032669
  have hstable : (prefixWord ++ tailWord_4032669).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4032669).length < 2 ^ (prefixWord ++ tailWord_4032669).sum := by decide
  have hdescent : baseEnd_4032669 < baseStart_4032669 := by decide
  rcases family_descends (prefixWord ++ tailWord_4032669) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4032672 : List Nat := [2, 1, 1, 4, 2, 3, 1, 1, 3, 1, 4]
def baseStart_4032672 : Nat := 118140960795 + 4032672 * 2 ^ 59
def prefixEnd_4032672 : Nat := 4983230072969 + 3 ^ 40 * 4032672 * 2
def baseEnd_4032672 : Nat := 2070699057928151385954085

theorem tailTrace_4032672 : CollatzResearch.WordTrace tailWord_4032672 prefixEnd_4032672 2070699057928151385954085 := by
  unfold tailWord_4032672
  simp only [CollatzResearch.WordTrace]
  refine ⟨73541815623162772195234135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98055754164217029593645513 73541815623162772195234135)
  ·
    refine ⟨110312723434744158292851203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73541815623162772195234135 110312723434744158292851203)
    ·
      refine ⟨165469085152116237439276805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110312723434744158292851203 165469085152116237439276805)
      ·
        refine ⟨31025453466021794519864401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 165469085152116237439276805 31025453466021794519864401)
        ·
          refine ⟨23269090099516345889898301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31025453466021794519864401 23269090099516345889898301)
          ·
            refine ⟨8725908787318629708711863, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23269090099516345889898301 8725908787318629708711863)
            ·
              refine ⟨13088863180977944563067795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8725908787318629708711863 13088863180977944563067795)
              ·
                refine ⟨19633294771466916844601693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13088863180977944563067795 19633294771466916844601693)
                ·
                  refine ⟨7362485539300093816725635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19633294771466916844601693 7362485539300093816725635)
                  ·
                    refine ⟨11043728308950140725088453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7362485539300093816725635 11043728308950140725088453)
                    ·
                      refine ⟨2070699057928151385954085, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11043728308950140725088453 2070699057928151385954085)
                      ·
                        rfl

theorem cell23_4032672_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 3, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 3, 1, 1, 3, 1, 4].length) (baseStart_4032672 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4032672 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4032672 prefixEnd_4032672 := by exact prefixLift 4032672
  have htrace : WordTrace (prefixWord ++ tailWord_4032672) baseStart_4032672 baseEnd_4032672 := by
    simpa [prefixWord, tailWord_4032672, baseEnd_4032672] using wordTrace_append hprefix tailTrace_4032672
  have hstable : (prefixWord ++ tailWord_4032672).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4032672).length < 2 ^ (prefixWord ++ tailWord_4032672).sum := by decide
  have hdescent : baseEnd_4032672 < baseStart_4032672 := by decide
  rcases family_descends (prefixWord ++ tailWord_4032672) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4032676 : List Nat := [2, 3, 1, 2, 4, 1, 2, 1, 2, 3, 2]
def baseStart_4032676 : Nat := 118140960795 + 4032676 * 2 ^ 59
def prefixEnd_4032676 : Nat := 4983230072969 + 3 ^ 40 * 4032676 * 2
def baseEnd_4032676 : Nat := 2070701111850769370304067

theorem tailTrace_4032676 : CollatzResearch.WordTrace tailWord_4032676 prefixEnd_4032676 2070701111850769370304067 := by
  unfold tailWord_4032676
  simp only [CollatzResearch.WordTrace]
  refine ⟨73541888569155526536806941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98055851425540702049075921 73541888569155526536806941)
  ·
    refine ⟨27578208213433322451302603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 73541888569155526536806941 27578208213433322451302603)
    ·
      refine ⟨41367312320149983676953905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27578208213433322451302603 41367312320149983676953905)
      ·
        refine ⟨31025484240112487757715429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41367312320149983676953905 31025484240112487757715429)
        ·
          refine ⟨5817278295021091454571643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 31025484240112487757715429 5817278295021091454571643)
          ·
            refine ⟨8725917442531637181857465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5817278295021091454571643 8725917442531637181857465)
            ·
              refine ⟨6544438081898727886393099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8725917442531637181857465 6544438081898727886393099)
              ·
                refine ⟨9816657122848091829589649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6544438081898727886393099 9816657122848091829589649)
                ·
                  refine ⟨7362492842136068872192237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9816657122848091829589649 7362492842136068872192237)
                  ·
                    refine ⟨2760934815801025827072089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7362492842136068872192237 2760934815801025827072089)
                    ·
                      refine ⟨2070701111850769370304067, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2760934815801025827072089 2070701111850769370304067)
                      ·
                        rfl

theorem cell23_4032676_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 4, 1, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 4, 1, 2, 1, 2, 3, 2].length) (baseStart_4032676 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4032676 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4032676 prefixEnd_4032676 := by exact prefixLift 4032676
  have htrace : WordTrace (prefixWord ++ tailWord_4032676) baseStart_4032676 baseEnd_4032676 := by
    simpa [prefixWord, tailWord_4032676, baseEnd_4032676] using wordTrace_append hprefix tailTrace_4032676
  have hstable : (prefixWord ++ tailWord_4032676).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4032676).length < 2 ^ (prefixWord ++ tailWord_4032676).sum := by decide
  have hdescent : baseEnd_4032676 < baseStart_4032676 := by decide
  rcases family_descends (prefixWord ++ tailWord_4032676) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4032700 : List Nat := [2, 2, 2, 3, 3, 2, 2, 2, 1, 1, 3]
def baseStart_4032700 : Nat := 118140960795 + 4032700 * 2 ^ 59
def prefixEnd_4032700 : Nat := 4983230072969 + 3 ^ 40 * 4032700 * 2
def baseEnd_4032700 : Nat := 2070713435386477276403957

theorem tailTrace_4032700 : CollatzResearch.WordTrace tailWord_4032700 prefixEnd_4032700 2070713435386477276403957 := by
  unfold tailWord_4032700
  simp only [CollatzResearch.WordTrace]
  refine ⟨73542326245112052586243777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98056434993482736781658369 73542326245112052586243777)
  ·
    refine ⟨55156744683834039439682833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73542326245112052586243777 55156744683834039439682833)
    ·
      refine ⟨41367558512875529579762125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55156744683834039439682833 41367558512875529579762125)
      ·
        refine ⟨15512834442328323592410797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 41367558512875529579762125 15512834442328323592410797)
        ·
          refine ⟨5817312915873121347154049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15512834442328323592410797 5817312915873121347154049)
          ·
            refine ⟨4362984686904841010365537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5817312915873121347154049 4362984686904841010365537)
            ·
              refine ⟨3272238515178630757774153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4362984686904841010365537 3272238515178630757774153)
              ·
                refine ⟨2454178886383973068330615, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3272238515178630757774153 2454178886383973068330615)
                ·
                  refine ⟨3681268329575959602495923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2454178886383973068330615 3681268329575959602495923)
                  ·
                    refine ⟨5521902494363939403743885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3681268329575959602495923 5521902494363939403743885)
                    ·
                      refine ⟨2070713435386477276403957, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5521902494363939403743885 2070713435386477276403957)
                      ·
                        rfl

theorem cell23_4032700_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 3, 2, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 3, 2, 2, 2, 1, 1, 3].length) (baseStart_4032700 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4032700 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4032700 prefixEnd_4032700 := by exact prefixLift 4032700
  have htrace : WordTrace (prefixWord ++ tailWord_4032700) baseStart_4032700 baseEnd_4032700 := by
    simpa [prefixWord, tailWord_4032700, baseEnd_4032700] using wordTrace_append hprefix tailTrace_4032700
  have hstable : (prefixWord ++ tailWord_4032700).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4032700).length < 2 ^ (prefixWord ++ tailWord_4032700).sum := by decide
  have hdescent : baseEnd_4032700 < baseStart_4032700 := by decide
  rcases family_descends (prefixWord ++ tailWord_4032700) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4032706 : List Nat := [3, 5, 1, 1, 1, 1, 1, 2, 3, 1, 4]
def baseStart_4032706 : Nat := 118140960795 + 4032706 * 2 ^ 59
def prefixEnd_4032706 : Nat := 4983230072969 + 3 ^ 40 * 4032706 * 2
def baseEnd_4032706 : Nat := 2070716516270404252928929

theorem tailTrace_4032706 : CollatzResearch.WordTrace tailWord_4032706 prefixEnd_4032706 2070716516270404252928929 := by
  unfold tailWord_4032706
  simp only [CollatzResearch.WordTrace]
  refine ⟨36771217832050592049301493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 98056580885468245464803981 36771217832050592049301493)
  ·
    refine ⟨3447301671754743004622015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 36771217832050592049301493 3447301671754743004622015)
    ·
      refine ⟨5170952507632114506933023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3447301671754743004622015 5170952507632114506933023)
      ·
        refine ⟨7756428761448171760399535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5170952507632114506933023 7756428761448171760399535)
        ·
          refine ⟨11634643142172257640599303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7756428761448171760399535 11634643142172257640599303)
          ·
            refine ⟨17451964713258386460898955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11634643142172257640599303 17451964713258386460898955)
            ·
              refine ⟨26177947069887579691348433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17451964713258386460898955 26177947069887579691348433)
              ·
                refine ⟨19633460302415684768511325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26177947069887579691348433 19633460302415684768511325)
                ·
                  refine ⟨7362547613405881788191747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19633460302415684768511325 7362547613405881788191747)
                  ·
                    refine ⟨11043821420108822682287621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7362547613405881788191747 11043821420108822682287621)
                    ·
                      refine ⟨2070716516270404252928929, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11043821420108822682287621 2070716516270404252928929)
                      ·
                        rfl

theorem cell23_4032706_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 1, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 1, 1, 2, 3, 1, 4].length) (baseStart_4032706 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4032706 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4032706 prefixEnd_4032706 := by exact prefixLift 4032706
  have htrace : WordTrace (prefixWord ++ tailWord_4032706) baseStart_4032706 baseEnd_4032706 := by
    simpa [prefixWord, tailWord_4032706, baseEnd_4032706] using wordTrace_append hprefix tailTrace_4032706
  have hstable : (prefixWord ++ tailWord_4032706).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4032706).length < 2 ^ (prefixWord ++ tailWord_4032706).sum := by decide
  have hdescent : baseEnd_4032706 < baseStart_4032706 := by decide
  rcases family_descends (prefixWord ++ tailWord_4032706) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
